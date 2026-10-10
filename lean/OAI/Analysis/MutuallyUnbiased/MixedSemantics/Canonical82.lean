import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10496 raw10496Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw10496 raw10496Labels = mixedMoment B raw10496step0 raw10496step0Labels := by
      have hz : ∀ j, raw10496 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10496step0 = (fun i j => raw10496 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10496step0 raw10496; decide +kernel
      have hl : raw10496step0Labels = raw10496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10496 raw10496Labels permutation346 hz
    mixedMoment B raw10496step0 raw10496step0Labels = mixedMoment B raw10496step1 raw10496step1Labels := by
      have ha : raw10496step1 = (fun i j => raw10496step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10496step1 raw10496step0; decide +kernel
      have hl : raw10496step1Labels = raw10496step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10496step0 raw10496step0Labels permutation32 permutation3
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw10497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10497step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10497 raw10497Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw10497 raw10497Labels = mixedMoment B raw10497step0 raw10497step0Labels := by
      have hz : ∀ j, raw10497 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10497step0 = (fun i j => raw10497 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10497step0 raw10497; decide +kernel
      have hl : raw10497step0Labels = raw10497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10497 raw10497Labels permutation265 hz
    mixedMoment B raw10497step0 raw10497step0Labels = mixedMoment B raw10497step1 raw10497step1Labels := by
      have ha : raw10497step1 = (fun i j => raw10497step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10497step1 raw10497step0; decide +kernel
      have hl : raw10497step1Labels = raw10497step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10497step0 raw10497step0Labels permutation32 permutation3
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw10498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10498step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10498step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw10498step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10498step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10498 raw10498Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw10498 raw10498Labels = mixedMoment B raw10498step0 raw10498step0Labels := by
      have hz : ∀ j, raw10498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10498step0 = (fun i j => raw10498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10498step0 raw10498; decide +kernel
      have hl : raw10498step0Labels = raw10498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10498 raw10498Labels permutation346 hz
    mixedMoment B raw10498step0 raw10498step0Labels = mixedMoment B raw10498step1 raw10498step1Labels := by
      have hz : ∀ j, raw10498step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10498step1 = (fun i j => raw10498step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10498step1 raw10498step0; decide +kernel
      have hl : raw10498step1Labels = raw10498step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10498step0 raw10498step0Labels permutation56 hz
    mixedMoment B raw10498step1 raw10498step1Labels = mixedMoment B raw10498step2 raw10498step2Labels := by
      have ha : raw10498step2 = (fun i j => raw10498step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10498step2 raw10498step1; decide +kernel
      have hl : raw10498step2Labels = raw10498step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10498step1 raw10498step1Labels permutation10 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw10499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10499step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10499step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw10499step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10499step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10499 raw10499Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw10499 raw10499Labels = mixedMoment B raw10499step0 raw10499step0Labels := by
      have hz : ∀ j, raw10499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10499step0 = (fun i j => raw10499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10499step0 raw10499; decide +kernel
      have hl : raw10499step0Labels = raw10499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10499 raw10499Labels permutation346 hz
    mixedMoment B raw10499step0 raw10499step0Labels = mixedMoment B raw10499step1 raw10499step1Labels := by
      have hz : ∀ j, raw10499step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10499step1 = (fun i j => raw10499step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10499step1 raw10499step0; decide +kernel
      have hl : raw10499step1Labels = raw10499step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10499step0 raw10499step0Labels permutation56 hz
    mixedMoment B raw10499step1 raw10499step1Labels = mixedMoment B raw10499step2 raw10499step2Labels := by
      have ha : raw10499step2 = (fun i j => raw10499step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10499step2 raw10499step1; decide +kernel
      have hl : raw10499step2Labels = raw10499step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10499step1 raw10499step1Labels permutation9 permutation3
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw10500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10500step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10500step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10500step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10500 raw10500Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw10500 raw10500Labels = mixedMoment B raw10500step0 raw10500step0Labels := by
      have hz : ∀ j, raw10500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10500step0 = (fun i j => raw10500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10500step0 raw10500; decide +kernel
      have hl : raw10500step0Labels = raw10500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10500 raw10500Labels permutation346 hz
    mixedMoment B raw10500step0 raw10500step0Labels = mixedMoment B raw10500step1 raw10500step1Labels := by
      have hz : ∀ j, raw10500step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10500step1 = (fun i j => raw10500step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10500step1 raw10500step0; decide +kernel
      have hl : raw10500step1Labels = raw10500step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10500step0 raw10500step0Labels permutation56 hz
    mixedMoment B raw10500step1 raw10500step1Labels = mixedMoment B raw10500step2 raw10500step2Labels := by
      have ha : raw10500step2 = (fun i j => raw10500step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10500step2 raw10500step1; decide +kernel
      have hl : raw10500step2Labels = raw10500step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10500step1 raw10500step1Labels permutation9 permutation3
    _ = mixedMoment B node1012 node1012Labels := by rfl

def raw10501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10501step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10501 raw10501Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw10501 raw10501Labels = mixedMoment B raw10501step0 raw10501step0Labels := by
      have hz : ∀ j, raw10501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10501step0 = (fun i j => raw10501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10501step0 raw10501; decide +kernel
      have hl : raw10501step0Labels = raw10501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10501 raw10501Labels permutation346 hz
    mixedMoment B raw10501step0 raw10501step0Labels = mixedMoment B raw10501step1 raw10501step1Labels := by
      have ha : raw10501step1 = (fun i j => raw10501step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10501step1 raw10501step0; decide +kernel
      have hl : raw10501step1Labels = raw10501step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10501step0 raw10501step0Labels permutation33 permutation3
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw10502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw10502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10502 raw10502Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw10502 raw10502Labels = mixedMoment B raw10502step0 raw10502step0Labels := by
      have hz : ∀ j, raw10502 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10502step0 = (fun i j => raw10502 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10502step0 raw10502; decide +kernel
      have hl : raw10502step0Labels = raw10502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10502 raw10502Labels permutation265 hz
    mixedMoment B raw10502step0 raw10502step0Labels = mixedMoment B raw10502step1 raw10502step1Labels := by
      have ha : raw10502step1 = (fun i j => raw10502step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10502step1 raw10502step0; decide +kernel
      have hl : raw10502step1Labels = raw10502step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10502step0 raw10502step0Labels permutation33 permutation3
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw10503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw10503step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10503step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw10503step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10503 raw10503Labels = mixedMoment B node2410 node2410Labels := by
  calc
    mixedMoment B raw10503 raw10503Labels = mixedMoment B raw10503step0 raw10503step0Labels := by
      have hz : ∀ j, raw10503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10503step0 = (fun i j => raw10503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10503step0 raw10503; decide +kernel
      have hl : raw10503step0Labels = raw10503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10503 raw10503Labels permutation346 hz
    mixedMoment B raw10503step0 raw10503step0Labels = mixedMoment B raw10503step1 raw10503step1Labels := by
      have hz : ∀ j, raw10503step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10503step1 = (fun i j => raw10503step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10503step1 raw10503step0; decide +kernel
      have hl : raw10503step1Labels = raw10503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10503step0 raw10503step0Labels permutation56 hz
    mixedMoment B raw10503step1 raw10503step1Labels = mixedMoment B raw10503step2 raw10503step2Labels := by
      have ha : raw10503step2 = (fun i j => raw10503step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10503step2 raw10503step1; decide +kernel
      have hl : raw10503step2Labels = raw10503step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10503step1 raw10503step1Labels permutation9 permutation3
    _ = mixedMoment B node2410 node2410Labels := by rfl

def raw10504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10504step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw10504step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10504step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10504 raw10504Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw10504 raw10504Labels = mixedMoment B raw10504step0 raw10504step0Labels := by
      have hz : ∀ j, raw10504 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10504step0 = (fun i j => raw10504 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10504step0 raw10504; decide +kernel
      have hl : raw10504step0Labels = raw10504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10504 raw10504Labels permutation346 hz
    mixedMoment B raw10504step0 raw10504step0Labels = mixedMoment B raw10504step1 raw10504step1Labels := by
      have hz : ∀ j, raw10504step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10504step1 = (fun i j => raw10504step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10504step1 raw10504step0; decide +kernel
      have hl : raw10504step1Labels = raw10504step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10504step0 raw10504step0Labels permutation56 hz
    mixedMoment B raw10504step1 raw10504step1Labels = mixedMoment B raw10504step2 raw10504step2Labels := by
      have ha : raw10504step2 = (fun i j => raw10504step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10504step2 raw10504step1; decide +kernel
      have hl : raw10504step2Labels = raw10504step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10504step1 raw10504step1Labels permutation9 permutation3
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw10505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10505step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10505 raw10505Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw10505 raw10505Labels = mixedMoment B raw10505step0 raw10505step0Labels := by
      have hz : ∀ j, raw10505 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10505step0 = (fun i j => raw10505 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10505step0 raw10505; decide +kernel
      have hl : raw10505step0Labels = raw10505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10505 raw10505Labels permutation346 hz
    mixedMoment B raw10505step0 raw10505step0Labels = mixedMoment B raw10505step1 raw10505step1Labels := by
      have hz : ∀ j, raw10505step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10505step1 = (fun i j => raw10505step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10505step1 raw10505step0; decide +kernel
      have hl : raw10505step1Labels = raw10505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10505step0 raw10505step0Labels permutation56 hz
    mixedMoment B raw10505step1 raw10505step1Labels = mixedMoment B raw10505step2 raw10505step2Labels := by
      have ha : raw10505step2 = (fun i j => raw10505step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10505step2 raw10505step1; decide +kernel
      have hl : raw10505step2Labels = raw10505step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10505step1 raw10505step1Labels permutation8 permutation3
    _ = mixedMoment B node1009 node1009Labels := by rfl

def raw10506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10506 raw10506Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw10506 raw10506Labels = mixedMoment B raw10506step0 raw10506step0Labels := by
      have hz : ∀ j, raw10506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10506step0 = (fun i j => raw10506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10506step0 raw10506; decide +kernel
      have hl : raw10506step0Labels = raw10506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10506 raw10506Labels permutation346 hz
    mixedMoment B raw10506step0 raw10506step0Labels = mixedMoment B raw10506step1 raw10506step1Labels := by
      have ha : raw10506step1 = (fun i j => raw10506step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10506step1 raw10506step0; decide +kernel
      have hl : raw10506step1Labels = raw10506step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10506step0 raw10506step0Labels permutation151 permutation3
    mixedMoment B raw10506step1 raw10506step1Labels = mixedMoment B raw10506step2 raw10506step2Labels := by
      have ha : raw10506step2 = -raw10506step1 := by apply Matrix.ext; change ∀ i j, raw10506step2 i j = -(raw10506step1 i j); unfold raw10506step2 raw10506step1; decide +kernel
      have hl : raw10506step2Labels = raw10506step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw10507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10507 raw10507Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw10507 raw10507Labels = mixedMoment B raw10507step0 raw10507step0Labels := by
      have hz : ∀ j, raw10507 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10507step0 = (fun i j => raw10507 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10507step0 raw10507; decide +kernel
      have hl : raw10507step0Labels = raw10507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10507 raw10507Labels permutation265 hz
    mixedMoment B raw10507step0 raw10507step0Labels = mixedMoment B raw10507step1 raw10507step1Labels := by
      have ha : raw10507step1 = (fun i j => raw10507step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10507step1 raw10507step0; decide +kernel
      have hl : raw10507step1Labels = raw10507step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10507step0 raw10507step0Labels permutation151 permutation3
    mixedMoment B raw10507step1 raw10507step1Labels = mixedMoment B raw10507step2 raw10507step2Labels := by
      have ha : raw10507step2 = -raw10507step1 := by apply Matrix.ext; change ∀ i j, raw10507step2 i j = -(raw10507step1 i j); unfold raw10507step2 raw10507step1; decide +kernel
      have hl : raw10507step2Labels = raw10507step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw10508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10508step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw10508step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10508step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw10508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10508 raw10508Labels = mixedMoment B node2407 node2407Labels := by
  calc
    mixedMoment B raw10508 raw10508Labels = mixedMoment B raw10508step0 raw10508step0Labels := by
      have hz : ∀ j, raw10508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10508step0 = (fun i j => raw10508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10508step0 raw10508; decide +kernel
      have hl : raw10508step0Labels = raw10508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10508 raw10508Labels permutation346 hz
    mixedMoment B raw10508step0 raw10508step0Labels = mixedMoment B raw10508step1 raw10508step1Labels := by
      have hz : ∀ j, raw10508step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10508step1 = (fun i j => raw10508step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10508step1 raw10508step0; decide +kernel
      have hl : raw10508step1Labels = raw10508step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10508step0 raw10508step0Labels permutation56 hz
    mixedMoment B raw10508step1 raw10508step1Labels = mixedMoment B raw10508step2 raw10508step2Labels := by
      have ha : raw10508step2 = (fun i j => raw10508step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10508step2 raw10508step1; decide +kernel
      have hl : raw10508step2Labels = raw10508step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10508step1 raw10508step1Labels permutation8 permutation3
    _ = mixedMoment B node2407 node2407Labels := by rfl

def raw10509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10509step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw10509step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10509step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10509 raw10509Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw10509 raw10509Labels = mixedMoment B raw10509step0 raw10509step0Labels := by
      have hz : ∀ j, raw10509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10509step0 = (fun i j => raw10509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10509step0 raw10509; decide +kernel
      have hl : raw10509step0Labels = raw10509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10509 raw10509Labels permutation346 hz
    mixedMoment B raw10509step0 raw10509step0Labels = mixedMoment B raw10509step1 raw10509step1Labels := by
      have hz : ∀ j, raw10509step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10509step1 = (fun i j => raw10509step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10509step1 raw10509step0; decide +kernel
      have hl : raw10509step1Labels = raw10509step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10509step0 raw10509step0Labels permutation56 hz
    mixedMoment B raw10509step1 raw10509step1Labels = mixedMoment B raw10509step2 raw10509step2Labels := by
      have ha : raw10509step2 = (fun i j => raw10509step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10509step2 raw10509step1; decide +kernel
      have hl : raw10509step2Labels = raw10509step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10509step1 raw10509step1Labels permutation8 permutation3
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw10510 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10510step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10510step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10510 raw10510Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw10510 raw10510Labels = mixedMoment B raw10510step0 raw10510step0Labels := by
      have hz : ∀ j, raw10510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10510step0 = (fun i j => raw10510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10510step0 raw10510; decide +kernel
      have hl : raw10510step0Labels = raw10510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10510 raw10510Labels permutation346 hz
    mixedMoment B raw10510step0 raw10510step0Labels = mixedMoment B raw10510step1 raw10510step1Labels := by
      have ha : raw10510step1 = (fun i j => raw10510step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10510step1 raw10510step0; decide +kernel
      have hl : raw10510step1Labels = raw10510step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10510step0 raw10510step0Labels permutation32 permutation7
    mixedMoment B raw10510step1 raw10510step1Labels = mixedMoment B raw10510step2 raw10510step2Labels := by
      have ha : raw10510step2 = raw10510step1 := by apply Matrix.ext; unfold raw10510step2 raw10510step1; decide +kernel
      have hl : raw10510step1Labels = labelEmbedding10 ∘ raw10510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10510step1 raw10510step1Labels raw10510step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw10511 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10511step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw10511step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10511 raw10511Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw10511 raw10511Labels = mixedMoment B raw10511step0 raw10511step0Labels := by
      have hz : ∀ j, raw10511 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10511step0 = (fun i j => raw10511 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10511step0 raw10511; decide +kernel
      have hl : raw10511step0Labels = raw10511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10511 raw10511Labels permutation265 hz
    mixedMoment B raw10511step0 raw10511step0Labels = mixedMoment B raw10511step1 raw10511step1Labels := by
      have ha : raw10511step1 = (fun i j => raw10511step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10511step1 raw10511step0; decide +kernel
      have hl : raw10511step1Labels = raw10511step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10511step0 raw10511step0Labels permutation32 permutation7
    mixedMoment B raw10511step1 raw10511step1Labels = mixedMoment B raw10511step2 raw10511step2Labels := by
      have ha : raw10511step2 = raw10511step1 := by apply Matrix.ext; unfold raw10511step2 raw10511step1; decide +kernel
      have hl : raw10511step1Labels = labelEmbedding10 ∘ raw10511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10511step1 raw10511step1Labels raw10511step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw10512 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10512step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10512step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10512step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10512step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw10512step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10512step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw10512step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10512 raw10512Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw10512 raw10512Labels = mixedMoment B raw10512step0 raw10512step0Labels := by
      have hz : ∀ j, raw10512 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10512step0 = (fun i j => raw10512 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10512step0 raw10512; decide +kernel
      have hl : raw10512step0Labels = raw10512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10512 raw10512Labels permutation346 hz
    mixedMoment B raw10512step0 raw10512step0Labels = mixedMoment B raw10512step1 raw10512step1Labels := by
      have hz : ∀ j, raw10512step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10512step1 = (fun i j => raw10512step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10512step1 raw10512step0; decide +kernel
      have hl : raw10512step1Labels = raw10512step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10512step0 raw10512step0Labels permutation56 hz
    mixedMoment B raw10512step1 raw10512step1Labels = mixedMoment B raw10512step2 raw10512step2Labels := by
      have ha : raw10512step2 = (fun i j => raw10512step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10512step2 raw10512step1; decide +kernel
      have hl : raw10512step2Labels = raw10512step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10512step1 raw10512step1Labels permutation8 permutation7
    mixedMoment B raw10512step2 raw10512step2Labels = mixedMoment B raw10512step3 raw10512step3Labels := by
      have ha : raw10512step3 = raw10512step2 := by apply Matrix.ext; unfold raw10512step3 raw10512step2; decide +kernel
      have hl : raw10512step2Labels = labelEmbedding10 ∘ raw10512step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10512step2 raw10512step2Labels raw10512step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw10513 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw10513step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10513step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10513step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10513step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10513 raw10513Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw10513 raw10513Labels = mixedMoment B raw10513step0 raw10513step0Labels := by
      have hz : ∀ j, raw10513 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10513step0 = (fun i j => raw10513 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10513step0 raw10513; decide +kernel
      have hl : raw10513step0Labels = raw10513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10513 raw10513Labels permutation265 hz
    mixedMoment B raw10513step0 raw10513step0Labels = mixedMoment B raw10513step1 raw10513step1Labels := by
      have ha : raw10513step1 = (fun i j => raw10513step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10513step1 raw10513step0; decide +kernel
      have hl : raw10513step1Labels = raw10513step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10513step0 raw10513step0Labels permutation39 permutation4
    mixedMoment B raw10513step1 raw10513step1Labels = mixedMoment B raw10513step2 raw10513step2Labels := by
      have ha : raw10513step2 = -raw10513step1 := by apply Matrix.ext; change ∀ i j, raw10513step2 i j = -(raw10513step1 i j); unfold raw10513step2 raw10513step1; decide +kernel
      have hl : raw10513step2Labels = raw10513step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10513step2 raw10513step2Labels = mixedMoment B raw10513step3 raw10513step3Labels := by
      have ha : raw10513step3 = raw10513step2 := by apply Matrix.ext; unfold raw10513step3 raw10513step2; decide +kernel
      have hl : raw10513step2Labels = labelEmbedding7 ∘ raw10513step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10513step2 raw10513step2Labels raw10513step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw10514 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10514step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10514 raw10514Labels = mixedMoment B node5242 node5242Labels := by
  calc
    mixedMoment B raw10514 raw10514Labels = mixedMoment B raw10514step0 raw10514step0Labels := by
      have ha : raw10514step0 = (fun i j => raw10514 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10514step0 raw10514; decide +kernel
      have hl : raw10514step0Labels = raw10514Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10514 raw10514Labels permutation158 permutation6
    mixedMoment B raw10514step0 raw10514step0Labels = mixedMoment B raw10514step1 raw10514step1Labels := by
      have ha : raw10514step1 = raw10514step0 := by apply Matrix.ext; unfold raw10514step1 raw10514step0; decide +kernel
      have hl : raw10514step0Labels = labelEmbedding9 ∘ raw10514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10514step0 raw10514step0Labels raw10514step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5242 node5242Labels := by rfl

def raw10515 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10515step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10515step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10515 raw10515Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw10515 raw10515Labels = mixedMoment B raw10515step0 raw10515step0Labels := by
      have hz : ∀ j, raw10515 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10515step0 = (fun i j => raw10515 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10515step0 raw10515; decide +kernel
      have hl : raw10515step0Labels = raw10515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10515 raw10515Labels permutation265 hz
    mixedMoment B raw10515step0 raw10515step0Labels = mixedMoment B raw10515step1 raw10515step1Labels := by
      have ha : raw10515step1 = (fun i j => raw10515step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10515step1 raw10515step0; decide +kernel
      have hl : raw10515step1Labels = raw10515step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10515step0 raw10515step0Labels permutation38 permutation6
    mixedMoment B raw10515step1 raw10515step1Labels = mixedMoment B raw10515step2 raw10515step2Labels := by
      have ha : raw10515step2 = raw10515step1 := by apply Matrix.ext; unfold raw10515step2 raw10515step1; decide +kernel
      have hl : raw10515step1Labels = labelEmbedding9 ∘ raw10515step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10515step1 raw10515step1Labels raw10515step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw10516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw10516step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10516step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw10516step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10516step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw10516step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10516 raw10516Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw10516 raw10516Labels = mixedMoment B raw10516step0 raw10516step0Labels := by
      have hz : ∀ j, raw10516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10516step0 = (fun i j => raw10516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10516step0 raw10516; decide +kernel
      have hl : raw10516step0Labels = raw10516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10516 raw10516Labels permutation346 hz
    mixedMoment B raw10516step0 raw10516step0Labels = mixedMoment B raw10516step1 raw10516step1Labels := by
      have hz : ∀ j, raw10516step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10516step1 = (fun i j => raw10516step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10516step1 raw10516step0; decide +kernel
      have hl : raw10516step1Labels = raw10516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10516step0 raw10516step0Labels permutation56 hz
    mixedMoment B raw10516step1 raw10516step1Labels = mixedMoment B raw10516step2 raw10516step2Labels := by
      have ha : raw10516step2 = (fun i j => raw10516step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10516step2 raw10516step1; decide +kernel
      have hl : raw10516step2Labels = raw10516step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10516step1 raw10516step1Labels permutation9 permutation4
    mixedMoment B raw10516step2 raw10516step2Labels = mixedMoment B raw10516step3 raw10516step3Labels := by
      have ha : raw10516step3 = -raw10516step2 := by apply Matrix.ext; change ∀ i j, raw10516step3 i j = -(raw10516step2 i j); unfold raw10516step3 raw10516step2; decide +kernel
      have hl : raw10516step3Labels = raw10516step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10516step3 raw10516step3Labels = mixedMoment B raw10516step4 raw10516step4Labels := by
      have ha : raw10516step4 = raw10516step3 := by apply Matrix.ext; unfold raw10516step4 raw10516step3; decide +kernel
      have hl : raw10516step3Labels = labelEmbedding7 ∘ raw10516step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10516step3 raw10516step3Labels raw10516step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw10517 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10517step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10517step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10517 raw10517Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw10517 raw10517Labels = mixedMoment B raw10517step0 raw10517step0Labels := by
      have hz : ∀ j, raw10517 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10517step0 = (fun i j => raw10517 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10517step0 raw10517; decide +kernel
      have hl : raw10517step0Labels = raw10517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10517 raw10517Labels permutation265 hz
    mixedMoment B raw10517step0 raw10517step0Labels = mixedMoment B raw10517step1 raw10517step1Labels := by
      have ha : raw10517step1 = (fun i j => raw10517step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10517step1 raw10517step0; decide +kernel
      have hl : raw10517step1Labels = raw10517step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10517step0 raw10517step0Labels permutation125 permutation5
    mixedMoment B raw10517step1 raw10517step1Labels = mixedMoment B raw10517step2 raw10517step2Labels := by
      have ha : raw10517step2 = raw10517step1 := by apply Matrix.ext; unfold raw10517step2 raw10517step1; decide +kernel
      have hl : raw10517step1Labels = labelEmbedding8 ∘ raw10517step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10517step1 raw10517step1Labels raw10517step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw10518 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10518step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10518step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10518step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10518step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10518 raw10518Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw10518 raw10518Labels = mixedMoment B raw10518step0 raw10518step0Labels := by
      have hz : ∀ j, raw10518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10518step0 = (fun i j => raw10518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10518step0 raw10518; decide +kernel
      have hl : raw10518step0Labels = raw10518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10518 raw10518Labels permutation346 hz
    mixedMoment B raw10518step0 raw10518step0Labels = mixedMoment B raw10518step1 raw10518step1Labels := by
      have hz : ∀ j, raw10518step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10518step1 = (fun i j => raw10518step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10518step1 raw10518step0; decide +kernel
      have hl : raw10518step1Labels = raw10518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10518step0 raw10518step0Labels permutation56 hz
    mixedMoment B raw10518step1 raw10518step1Labels = mixedMoment B raw10518step2 raw10518step2Labels := by
      have ha : raw10518step2 = (fun i j => raw10518step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10518step2 raw10518step1; decide +kernel
      have hl : raw10518step2Labels = raw10518step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10518step1 raw10518step1Labels permutation24 permutation5
    mixedMoment B raw10518step2 raw10518step2Labels = mixedMoment B raw10518step3 raw10518step3Labels := by
      have ha : raw10518step3 = raw10518step2 := by apply Matrix.ext; unfold raw10518step3 raw10518step2; decide +kernel
      have hl : raw10518step2Labels = labelEmbedding8 ∘ raw10518step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10518step2 raw10518step2Labels raw10518step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw10519 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw10519step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10519step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw10519step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10519step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw10519step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10519 raw10519Labels = mixedMoment B node4846 node4846Labels := by
  calc
    mixedMoment B raw10519 raw10519Labels = mixedMoment B raw10519step0 raw10519step0Labels := by
      have hz : ∀ j, raw10519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10519step0 = (fun i j => raw10519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10519step0 raw10519; decide +kernel
      have hl : raw10519step0Labels = raw10519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10519 raw10519Labels permutation346 hz
    mixedMoment B raw10519step0 raw10519step0Labels = mixedMoment B raw10519step1 raw10519step1Labels := by
      have hz : ∀ j, raw10519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10519step1 = (fun i j => raw10519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10519step1 raw10519step0; decide +kernel
      have hl : raw10519step1Labels = raw10519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10519step0 raw10519step0Labels permutation56 hz
    mixedMoment B raw10519step1 raw10519step1Labels = mixedMoment B raw10519step2 raw10519step2Labels := by
      have ha : raw10519step2 = (fun i j => raw10519step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10519step2 raw10519step1; decide +kernel
      have hl : raw10519step2Labels = raw10519step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10519step1 raw10519step1Labels permutation8 permutation4
    mixedMoment B raw10519step2 raw10519step2Labels = mixedMoment B raw10519step3 raw10519step3Labels := by
      have ha : raw10519step3 = -raw10519step2 := by apply Matrix.ext; change ∀ i j, raw10519step3 i j = -(raw10519step2 i j); unfold raw10519step3 raw10519step2; decide +kernel
      have hl : raw10519step3Labels = raw10519step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10519step3 raw10519step3Labels = mixedMoment B raw10519step4 raw10519step4Labels := by
      have ha : raw10519step4 = raw10519step3 := by apply Matrix.ext; unfold raw10519step4 raw10519step3; decide +kernel
      have hl : raw10519step3Labels = labelEmbedding7 ∘ raw10519step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10519step3 raw10519step3Labels raw10519step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4846 node4846Labels := by rfl

def raw10520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10520step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10520 raw10520Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw10520 raw10520Labels = mixedMoment B raw10520step0 raw10520step0Labels := by
      have hz : ∀ j, raw10520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10520step0 = (fun i j => raw10520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10520step0 raw10520; decide +kernel
      have hl : raw10520step0Labels = raw10520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10520 raw10520Labels permutation346 hz
    mixedMoment B raw10520step0 raw10520step0Labels = mixedMoment B raw10520step1 raw10520step1Labels := by
      have ha : raw10520step1 = (fun i j => raw10520step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10520step1 raw10520step0; decide +kernel
      have hl : raw10520step1Labels = raw10520step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10520step0 raw10520step0Labels permutation32 permutation6
    mixedMoment B raw10520step1 raw10520step1Labels = mixedMoment B raw10520step2 raw10520step2Labels := by
      have ha : raw10520step2 = raw10520step1 := by apply Matrix.ext; unfold raw10520step2 raw10520step1; decide +kernel
      have hl : raw10520step1Labels = labelEmbedding9 ∘ raw10520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10520step1 raw10520step1Labels raw10520step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw10521 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10521step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10521 raw10521Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw10521 raw10521Labels = mixedMoment B raw10521step0 raw10521step0Labels := by
      have hz : ∀ j, raw10521 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10521step0 = (fun i j => raw10521 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10521step0 raw10521; decide +kernel
      have hl : raw10521step0Labels = raw10521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10521 raw10521Labels permutation265 hz
    mixedMoment B raw10521step0 raw10521step0Labels = mixedMoment B raw10521step1 raw10521step1Labels := by
      have ha : raw10521step1 = (fun i j => raw10521step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10521step1 raw10521step0; decide +kernel
      have hl : raw10521step1Labels = raw10521step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10521step0 raw10521step0Labels permutation32 permutation6
    mixedMoment B raw10521step1 raw10521step1Labels = mixedMoment B raw10521step2 raw10521step2Labels := by
      have ha : raw10521step2 = raw10521step1 := by apply Matrix.ext; unfold raw10521step2 raw10521step1; decide +kernel
      have hl : raw10521step1Labels = labelEmbedding9 ∘ raw10521step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10521step1 raw10521step1Labels raw10521step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw10522 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10522step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10522step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw10522step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10522step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw10522step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10522 raw10522Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw10522 raw10522Labels = mixedMoment B raw10522step0 raw10522step0Labels := by
      have hz : ∀ j, raw10522 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10522step0 = (fun i j => raw10522 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10522step0 raw10522; decide +kernel
      have hl : raw10522step0Labels = raw10522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10522 raw10522Labels permutation346 hz
    mixedMoment B raw10522step0 raw10522step0Labels = mixedMoment B raw10522step1 raw10522step1Labels := by
      have hz : ∀ j, raw10522step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10522step1 = (fun i j => raw10522step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10522step1 raw10522step0; decide +kernel
      have hl : raw10522step1Labels = raw10522step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10522step0 raw10522step0Labels permutation56 hz
    mixedMoment B raw10522step1 raw10522step1Labels = mixedMoment B raw10522step2 raw10522step2Labels := by
      have ha : raw10522step2 = (fun i j => raw10522step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10522step2 raw10522step1; decide +kernel
      have hl : raw10522step2Labels = raw10522step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10522step1 raw10522step1Labels permutation8 permutation6
    mixedMoment B raw10522step2 raw10522step2Labels = mixedMoment B raw10522step3 raw10522step3Labels := by
      have ha : raw10522step3 = raw10522step2 := by apply Matrix.ext; unfold raw10522step3 raw10522step2; decide +kernel
      have hl : raw10522step2Labels = labelEmbedding9 ∘ raw10522step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10522step2 raw10522step2Labels raw10522step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw10523 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10523Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10523step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10523step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10523 raw10523Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw10523 raw10523Labels = mixedMoment B raw10523step0 raw10523step0Labels := by
      have hz : ∀ j, raw10523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10523step0 = (fun i j => raw10523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10523step0 raw10523; decide +kernel
      have hl : raw10523step0Labels = raw10523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10523 raw10523Labels permutation346 hz
    mixedMoment B raw10523step0 raw10523step0Labels = mixedMoment B raw10523step1 raw10523step1Labels := by
      have ha : raw10523step1 = (fun i j => raw10523step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10523step1 raw10523step0; decide +kernel
      have hl : raw10523step1Labels = raw10523step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10523step0 raw10523step0Labels permutation32 permutation6
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw10524 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10524Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10524step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10524 raw10524Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw10524 raw10524Labels = mixedMoment B raw10524step0 raw10524step0Labels := by
      have hz : ∀ j, raw10524 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10524step0 = (fun i j => raw10524 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10524step0 raw10524; decide +kernel
      have hl : raw10524step0Labels = raw10524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10524 raw10524Labels permutation265 hz
    mixedMoment B raw10524step0 raw10524step0Labels = mixedMoment B raw10524step1 raw10524step1Labels := by
      have ha : raw10524step1 = (fun i j => raw10524step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10524step1 raw10524step0; decide +kernel
      have hl : raw10524step1Labels = raw10524step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10524step0 raw10524step0Labels permutation32 permutation6
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw10525 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10525Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10525step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10525step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw10525step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10525 raw10525Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw10525 raw10525Labels = mixedMoment B raw10525step0 raw10525step0Labels := by
      have hz : ∀ j, raw10525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10525step0 = (fun i j => raw10525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10525step0 raw10525; decide +kernel
      have hl : raw10525step0Labels = raw10525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10525 raw10525Labels permutation346 hz
    mixedMoment B raw10525step0 raw10525step0Labels = mixedMoment B raw10525step1 raw10525step1Labels := by
      have hz : ∀ j, raw10525step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10525step1 = (fun i j => raw10525step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10525step1 raw10525step0; decide +kernel
      have hl : raw10525step1Labels = raw10525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10525step0 raw10525step0Labels permutation56 hz
    mixedMoment B raw10525step1 raw10525step1Labels = mixedMoment B raw10525step2 raw10525step2Labels := by
      have ha : raw10525step2 = (fun i j => raw10525step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10525step2 raw10525step1; decide +kernel
      have hl : raw10525step2Labels = raw10525step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10525step1 raw10525step1Labels permutation8 permutation6
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw10526 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10526Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10526step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10526 raw10526Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw10526 raw10526Labels = mixedMoment B raw10526step0 raw10526step0Labels := by
      have hz : ∀ j, raw10526 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10526step0 = (fun i j => raw10526 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10526step0 raw10526; decide +kernel
      have hl : raw10526step0Labels = raw10526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10526 raw10526Labels permutation265 hz
    mixedMoment B raw10526step0 raw10526step0Labels = mixedMoment B raw10526step1 raw10526step1Labels := by
      have ha : raw10526step1 = (fun i j => raw10526step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10526step1 raw10526step0; decide +kernel
      have hl : raw10526step1Labels = raw10526step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10526step0 raw10526step0Labels permutation38 permutation6
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw10527 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10527Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10527 raw10527Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw10527 raw10527Labels = mixedMoment B raw10527step0 raw10527step0Labels := by
      have ha : raw10527step0 = (fun i j => raw10527 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10527step0 raw10527; decide +kernel
      have hl : raw10527step0Labels = raw10527Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10527 raw10527Labels permutation158 permutation6
    _ = mixedMoment B node2695 node2695Labels := by rfl

def raw10528 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10528Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10528step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw10528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10528 raw10528Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw10528 raw10528Labels = mixedMoment B raw10528step0 raw10528step0Labels := by
      have hz : ∀ j, raw10528 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10528step0 = (fun i j => raw10528 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10528step0 raw10528; decide +kernel
      have hl : raw10528step0Labels = raw10528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10528 raw10528Labels permutation265 hz
    mixedMoment B raw10528step0 raw10528step0Labels = mixedMoment B raw10528step1 raw10528step1Labels := by
      have ha : raw10528step1 = (fun i j => raw10528step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10528step1 raw10528step0; decide +kernel
      have hl : raw10528step1Labels = raw10528step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10528step0 raw10528step0Labels permutation38 permutation6
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw10529 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10529Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10529step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10529step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10529 raw10529Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw10529 raw10529Labels = mixedMoment B raw10529step0 raw10529step0Labels := by
      have hz : ∀ j, raw10529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10529step0 = (fun i j => raw10529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10529step0 raw10529; decide +kernel
      have hl : raw10529step0Labels = raw10529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10529 raw10529Labels permutation346 hz
    mixedMoment B raw10529step0 raw10529step0Labels = mixedMoment B raw10529step1 raw10529step1Labels := by
      have hz : ∀ j, raw10529step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10529step1 = (fun i j => raw10529step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10529step1 raw10529step0; decide +kernel
      have hl : raw10529step1Labels = raw10529step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10529step0 raw10529step0Labels permutation56 hz
    mixedMoment B raw10529step1 raw10529step1Labels = mixedMoment B raw10529step2 raw10529step2Labels := by
      have ha : raw10529step2 = (fun i j => raw10529step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10529step2 raw10529step1; decide +kernel
      have hl : raw10529step2Labels = raw10529step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10529step1 raw10529step1Labels permutation8 permutation6
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw10530 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10530Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10530step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw10530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10530 raw10530Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw10530 raw10530Labels = mixedMoment B raw10530step0 raw10530step0Labels := by
      have hz : ∀ j, raw10530 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10530step0 = (fun i j => raw10530 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10530step0 raw10530; decide +kernel
      have hl : raw10530step0Labels = raw10530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10530 raw10530Labels permutation265 hz
    mixedMoment B raw10530step0 raw10530step0Labels = mixedMoment B raw10530step1 raw10530step1Labels := by
      have ha : raw10530step1 = (fun i j => raw10530step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10530step1 raw10530step0; decide +kernel
      have hl : raw10530step1Labels = raw10530step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10530step0 raw10530step0Labels permutation32 permutation6
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw10531 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10531step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10531step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10531step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw10531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10531 raw10531Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw10531 raw10531Labels = mixedMoment B raw10531step0 raw10531step0Labels := by
      have hz : ∀ j, raw10531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10531step0 = (fun i j => raw10531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10531step0 raw10531; decide +kernel
      have hl : raw10531step0Labels = raw10531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10531 raw10531Labels permutation346 hz
    mixedMoment B raw10531step0 raw10531step0Labels = mixedMoment B raw10531step1 raw10531step1Labels := by
      have hz : ∀ j, raw10531step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10531step1 = (fun i j => raw10531step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10531step1 raw10531step0; decide +kernel
      have hl : raw10531step1Labels = raw10531step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10531step0 raw10531step0Labels permutation56 hz
    mixedMoment B raw10531step1 raw10531step1Labels = mixedMoment B raw10531step2 raw10531step2Labels := by
      have ha : raw10531step2 = (fun i j => raw10531step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10531step2 raw10531step1; decide +kernel
      have hl : raw10531step2Labels = raw10531step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10531step1 raw10531step1Labels permutation8 permutation6
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw10532 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10532step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10532step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10532step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10532step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10532 raw10532Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw10532 raw10532Labels = mixedMoment B raw10532step0 raw10532step0Labels := by
      have hz : ∀ j, raw10532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10532step0 = (fun i j => raw10532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10532step0 raw10532; decide +kernel
      have hl : raw10532step0Labels = raw10532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10532 raw10532Labels permutation346 hz
    mixedMoment B raw10532step0 raw10532step0Labels = mixedMoment B raw10532step1 raw10532step1Labels := by
      have hz : ∀ j, raw10532step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10532step1 = (fun i j => raw10532step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10532step1 raw10532step0; decide +kernel
      have hl : raw10532step1Labels = raw10532step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10532step0 raw10532step0Labels permutation56 hz
    mixedMoment B raw10532step1 raw10532step1Labels = mixedMoment B raw10532step2 raw10532step2Labels := by
      have ha : raw10532step2 = (fun i j => raw10532step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10532step2 raw10532step1; decide +kernel
      have hl : raw10532step2Labels = raw10532step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10532step1 raw10532step1Labels permutation8 permutation6
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw10533 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10533step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10533step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10533 raw10533Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw10533 raw10533Labels = mixedMoment B raw10533step0 raw10533step0Labels := by
      have hz : ∀ j, raw10533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10533step0 = (fun i j => raw10533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10533step0 raw10533; decide +kernel
      have hl : raw10533step0Labels = raw10533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10533 raw10533Labels permutation346 hz
    mixedMoment B raw10533step0 raw10533step0Labels = mixedMoment B raw10533step1 raw10533step1Labels := by
      have ha : raw10533step1 = (fun i j => raw10533step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10533step1 raw10533step0; decide +kernel
      have hl : raw10533step1Labels = raw10533step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10533step0 raw10533step0Labels permutation32 permutation6
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw10534 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10534 raw10534Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw10534 raw10534Labels = mixedMoment B raw10534step0 raw10534step0Labels := by
      have hz : ∀ j, raw10534 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10534step0 = (fun i j => raw10534 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10534step0 raw10534; decide +kernel
      have hl : raw10534step0Labels = raw10534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10534 raw10534Labels permutation265 hz
    mixedMoment B raw10534step0 raw10534step0Labels = mixedMoment B raw10534step1 raw10534step1Labels := by
      have ha : raw10534step1 = (fun i j => raw10534step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10534step1 raw10534step0; decide +kernel
      have hl : raw10534step1Labels = raw10534step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10534step0 raw10534step0Labels permutation32 permutation6
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw10535 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10535step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw10535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10535 raw10535Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw10535 raw10535Labels = mixedMoment B raw10535step0 raw10535step0Labels := by
      have hz : ∀ j, raw10535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10535step0 = (fun i j => raw10535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10535step0 raw10535; decide +kernel
      have hl : raw10535step0Labels = raw10535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10535 raw10535Labels permutation346 hz
    mixedMoment B raw10535step0 raw10535step0Labels = mixedMoment B raw10535step1 raw10535step1Labels := by
      have hz : ∀ j, raw10535step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10535step1 = (fun i j => raw10535step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10535step1 raw10535step0; decide +kernel
      have hl : raw10535step1Labels = raw10535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10535step0 raw10535step0Labels permutation56 hz
    mixedMoment B raw10535step1 raw10535step1Labels = mixedMoment B raw10535step2 raw10535step2Labels := by
      have ha : raw10535step2 = (fun i j => raw10535step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10535step2 raw10535step1; decide +kernel
      have hl : raw10535step2Labels = raw10535step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10535step1 raw10535step1Labels permutation8 permutation6
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw10536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw10536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw10536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw10536step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10536 raw10536Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw10536 raw10536Labels = mixedMoment B raw10536step0 raw10536step0Labels := by
      have hz : ∀ j, raw10536 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10536step0 = (fun i j => raw10536 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10536step0 raw10536; decide +kernel
      have hl : raw10536step0Labels = raw10536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10536 raw10536Labels permutation265 hz
    mixedMoment B raw10536step0 raw10536step0Labels = mixedMoment B raw10536step1 raw10536step1Labels := by
      have ha : raw10536step1 = (fun i j => raw10536step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10536step1 raw10536step0; decide +kernel
      have hl : raw10536step1Labels = raw10536step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10536step0 raw10536step0Labels permutation39 permutation4
    mixedMoment B raw10536step1 raw10536step1Labels = mixedMoment B raw10536step2 raw10536step2Labels := by
      have ha : raw10536step2 = -raw10536step1 := by apply Matrix.ext; change ∀ i j, raw10536step2 i j = -(raw10536step1 i j); unfold raw10536step2 raw10536step1; decide +kernel
      have hl : raw10536step2Labels = raw10536step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw10537 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10537step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw10537step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10537step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw10537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10537step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw10537step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10537 raw10537Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw10537 raw10537Labels = mixedMoment B raw10537step0 raw10537step0Labels := by
      have hz : ∀ j, raw10537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10537step0 = (fun i j => raw10537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10537step0 raw10537; decide +kernel
      have hl : raw10537step0Labels = raw10537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10537 raw10537Labels permutation346 hz
    mixedMoment B raw10537step0 raw10537step0Labels = mixedMoment B raw10537step1 raw10537step1Labels := by
      have hz : ∀ j, raw10537step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10537step1 = (fun i j => raw10537step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10537step1 raw10537step0; decide +kernel
      have hl : raw10537step1Labels = raw10537step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10537step0 raw10537step0Labels permutation56 hz
    mixedMoment B raw10537step1 raw10537step1Labels = mixedMoment B raw10537step2 raw10537step2Labels := by
      have ha : raw10537step2 = (fun i j => raw10537step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10537step2 raw10537step1; decide +kernel
      have hl : raw10537step2Labels = raw10537step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10537step1 raw10537step1Labels permutation9 permutation4
    mixedMoment B raw10537step2 raw10537step2Labels = mixedMoment B raw10537step3 raw10537step3Labels := by
      have ha : raw10537step3 = -raw10537step2 := by apply Matrix.ext; change ∀ i j, raw10537step3 i j = -(raw10537step2 i j); unfold raw10537step3 raw10537step2; decide +kernel
      have hl : raw10537step3Labels = raw10537step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw10538 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10538step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw10538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10538step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw10538step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10538step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw10538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10538 raw10538Labels = mixedMoment B node2066 node2066Labels := by
  calc
    mixedMoment B raw10538 raw10538Labels = mixedMoment B raw10538step0 raw10538step0Labels := by
      have hz : ∀ j, raw10538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10538step0 = (fun i j => raw10538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10538step0 raw10538; decide +kernel
      have hl : raw10538step0Labels = raw10538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10538 raw10538Labels permutation346 hz
    mixedMoment B raw10538step0 raw10538step0Labels = mixedMoment B raw10538step1 raw10538step1Labels := by
      have hz : ∀ j, raw10538step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10538step1 = (fun i j => raw10538step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10538step1 raw10538step0; decide +kernel
      have hl : raw10538step1Labels = raw10538step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10538step0 raw10538step0Labels permutation56 hz
    mixedMoment B raw10538step1 raw10538step1Labels = mixedMoment B raw10538step2 raw10538step2Labels := by
      have ha : raw10538step2 = (fun i j => raw10538step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10538step2 raw10538step1; decide +kernel
      have hl : raw10538step2Labels = raw10538step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10538step1 raw10538step1Labels permutation8 permutation4
    mixedMoment B raw10538step2 raw10538step2Labels = mixedMoment B raw10538step3 raw10538step3Labels := by
      have ha : raw10538step3 = -raw10538step2 := by apply Matrix.ext; change ∀ i j, raw10538step3 i j = -(raw10538step2 i j); unfold raw10538step3 raw10538step2; decide +kernel
      have hl : raw10538step3Labels = raw10538step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2066 node2066Labels := by rfl

def raw10539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10539 raw10539Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw10539 raw10539Labels = mixedMoment B raw10539step0 raw10539step0Labels := by
      have hz : ∀ j, raw10539 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10539step0 = (fun i j => raw10539 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10539step0 raw10539; decide +kernel
      have hl : raw10539step0Labels = raw10539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10539 raw10539Labels permutation346 hz
    mixedMoment B raw10539step0 raw10539step0Labels = mixedMoment B raw10539step1 raw10539step1Labels := by
      have ha : raw10539step1 = (fun i j => raw10539step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10539step1 raw10539step0; decide +kernel
      have hl : raw10539step1Labels = raw10539step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10539step0 raw10539step0Labels permutation151 permutation2
    mixedMoment B raw10539step1 raw10539step1Labels = mixedMoment B raw10539step2 raw10539step2Labels := by
      have ha : raw10539step2 = -raw10539step1 := by apply Matrix.ext; change ∀ i j, raw10539step2 i j = -(raw10539step1 i j); unfold raw10539step2 raw10539step1; decide +kernel
      have hl : raw10539step2Labels = raw10539step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw10540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10540step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10540 raw10540Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw10540 raw10540Labels = mixedMoment B raw10540step0 raw10540step0Labels := by
      have hz : ∀ j, raw10540 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10540step0 = (fun i j => raw10540 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10540step0 raw10540; decide +kernel
      have hl : raw10540step0Labels = raw10540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10540 raw10540Labels permutation265 hz
    mixedMoment B raw10540step0 raw10540step0Labels = mixedMoment B raw10540step1 raw10540step1Labels := by
      have ha : raw10540step1 = (fun i j => raw10540step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10540step1 raw10540step0; decide +kernel
      have hl : raw10540step1Labels = raw10540step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10540step0 raw10540step0Labels permutation151 permutation2
    mixedMoment B raw10540step1 raw10540step1Labels = mixedMoment B raw10540step2 raw10540step2Labels := by
      have ha : raw10540step2 = -raw10540step1 := by apply Matrix.ext; change ∀ i j, raw10540step2 i j = -(raw10540step1 i j); unfold raw10540step2 raw10540step1; decide +kernel
      have hl : raw10540step2Labels = raw10540step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw10541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10541step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10541step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw10541step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw10541step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw10541step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical10541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10541 raw10541Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw10541 raw10541Labels = mixedMoment B raw10541step0 raw10541step0Labels := by
      have hz : ∀ j, raw10541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10541step0 = (fun i j => raw10541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10541step0 raw10541; decide +kernel
      have hl : raw10541step0Labels = raw10541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10541 raw10541Labels permutation346 hz
    mixedMoment B raw10541step0 raw10541step0Labels = mixedMoment B raw10541step1 raw10541step1Labels := by
      have hz : ∀ j, raw10541step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10541step1 = (fun i j => raw10541step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10541step1 raw10541step0; decide +kernel
      have hl : raw10541step1Labels = raw10541step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10541step0 raw10541step0Labels permutation56 hz
    mixedMoment B raw10541step1 raw10541step1Labels = mixedMoment B raw10541step2 raw10541step2Labels := by
      have hz : ∀ i, raw10541step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw10541step2 = (fun i j => raw10541step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw10541step2 raw10541step1; decide +kernel
      have hl : raw10541step2Labels = (fun j => raw10541step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw10541step1 raw10541step1Labels permutation4 hz
    mixedMoment B raw10541step2 raw10541step2Labels = mixedMoment B raw10541step3 raw10541step3Labels := by
      have ha : raw10541step3 = raw10541step2 := by apply Matrix.ext; unfold raw10541step3 raw10541step2; decide +kernel
      have hl : raw10541step2Labels = labelEmbedding2 ∘ raw10541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10541step2 raw10541step2Labels raw10541step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw10542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10542step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10542step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10542step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10542step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10542step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10542 raw10542Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw10542 raw10542Labels = mixedMoment B raw10542step0 raw10542step0Labels := by
      have hz : ∀ j, raw10542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10542step0 = (fun i j => raw10542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10542step0 raw10542; decide +kernel
      have hl : raw10542step0Labels = raw10542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10542 raw10542Labels permutation346 hz
    mixedMoment B raw10542step0 raw10542step0Labels = mixedMoment B raw10542step1 raw10542step1Labels := by
      have hz : ∀ j, raw10542step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10542step1 = (fun i j => raw10542step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10542step1 raw10542step0; decide +kernel
      have hl : raw10542step1Labels = raw10542step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10542step0 raw10542step0Labels permutation56 hz
    mixedMoment B raw10542step1 raw10542step1Labels = mixedMoment B raw10542step2 raw10542step2Labels := by
      have ha : raw10542step2 = (fun i j => raw10542step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10542step2 raw10542step1; decide +kernel
      have hl : raw10542step2Labels = raw10542step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10542step1 raw10542step1Labels permutation31 permutation7
    mixedMoment B raw10542step2 raw10542step2Labels = mixedMoment B raw10542step3 raw10542step3Labels := by
      have ha : raw10542step3 = raw10542step2 := by apply Matrix.ext; unfold raw10542step3 raw10542step2; decide +kernel
      have hl : raw10542step2Labels = labelEmbedding10 ∘ raw10542step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10542step2 raw10542step2Labels raw10542step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw10543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10543step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10543step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10543step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw10543step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10543step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10543step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10543step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10543step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10543 raw10543Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw10543 raw10543Labels = mixedMoment B raw10543step0 raw10543step0Labels := by
      have hz : ∀ j, raw10543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10543step0 = (fun i j => raw10543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10543step0 raw10543; decide +kernel
      have hl : raw10543step0Labels = raw10543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10543 raw10543Labels permutation346 hz
    mixedMoment B raw10543step0 raw10543step0Labels = mixedMoment B raw10543step1 raw10543step1Labels := by
      have hz : ∀ j, raw10543step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10543step1 = (fun i j => raw10543step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10543step1 raw10543step0; decide +kernel
      have hl : raw10543step1Labels = raw10543step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10543step0 raw10543step0Labels permutation56 hz
    mixedMoment B raw10543step1 raw10543step1Labels = mixedMoment B raw10543step2 raw10543step2Labels := by
      have ha : raw10543step2 = (fun i j => raw10543step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10543step2 raw10543step1; decide +kernel
      have hl : raw10543step2Labels = raw10543step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10543step1 raw10543step1Labels permutation8 permutation7
    mixedMoment B raw10543step2 raw10543step2Labels = mixedMoment B raw10543step3 raw10543step3Labels := by
      have ha : raw10543step3 = -raw10543step2 := by apply Matrix.ext; change ∀ i j, raw10543step3 i j = -(raw10543step2 i j); unfold raw10543step3 raw10543step2; decide +kernel
      have hl : raw10543step3Labels = raw10543step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10543step3 raw10543step3Labels = mixedMoment B raw10543step4 raw10543step4Labels := by
      have ha : raw10543step4 = raw10543step3 := by apply Matrix.ext; unfold raw10543step4 raw10543step3; decide +kernel
      have hl : raw10543step3Labels = labelEmbedding10 ∘ raw10543step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10543step3 raw10543step3Labels raw10543step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw10544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10544step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10544step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10544 raw10544Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw10544 raw10544Labels = mixedMoment B raw10544step0 raw10544step0Labels := by
      have hz : ∀ j, raw10544 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10544step0 = (fun i j => raw10544 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10544step0 raw10544; decide +kernel
      have hl : raw10544step0Labels = raw10544Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10544 raw10544Labels permutation346 hz
    mixedMoment B raw10544step0 raw10544step0Labels = mixedMoment B raw10544step1 raw10544step1Labels := by
      have ha : raw10544step1 = (fun i j => raw10544step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10544step1 raw10544step0; decide +kernel
      have hl : raw10544step1Labels = raw10544step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10544step0 raw10544step0Labels permutation38 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw10545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10545 raw10545Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw10545 raw10545Labels = mixedMoment B raw10545step0 raw10545step0Labels := by
      have ha : raw10545step0 = (fun i j => raw10545 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10545step0 raw10545; decide +kernel
      have hl : raw10545step0Labels = raw10545Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10545 raw10545Labels permutation182 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw10546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10546step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10546 raw10546Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw10546 raw10546Labels = mixedMoment B raw10546step0 raw10546step0Labels := by
      have hz : ∀ j, raw10546 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10546step0 = (fun i j => raw10546 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10546step0 raw10546; decide +kernel
      have hl : raw10546step0Labels = raw10546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10546 raw10546Labels permutation346 hz
    mixedMoment B raw10546step0 raw10546step0Labels = mixedMoment B raw10546step1 raw10546step1Labels := by
      have ha : raw10546step1 = (fun i j => raw10546step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10546step1 raw10546step0; decide +kernel
      have hl : raw10546step1Labels = raw10546step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10546step0 raw10546step0Labels permutation38 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw10547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10547step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10547 raw10547Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw10547 raw10547Labels = mixedMoment B raw10547step0 raw10547step0Labels := by
      have hz : ∀ j, raw10547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10547step0 = (fun i j => raw10547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10547step0 raw10547; decide +kernel
      have hl : raw10547step0Labels = raw10547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10547 raw10547Labels permutation346 hz
    mixedMoment B raw10547step0 raw10547step0Labels = mixedMoment B raw10547step1 raw10547step1Labels := by
      have ha : raw10547step1 = (fun i j => raw10547step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10547step1 raw10547step0; decide +kernel
      have hl : raw10547step1Labels = raw10547step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10547step0 raw10547step0Labels permutation40 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw10548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10548 raw10548Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10548 raw10548Labels = mixedMoment B raw10548step0 raw10548step0Labels := by
      have hz : ∀ j, raw10548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10548step0 = (fun i j => raw10548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10548step0 raw10548; decide +kernel
      have hl : raw10548step0Labels = raw10548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10548 raw10548Labels permutation346 hz
    mixedMoment B raw10548step0 raw10548step0Labels = mixedMoment B raw10548step1 raw10548step1Labels := by
      have ha : raw10548step1 = (fun i j => raw10548step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10548step1 raw10548step0; decide +kernel
      have hl : raw10548step1Labels = raw10548step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10548step0 raw10548step0Labels permutation38 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw10549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10549 raw10549Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw10549 raw10549Labels = mixedMoment B raw10549step0 raw10549step0Labels := by
      have hz : ∀ j, raw10549 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10549step0 = (fun i j => raw10549 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10549step0 raw10549; decide +kernel
      have hl : raw10549step0Labels = raw10549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10549 raw10549Labels permutation265 hz
    mixedMoment B raw10549step0 raw10549step0Labels = mixedMoment B raw10549step1 raw10549step1Labels := by
      have ha : raw10549step1 = (fun i j => raw10549step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10549step1 raw10549step0; decide +kernel
      have hl : raw10549step1Labels = raw10549step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10549step0 raw10549step0Labels permutation38 permutation2
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw10550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10550 raw10550Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw10550 raw10550Labels = mixedMoment B raw10550step0 raw10550step0Labels := by
      have ha : raw10550step0 = (fun i j => raw10550 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10550step0 raw10550; decide +kernel
      have hl : raw10550step0Labels = raw10550Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10550 raw10550Labels permutation158 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw10551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10551step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10551 raw10551Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw10551 raw10551Labels = mixedMoment B raw10551step0 raw10551step0Labels := by
      have hz : ∀ j, raw10551 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10551step0 = (fun i j => raw10551 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10551step0 raw10551; decide +kernel
      have hl : raw10551step0Labels = raw10551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10551 raw10551Labels permutation265 hz
    mixedMoment B raw10551step0 raw10551step0Labels = mixedMoment B raw10551step1 raw10551step1Labels := by
      have ha : raw10551step1 = (fun i j => raw10551step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10551step1 raw10551step0; decide +kernel
      have hl : raw10551step1Labels = raw10551step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10551step0 raw10551step0Labels permutation38 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw10552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10552step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10552step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10552 raw10552Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw10552 raw10552Labels = mixedMoment B raw10552step0 raw10552step0Labels := by
      have hz : ∀ j, raw10552 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10552step0 = (fun i j => raw10552 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10552step0 raw10552; decide +kernel
      have hl : raw10552step0Labels = raw10552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10552 raw10552Labels permutation265 hz
    mixedMoment B raw10552step0 raw10552step0Labels = mixedMoment B raw10552step1 raw10552step1Labels := by
      have ha : raw10552step1 = (fun i j => raw10552step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10552step1 raw10552step0; decide +kernel
      have hl : raw10552step1Labels = raw10552step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10552step0 raw10552step0Labels permutation40 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw10553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10553step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10553 raw10553Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10553 raw10553Labels = mixedMoment B raw10553step0 raw10553step0Labels := by
      have hz : ∀ j, raw10553 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10553step0 = (fun i j => raw10553 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10553step0 raw10553; decide +kernel
      have hl : raw10553step0Labels = raw10553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10553 raw10553Labels permutation265 hz
    mixedMoment B raw10553step0 raw10553step0Labels = mixedMoment B raw10553step1 raw10553step1Labels := by
      have ha : raw10553step1 = (fun i j => raw10553step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10553step1 raw10553step0; decide +kernel
      have hl : raw10553step1Labels = raw10553step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10553step0 raw10553step0Labels permutation38 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw10554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10554step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10554step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10554 raw10554Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw10554 raw10554Labels = mixedMoment B raw10554step0 raw10554step0Labels := by
      have hz : ∀ j, raw10554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10554step0 = (fun i j => raw10554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10554step0 raw10554; decide +kernel
      have hl : raw10554step0Labels = raw10554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10554 raw10554Labels permutation346 hz
    mixedMoment B raw10554step0 raw10554step0Labels = mixedMoment B raw10554step1 raw10554step1Labels := by
      have hz : ∀ j, raw10554step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10554step1 = (fun i j => raw10554step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10554step1 raw10554step0; decide +kernel
      have hl : raw10554step1Labels = raw10554step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10554step0 raw10554step0Labels permutation56 hz
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw10555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10555step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10555 raw10555Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw10555 raw10555Labels = mixedMoment B raw10555step0 raw10555step0Labels := by
      have hz : ∀ j, raw10555 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10555step0 = (fun i j => raw10555 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10555step0 raw10555; decide +kernel
      have hl : raw10555step0Labels = raw10555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10555 raw10555Labels permutation346 hz
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw10556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10556step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10556 raw10556Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw10556 raw10556Labels = mixedMoment B raw10556step0 raw10556step0Labels := by
      have hz : ∀ j, raw10556 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10556step0 = (fun i j => raw10556 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10556step0 raw10556; decide +kernel
      have hl : raw10556step0Labels = raw10556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10556 raw10556Labels permutation265 hz
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw10557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10557step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10557step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10557step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10557step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10557 raw10557Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw10557 raw10557Labels = mixedMoment B raw10557step0 raw10557step0Labels := by
      have hz : ∀ j, raw10557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10557step0 = (fun i j => raw10557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10557step0 raw10557; decide +kernel
      have hl : raw10557step0Labels = raw10557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10557 raw10557Labels permutation346 hz
    mixedMoment B raw10557step0 raw10557step0Labels = mixedMoment B raw10557step1 raw10557step1Labels := by
      have hz : ∀ j, raw10557step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10557step1 = (fun i j => raw10557step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10557step1 raw10557step0; decide +kernel
      have hl : raw10557step1Labels = raw10557step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10557step0 raw10557step0Labels permutation56 hz
    mixedMoment B raw10557step1 raw10557step1Labels = mixedMoment B raw10557step2 raw10557step2Labels := by
      have ha : raw10557step2 = (fun i j => raw10557step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10557step2 raw10557step1; decide +kernel
      have hl : raw10557step2Labels = raw10557step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10557step1 raw10557step1Labels permutation10 permutation2
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw10558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10558step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10558step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10558 raw10558Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw10558 raw10558Labels = mixedMoment B raw10558step0 raw10558step0Labels := by
      have hz : ∀ j, raw10558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10558step0 = (fun i j => raw10558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10558step0 raw10558; decide +kernel
      have hl : raw10558step0Labels = raw10558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10558 raw10558Labels permutation346 hz
    mixedMoment B raw10558step0 raw10558step0Labels = mixedMoment B raw10558step1 raw10558step1Labels := by
      have hz : ∀ j, raw10558step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10558step1 = (fun i j => raw10558step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10558step1 raw10558step0; decide +kernel
      have hl : raw10558step1Labels = raw10558step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10558step0 raw10558step0Labels permutation56 hz
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw10559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10559step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10559 raw10559Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw10559 raw10559Labels = mixedMoment B raw10559step0 raw10559step0Labels := by
      have hz : ∀ j, raw10559 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10559step0 = (fun i j => raw10559 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10559step0 raw10559; decide +kernel
      have hl : raw10559step0Labels = raw10559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10559 raw10559Labels permutation346 hz
    mixedMoment B raw10559step0 raw10559step0Labels = mixedMoment B raw10559step1 raw10559step1Labels := by
      have hz : ∀ j, raw10559step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10559step1 = (fun i j => raw10559step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10559step1 raw10559step0; decide +kernel
      have hl : raw10559step1Labels = raw10559step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10559step0 raw10559step0Labels permutation56 hz
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw10560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10560step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10560 raw10560Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw10560 raw10560Labels = mixedMoment B raw10560step0 raw10560step0Labels := by
      have hz : ∀ j, raw10560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10560step0 = (fun i j => raw10560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10560step0 raw10560; decide +kernel
      have hl : raw10560step0Labels = raw10560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10560 raw10560Labels permutation346 hz
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw10561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10561step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10561 raw10561Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw10561 raw10561Labels = mixedMoment B raw10561step0 raw10561step0Labels := by
      have hz : ∀ j, raw10561 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10561step0 = (fun i j => raw10561 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10561step0 raw10561; decide +kernel
      have hl : raw10561step0Labels = raw10561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10561 raw10561Labels permutation265 hz
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw10562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10562step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10562step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10562 raw10562Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw10562 raw10562Labels = mixedMoment B raw10562step0 raw10562step0Labels := by
      have hz : ∀ j, raw10562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10562step0 = (fun i j => raw10562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10562step0 raw10562; decide +kernel
      have hl : raw10562step0Labels = raw10562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10562 raw10562Labels permutation346 hz
    mixedMoment B raw10562step0 raw10562step0Labels = mixedMoment B raw10562step1 raw10562step1Labels := by
      have hz : ∀ j, raw10562step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10562step1 = (fun i j => raw10562step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10562step1 raw10562step0; decide +kernel
      have hl : raw10562step1Labels = raw10562step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10562step0 raw10562step0Labels permutation56 hz
    _ = mixedMoment B node5111 node5111Labels := by rfl

def raw10563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw10563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10563step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw10563step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10563step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw10563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10563step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10563step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10563 raw10563Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw10563 raw10563Labels = mixedMoment B raw10563step0 raw10563step0Labels := by
      have hz : ∀ j, raw10563 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10563step0 = (fun i j => raw10563 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10563step0 raw10563; decide +kernel
      have hl : raw10563step0Labels = raw10563Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10563 raw10563Labels permutation346 hz
    mixedMoment B raw10563step0 raw10563step0Labels = mixedMoment B raw10563step1 raw10563step1Labels := by
      have hz : ∀ j, raw10563step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10563step1 = (fun i j => raw10563step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10563step1 raw10563step0; decide +kernel
      have hl : raw10563step1Labels = raw10563step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10563step0 raw10563step0Labels permutation56 hz
    mixedMoment B raw10563step1 raw10563step1Labels = mixedMoment B raw10563step2 raw10563step2Labels := by
      have ha : raw10563step2 = (fun i j => raw10563step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10563step2 raw10563step1; decide +kernel
      have hl : raw10563step2Labels = raw10563step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10563step1 raw10563step1Labels permutation9 permutation2
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw10564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10564step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10564step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10564step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10564 raw10564Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw10564 raw10564Labels = mixedMoment B raw10564step0 raw10564step0Labels := by
      have hz : ∀ j, raw10564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10564step0 = (fun i j => raw10564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10564step0 raw10564; decide +kernel
      have hl : raw10564step0Labels = raw10564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10564 raw10564Labels permutation346 hz
    mixedMoment B raw10564step0 raw10564step0Labels = mixedMoment B raw10564step1 raw10564step1Labels := by
      have hz : ∀ j, raw10564step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10564step1 = (fun i j => raw10564step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10564step1 raw10564step0; decide +kernel
      have hl : raw10564step1Labels = raw10564step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10564step0 raw10564step0Labels permutation56 hz
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw10565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10565step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10565step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10565step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10565step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10565 raw10565Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw10565 raw10565Labels = mixedMoment B raw10565step0 raw10565step0Labels := by
      have hz : ∀ j, raw10565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10565step0 = (fun i j => raw10565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10565step0 raw10565; decide +kernel
      have hl : raw10565step0Labels = raw10565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10565 raw10565Labels permutation346 hz
    mixedMoment B raw10565step0 raw10565step0Labels = mixedMoment B raw10565step1 raw10565step1Labels := by
      have ha : raw10565step1 = (fun i j => raw10565step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10565step1 raw10565step0; decide +kernel
      have hl : raw10565step1Labels = raw10565step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10565step0 raw10565step0Labels permutation151 permutation2
    mixedMoment B raw10565step1 raw10565step1Labels = mixedMoment B raw10565step2 raw10565step2Labels := by
      have ha : raw10565step2 = -raw10565step1 := by apply Matrix.ext; change ∀ i j, raw10565step2 i j = -(raw10565step1 i j); unfold raw10565step2 raw10565step1; decide +kernel
      have hl : raw10565step2Labels = raw10565step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw10566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10566step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10566step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10566step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10566 raw10566Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw10566 raw10566Labels = mixedMoment B raw10566step0 raw10566step0Labels := by
      have hz : ∀ j, raw10566 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10566step0 = (fun i j => raw10566 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10566step0 raw10566; decide +kernel
      have hl : raw10566step0Labels = raw10566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10566 raw10566Labels permutation265 hz
    mixedMoment B raw10566step0 raw10566step0Labels = mixedMoment B raw10566step1 raw10566step1Labels := by
      have ha : raw10566step1 = (fun i j => raw10566step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10566step1 raw10566step0; decide +kernel
      have hl : raw10566step1Labels = raw10566step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10566step0 raw10566step0Labels permutation151 permutation2
    mixedMoment B raw10566step1 raw10566step1Labels = mixedMoment B raw10566step2 raw10566step2Labels := by
      have ha : raw10566step2 = -raw10566step1 := by apply Matrix.ext; change ∀ i j, raw10566step2 i j = -(raw10566step1 i j); unfold raw10566step2 raw10566step1; decide +kernel
      have hl : raw10566step2Labels = raw10566step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw10567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10567step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw10567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10567 raw10567Labels = mixedMoment B node5107 node5107Labels := by
  calc
    mixedMoment B raw10567 raw10567Labels = mixedMoment B raw10567step0 raw10567step0Labels := by
      have hz : ∀ j, raw10567 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10567step0 = (fun i j => raw10567 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10567step0 raw10567; decide +kernel
      have hl : raw10567step0Labels = raw10567Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10567 raw10567Labels permutation346 hz
    mixedMoment B raw10567step0 raw10567step0Labels = mixedMoment B raw10567step1 raw10567step1Labels := by
      have hz : ∀ j, raw10567step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10567step1 = (fun i j => raw10567step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10567step1 raw10567step0; decide +kernel
      have hl : raw10567step1Labels = raw10567step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10567step0 raw10567step0Labels permutation56 hz
    _ = mixedMoment B node5107 node5107Labels := by rfl

def raw10568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10568step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10568step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw10568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10568 raw10568Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw10568 raw10568Labels = mixedMoment B raw10568step0 raw10568step0Labels := by
      have hz : ∀ j, raw10568 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10568step0 = (fun i j => raw10568 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10568step0 raw10568; decide +kernel
      have hl : raw10568step0Labels = raw10568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10568 raw10568Labels permutation346 hz
    mixedMoment B raw10568step0 raw10568step0Labels = mixedMoment B raw10568step1 raw10568step1Labels := by
      have hz : ∀ j, raw10568step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10568step1 = (fun i j => raw10568step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10568step1 raw10568step0; decide +kernel
      have hl : raw10568step1Labels = raw10568step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10568step0 raw10568step0Labels permutation56 hz
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw10569 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10569step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10569step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10569 raw10569Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw10569 raw10569Labels = mixedMoment B raw10569step0 raw10569step0Labels := by
      have hz : ∀ j, raw10569 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10569step0 = (fun i j => raw10569 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10569step0 raw10569; decide +kernel
      have hl : raw10569step0Labels = raw10569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10569 raw10569Labels permutation346 hz
    mixedMoment B raw10569step0 raw10569step0Labels = mixedMoment B raw10569step1 raw10569step1Labels := by
      have ha : raw10569step1 = (fun i j => raw10569step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10569step1 raw10569step0; decide +kernel
      have hl : raw10569step1Labels = raw10569step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10569step0 raw10569step0Labels permutation32 permutation7
    mixedMoment B raw10569step1 raw10569step1Labels = mixedMoment B raw10569step2 raw10569step2Labels := by
      have ha : raw10569step2 = raw10569step1 := by apply Matrix.ext; unfold raw10569step2 raw10569step1; decide +kernel
      have hl : raw10569step1Labels = labelEmbedding10 ∘ raw10569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10569step1 raw10569step1Labels raw10569step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw10570 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10570Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10570step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10570step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10570step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10570step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10570step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10570step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10570 raw10570Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw10570 raw10570Labels = mixedMoment B raw10570step0 raw10570step0Labels := by
      have hz : ∀ j, raw10570 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10570step0 = (fun i j => raw10570 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10570step0 raw10570; decide +kernel
      have hl : raw10570step0Labels = raw10570Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10570 raw10570Labels permutation265 hz
    mixedMoment B raw10570step0 raw10570step0Labels = mixedMoment B raw10570step1 raw10570step1Labels := by
      have ha : raw10570step1 = (fun i j => raw10570step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10570step1 raw10570step0; decide +kernel
      have hl : raw10570step1Labels = raw10570step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10570step0 raw10570step0Labels permutation32 permutation7
    mixedMoment B raw10570step1 raw10570step1Labels = mixedMoment B raw10570step2 raw10570step2Labels := by
      have ha : raw10570step2 = raw10570step1 := by apply Matrix.ext; unfold raw10570step2 raw10570step1; decide +kernel
      have hl : raw10570step1Labels = labelEmbedding10 ∘ raw10570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10570step1 raw10570step1Labels raw10570step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw10571 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10571step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10571step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10571step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10571step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10571step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10571step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw10571step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10571 raw10571Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw10571 raw10571Labels = mixedMoment B raw10571step0 raw10571step0Labels := by
      have hz : ∀ j, raw10571 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10571step0 = (fun i j => raw10571 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10571step0 raw10571; decide +kernel
      have hl : raw10571step0Labels = raw10571Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10571 raw10571Labels permutation346 hz
    mixedMoment B raw10571step0 raw10571step0Labels = mixedMoment B raw10571step1 raw10571step1Labels := by
      have hz : ∀ j, raw10571step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10571step1 = (fun i j => raw10571step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10571step1 raw10571step0; decide +kernel
      have hl : raw10571step1Labels = raw10571step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10571step0 raw10571step0Labels permutation56 hz
    mixedMoment B raw10571step1 raw10571step1Labels = mixedMoment B raw10571step2 raw10571step2Labels := by
      have ha : raw10571step2 = (fun i j => raw10571step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10571step2 raw10571step1; decide +kernel
      have hl : raw10571step2Labels = raw10571step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10571step1 raw10571step1Labels permutation8 permutation7
    mixedMoment B raw10571step2 raw10571step2Labels = mixedMoment B raw10571step3 raw10571step3Labels := by
      have ha : raw10571step3 = raw10571step2 := by apply Matrix.ext; unfold raw10571step3 raw10571step2; decide +kernel
      have hl : raw10571step2Labels = labelEmbedding10 ∘ raw10571step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10571step2 raw10571step2Labels raw10571step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw10572 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10572Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10572step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10572step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10572step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10572step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10572step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10572step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10572step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10572step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10572 raw10572Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw10572 raw10572Labels = mixedMoment B raw10572step0 raw10572step0Labels := by
      have hz : ∀ j, raw10572 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10572step0 = (fun i j => raw10572 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10572step0 raw10572; decide +kernel
      have hl : raw10572step0Labels = raw10572Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10572 raw10572Labels permutation265 hz
    mixedMoment B raw10572step0 raw10572step0Labels = mixedMoment B raw10572step1 raw10572step1Labels := by
      have ha : raw10572step1 = (fun i j => raw10572step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10572step1 raw10572step0; decide +kernel
      have hl : raw10572step1Labels = raw10572step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10572step0 raw10572step0Labels permutation38 permutation4
    mixedMoment B raw10572step1 raw10572step1Labels = mixedMoment B raw10572step2 raw10572step2Labels := by
      have ha : raw10572step2 = -raw10572step1 := by apply Matrix.ext; change ∀ i j, raw10572step2 i j = -(raw10572step1 i j); unfold raw10572step2 raw10572step1; decide +kernel
      have hl : raw10572step2Labels = raw10572step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10572step2 raw10572step2Labels = mixedMoment B raw10572step3 raw10572step3Labels := by
      have ha : raw10572step3 = raw10572step2 := by apply Matrix.ext; unfold raw10572step3 raw10572step2; decide +kernel
      have hl : raw10572step2Labels = labelEmbedding7 ∘ raw10572step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10572step2 raw10572step2Labels raw10572step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw10573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10573Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10573step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10573step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10573 raw10573Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw10573 raw10573Labels = mixedMoment B raw10573step0 raw10573step0Labels := by
      have ha : raw10573step0 = (fun i j => raw10573 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10573step0 raw10573; decide +kernel
      have hl : raw10573step0Labels = raw10573Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10573 raw10573Labels permutation158 permutation6
    mixedMoment B raw10573step0 raw10573step0Labels = mixedMoment B raw10573step1 raw10573step1Labels := by
      have ha : raw10573step1 = raw10573step0 := by apply Matrix.ext; unfold raw10573step1 raw10573step0; decide +kernel
      have hl : raw10573step0Labels = labelEmbedding9 ∘ raw10573step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10573step0 raw10573step0Labels raw10573step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw10574 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10574step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10574step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10574step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10574step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10574 raw10574Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw10574 raw10574Labels = mixedMoment B raw10574step0 raw10574step0Labels := by
      have hz : ∀ j, raw10574 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10574step0 = (fun i j => raw10574 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10574step0 raw10574; decide +kernel
      have hl : raw10574step0Labels = raw10574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10574 raw10574Labels permutation265 hz
    mixedMoment B raw10574step0 raw10574step0Labels = mixedMoment B raw10574step1 raw10574step1Labels := by
      have ha : raw10574step1 = (fun i j => raw10574step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10574step1 raw10574step0; decide +kernel
      have hl : raw10574step1Labels = raw10574step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10574step0 raw10574step0Labels permutation38 permutation6
    mixedMoment B raw10574step1 raw10574step1Labels = mixedMoment B raw10574step2 raw10574step2Labels := by
      have ha : raw10574step2 = raw10574step1 := by apply Matrix.ext; unfold raw10574step2 raw10574step1; decide +kernel
      have hl : raw10574step1Labels = labelEmbedding9 ∘ raw10574step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10574step1 raw10574step1Labels raw10574step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw10575 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10575Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10575step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10575step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10575step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10575step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![0, -1, 1], ![0, -2, 2]]
def raw10575step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10575step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw10575step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw10575step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw10575step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw10575step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw10575step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical10575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10575 raw10575Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw10575 raw10575Labels = mixedMoment B raw10575step0 raw10575step0Labels := by
      have hz : ∀ j, raw10575 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10575step0 = (fun i j => raw10575 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10575step0 raw10575; decide +kernel
      have hl : raw10575step0Labels = raw10575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10575 raw10575Labels permutation434 hz
    mixedMoment B raw10575step0 raw10575step0Labels = mixedMoment B raw10575step1 raw10575step1Labels := by
      have hz : ∀ j, raw10575step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10575step1 = (fun i j => raw10575step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10575step1 raw10575step0; decide +kernel
      have hl : raw10575step1Labels = raw10575step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10575step0 raw10575step0Labels permutation80 hz
    mixedMoment B raw10575step1 raw10575step1Labels = mixedMoment B raw10575step2 raw10575step2Labels := by
      have hz : ∀ j, raw10575step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10575step2 = (fun i j => raw10575step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10575step2 raw10575step1; decide +kernel
      have hl : raw10575step2Labels = raw10575step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10575step1 raw10575step1Labels permutation14 hz
    mixedMoment B raw10575step2 raw10575step2Labels = mixedMoment B raw10575step3 raw10575step3Labels := by
      have hz : ∀ i, raw10575step2 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw10575step3 = (fun i j => raw10575step2 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw10575step3 raw10575step2; decide +kernel
      have hl : raw10575step3Labels = (fun j => raw10575step2Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw10575step2 raw10575step2Labels permutation2 hz
    mixedMoment B raw10575step3 raw10575step3Labels = mixedMoment B raw10575step4 raw10575step4Labels := by
      have ha : raw10575step4 = -raw10575step3 := by apply Matrix.ext; change ∀ i j, raw10575step4 i j = -(raw10575step3 i j); unfold raw10575step4 raw10575step3; decide +kernel
      have hl : raw10575step4Labels = raw10575step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10575step4 raw10575step4Labels = mixedMoment B raw10575step5 raw10575step5Labels := by
      have ha : raw10575step5 = raw10575step4 := by apply Matrix.ext; unfold raw10575step5 raw10575step4; decide +kernel
      have hl : raw10575step4Labels = labelEmbedding3 ∘ raw10575step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10575step4 raw10575step4Labels raw10575step5Labels labelEmbedding3 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw10576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10576Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10576step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10576step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10576step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10576step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10576step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10576step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10576step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10576 raw10576Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw10576 raw10576Labels = mixedMoment B raw10576step0 raw10576step0Labels := by
      have hz : ∀ j, raw10576 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10576step0 = (fun i j => raw10576 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10576step0 raw10576; decide +kernel
      have hl : raw10576step0Labels = raw10576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10576 raw10576Labels permutation434 hz
    mixedMoment B raw10576step0 raw10576step0Labels = mixedMoment B raw10576step1 raw10576step1Labels := by
      have hz : ∀ j, raw10576step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10576step1 = (fun i j => raw10576step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10576step1 raw10576step0; decide +kernel
      have hl : raw10576step1Labels = raw10576step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10576step0 raw10576step0Labels permutation80 hz
    mixedMoment B raw10576step1 raw10576step1Labels = mixedMoment B raw10576step2 raw10576step2Labels := by
      have ha : raw10576step2 = (fun i j => raw10576step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10576step2 raw10576step1; decide +kernel
      have hl : raw10576step2Labels = raw10576step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10576step1 raw10576step1Labels permutation8 permutation6
    mixedMoment B raw10576step2 raw10576step2Labels = mixedMoment B raw10576step3 raw10576step3Labels := by
      have ha : raw10576step3 = raw10576step2 := by apply Matrix.ext; unfold raw10576step3 raw10576step2; decide +kernel
      have hl : raw10576step2Labels = labelEmbedding9 ∘ raw10576step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10576step2 raw10576step2Labels raw10576step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw10577 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10577step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw10577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10577step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10577step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10577step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10577step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10577 raw10577Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw10577 raw10577Labels = mixedMoment B raw10577step0 raw10577step0Labels := by
      have hz : ∀ j, raw10577 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10577step0 = (fun i j => raw10577 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10577step0 raw10577; decide +kernel
      have hl : raw10577step0Labels = raw10577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10577 raw10577Labels permutation434 hz
    mixedMoment B raw10577step0 raw10577step0Labels = mixedMoment B raw10577step1 raw10577step1Labels := by
      have hz : ∀ j, raw10577step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10577step1 = (fun i j => raw10577step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10577step1 raw10577step0; decide +kernel
      have hl : raw10577step1Labels = raw10577step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10577step0 raw10577step0Labels permutation56 hz
    mixedMoment B raw10577step1 raw10577step1Labels = mixedMoment B raw10577step2 raw10577step2Labels := by
      have ha : raw10577step2 = (fun i j => raw10577step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10577step2 raw10577step1; decide +kernel
      have hl : raw10577step2Labels = raw10577step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10577step1 raw10577step1Labels permutation8 permutation6
    mixedMoment B raw10577step2 raw10577step2Labels = mixedMoment B raw10577step3 raw10577step3Labels := by
      have ha : raw10577step3 = raw10577step2 := by apply Matrix.ext; unfold raw10577step3 raw10577step2; decide +kernel
      have hl : raw10577step2Labels = labelEmbedding9 ∘ raw10577step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10577step2 raw10577step2Labels raw10577step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw10578 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10578step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10578step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10578step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw10578step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10578step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw10578step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10578step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw10578step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10578 raw10578Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw10578 raw10578Labels = mixedMoment B raw10578step0 raw10578step0Labels := by
      have hz : ∀ j, raw10578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10578step0 = (fun i j => raw10578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10578step0 raw10578; decide +kernel
      have hl : raw10578step0Labels = raw10578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10578 raw10578Labels permutation346 hz
    mixedMoment B raw10578step0 raw10578step0Labels = mixedMoment B raw10578step1 raw10578step1Labels := by
      have hz : ∀ j, raw10578step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10578step1 = (fun i j => raw10578step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10578step1 raw10578step0; decide +kernel
      have hl : raw10578step1Labels = raw10578step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10578step0 raw10578step0Labels permutation56 hz
    mixedMoment B raw10578step1 raw10578step1Labels = mixedMoment B raw10578step2 raw10578step2Labels := by
      have ha : raw10578step2 = (fun i j => raw10578step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10578step2 raw10578step1; decide +kernel
      have hl : raw10578step2Labels = raw10578step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10578step1 raw10578step1Labels permutation8 permutation4
    mixedMoment B raw10578step2 raw10578step2Labels = mixedMoment B raw10578step3 raw10578step3Labels := by
      have ha : raw10578step3 = -raw10578step2 := by apply Matrix.ext; change ∀ i j, raw10578step3 i j = -(raw10578step2 i j); unfold raw10578step3 raw10578step2; decide +kernel
      have hl : raw10578step3Labels = raw10578step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10578step3 raw10578step3Labels = mixedMoment B raw10578step4 raw10578step4Labels := by
      have ha : raw10578step4 = raw10578step3 := by apply Matrix.ext; unfold raw10578step4 raw10578step3; decide +kernel
      have hl : raw10578step3Labels = labelEmbedding7 ∘ raw10578step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10578step3 raw10578step3Labels raw10578step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw10579 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10579step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10579step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10579step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10579step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10579step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10579 raw10579Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw10579 raw10579Labels = mixedMoment B raw10579step0 raw10579step0Labels := by
      have hz : ∀ j, raw10579 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10579step0 = (fun i j => raw10579 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10579step0 raw10579; decide +kernel
      have hl : raw10579step0Labels = raw10579Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10579 raw10579Labels permutation346 hz
    mixedMoment B raw10579step0 raw10579step0Labels = mixedMoment B raw10579step1 raw10579step1Labels := by
      have ha : raw10579step1 = (fun i j => raw10579step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10579step1 raw10579step0; decide +kernel
      have hl : raw10579step1Labels = raw10579step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10579step0 raw10579step0Labels permutation149 permutation4
    mixedMoment B raw10579step1 raw10579step1Labels = mixedMoment B raw10579step2 raw10579step2Labels := by
      have ha : raw10579step2 = raw10579step1 := by apply Matrix.ext; unfold raw10579step2 raw10579step1; decide +kernel
      have hl : raw10579step1Labels = labelEmbedding7 ∘ raw10579step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10579step1 raw10579step1Labels raw10579step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw10580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10580step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10580step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10580 raw10580Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw10580 raw10580Labels = mixedMoment B raw10580step0 raw10580step0Labels := by
      have hz : ∀ j, raw10580 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10580step0 = (fun i j => raw10580 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10580step0 raw10580; decide +kernel
      have hl : raw10580step0Labels = raw10580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10580 raw10580Labels permutation265 hz
    mixedMoment B raw10580step0 raw10580step0Labels = mixedMoment B raw10580step1 raw10580step1Labels := by
      have ha : raw10580step1 = (fun i j => raw10580step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10580step1 raw10580step0; decide +kernel
      have hl : raw10580step1Labels = raw10580step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10580step0 raw10580step0Labels permutation149 permutation4
    mixedMoment B raw10580step1 raw10580step1Labels = mixedMoment B raw10580step2 raw10580step2Labels := by
      have ha : raw10580step2 = raw10580step1 := by apply Matrix.ext; unfold raw10580step2 raw10580step1; decide +kernel
      have hl : raw10580step1Labels = labelEmbedding7 ∘ raw10580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10580step1 raw10580step1Labels raw10580step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw10581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10581step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw10581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10581step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10581step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10581step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10581step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10581 raw10581Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw10581 raw10581Labels = mixedMoment B raw10581step0 raw10581step0Labels := by
      have hz : ∀ j, raw10581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10581step0 = (fun i j => raw10581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10581step0 raw10581; decide +kernel
      have hl : raw10581step0Labels = raw10581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10581 raw10581Labels permutation346 hz
    mixedMoment B raw10581step0 raw10581step0Labels = mixedMoment B raw10581step1 raw10581step1Labels := by
      have hz : ∀ j, raw10581step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10581step1 = (fun i j => raw10581step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10581step1 raw10581step0; decide +kernel
      have hl : raw10581step1Labels = raw10581step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10581step0 raw10581step0Labels permutation56 hz
    mixedMoment B raw10581step1 raw10581step1Labels = mixedMoment B raw10581step2 raw10581step2Labels := by
      have ha : raw10581step2 = (fun i j => raw10581step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10581step2 raw10581step1; decide +kernel
      have hl : raw10581step2Labels = raw10581step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10581step1 raw10581step1Labels permutation31 permutation4
    mixedMoment B raw10581step2 raw10581step2Labels = mixedMoment B raw10581step3 raw10581step3Labels := by
      have ha : raw10581step3 = raw10581step2 := by apply Matrix.ext; unfold raw10581step3 raw10581step2; decide +kernel
      have hl : raw10581step2Labels = labelEmbedding7 ∘ raw10581step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10581step2 raw10581step2Labels raw10581step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw10582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10582step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10582 raw10582Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw10582 raw10582Labels = mixedMoment B raw10582step0 raw10582step0Labels := by
      have hz : ∀ j, raw10582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10582step0 = (fun i j => raw10582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10582step0 raw10582; decide +kernel
      have hl : raw10582step0Labels = raw10582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10582 raw10582Labels permutation346 hz
    mixedMoment B raw10582step0 raw10582step0Labels = mixedMoment B raw10582step1 raw10582step1Labels := by
      have ha : raw10582step1 = (fun i j => raw10582step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10582step1 raw10582step0; decide +kernel
      have hl : raw10582step1Labels = raw10582step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10582step0 raw10582step0Labels permutation149 permutation7
    mixedMoment B raw10582step1 raw10582step1Labels = mixedMoment B raw10582step2 raw10582step2Labels := by
      have ha : raw10582step2 = raw10582step1 := by apply Matrix.ext; unfold raw10582step2 raw10582step1; decide +kernel
      have hl : raw10582step1Labels = labelEmbedding10 ∘ raw10582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10582step1 raw10582step1Labels raw10582step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw10583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10583step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10583step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10583step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10583 raw10583Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw10583 raw10583Labels = mixedMoment B raw10583step0 raw10583step0Labels := by
      have hz : ∀ j, raw10583 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10583step0 = (fun i j => raw10583 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10583step0 raw10583; decide +kernel
      have hl : raw10583step0Labels = raw10583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10583 raw10583Labels permutation265 hz
    mixedMoment B raw10583step0 raw10583step0Labels = mixedMoment B raw10583step1 raw10583step1Labels := by
      have ha : raw10583step1 = (fun i j => raw10583step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10583step1 raw10583step0; decide +kernel
      have hl : raw10583step1Labels = raw10583step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10583step0 raw10583step0Labels permutation149 permutation7
    mixedMoment B raw10583step1 raw10583step1Labels = mixedMoment B raw10583step2 raw10583step2Labels := by
      have ha : raw10583step2 = raw10583step1 := by apply Matrix.ext; unfold raw10583step2 raw10583step1; decide +kernel
      have hl : raw10583step1Labels = labelEmbedding10 ∘ raw10583step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10583step1 raw10583step1Labels raw10583step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw10584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10584step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10584step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10584step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10584step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10584step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10584step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10584step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10584 raw10584Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw10584 raw10584Labels = mixedMoment B raw10584step0 raw10584step0Labels := by
      have hz : ∀ j, raw10584 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10584step0 = (fun i j => raw10584 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10584step0 raw10584; decide +kernel
      have hl : raw10584step0Labels = raw10584Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10584 raw10584Labels permutation346 hz
    mixedMoment B raw10584step0 raw10584step0Labels = mixedMoment B raw10584step1 raw10584step1Labels := by
      have hz : ∀ j, raw10584step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10584step1 = (fun i j => raw10584step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10584step1 raw10584step0; decide +kernel
      have hl : raw10584step1Labels = raw10584step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10584step0 raw10584step0Labels permutation56 hz
    mixedMoment B raw10584step1 raw10584step1Labels = mixedMoment B raw10584step2 raw10584step2Labels := by
      have ha : raw10584step2 = (fun i j => raw10584step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10584step2 raw10584step1; decide +kernel
      have hl : raw10584step2Labels = raw10584step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10584step1 raw10584step1Labels permutation31 permutation7
    mixedMoment B raw10584step2 raw10584step2Labels = mixedMoment B raw10584step3 raw10584step3Labels := by
      have ha : raw10584step3 = raw10584step2 := by apply Matrix.ext; unfold raw10584step3 raw10584step2; decide +kernel
      have hl : raw10584step2Labels = labelEmbedding10 ∘ raw10584step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10584step2 raw10584step2Labels raw10584step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw10585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10585step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10585step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10585step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw10585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10585step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10585step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10585step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw10585step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10585 raw10585Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw10585 raw10585Labels = mixedMoment B raw10585step0 raw10585step0Labels := by
      have hz : ∀ j, raw10585 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10585step0 = (fun i j => raw10585 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10585step0 raw10585; decide +kernel
      have hl : raw10585step0Labels = raw10585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10585 raw10585Labels permutation520 hz
    mixedMoment B raw10585step0 raw10585step0Labels = mixedMoment B raw10585step1 raw10585step1Labels := by
      have hz : ∀ j, raw10585step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10585step1 = (fun i j => raw10585step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10585step1 raw10585step0; decide +kernel
      have hl : raw10585step1Labels = raw10585step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10585step0 raw10585step0Labels permutation80 hz
    mixedMoment B raw10585step1 raw10585step1Labels = mixedMoment B raw10585step2 raw10585step2Labels := by
      have hz : ∀ j, raw10585step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10585step2 = (fun i j => raw10585step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10585step2 raw10585step1; decide +kernel
      have hl : raw10585step2Labels = raw10585step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10585step1 raw10585step1Labels permutation14 hz
    mixedMoment B raw10585step2 raw10585step2Labels = mixedMoment B raw10585step3 raw10585step3Labels := by
      have ha : raw10585step3 = (fun i j => raw10585step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10585step3 raw10585step2; decide +kernel
      have hl : raw10585step3Labels = raw10585step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10585step2 raw10585step2Labels permutation7 permutation7
    mixedMoment B raw10585step3 raw10585step3Labels = mixedMoment B raw10585step4 raw10585step4Labels := by
      have ha : raw10585step4 = raw10585step3 := by apply Matrix.ext; unfold raw10585step4 raw10585step3; decide +kernel
      have hl : raw10585step3Labels = labelEmbedding10 ∘ raw10585step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10585step3 raw10585step3Labels raw10585step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw10586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10586step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10586step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10586step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10586step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10586step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10586 raw10586Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw10586 raw10586Labels = mixedMoment B raw10586step0 raw10586step0Labels := by
      have hz : ∀ j, raw10586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10586step0 = (fun i j => raw10586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10586step0 raw10586; decide +kernel
      have hl : raw10586step0Labels = raw10586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10586 raw10586Labels permutation346 hz
    mixedMoment B raw10586step0 raw10586step0Labels = mixedMoment B raw10586step1 raw10586step1Labels := by
      have hz : ∀ j, raw10586step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10586step1 = (fun i j => raw10586step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10586step1 raw10586step0; decide +kernel
      have hl : raw10586step1Labels = raw10586step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10586step0 raw10586step0Labels permutation56 hz
    mixedMoment B raw10586step1 raw10586step1Labels = mixedMoment B raw10586step2 raw10586step2Labels := by
      have ha : raw10586step2 = (fun i j => raw10586step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10586step2 raw10586step1; decide +kernel
      have hl : raw10586step2Labels = raw10586step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10586step1 raw10586step1Labels permutation31 permutation6
    mixedMoment B raw10586step2 raw10586step2Labels = mixedMoment B raw10586step3 raw10586step3Labels := by
      have ha : raw10586step3 = raw10586step2 := by apply Matrix.ext; unfold raw10586step3 raw10586step2; decide +kernel
      have hl : raw10586step2Labels = labelEmbedding9 ∘ raw10586step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10586step2 raw10586step2Labels raw10586step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw10587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10587step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10587 raw10587Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw10587 raw10587Labels = mixedMoment B raw10587step0 raw10587step0Labels := by
      have hz : ∀ j, raw10587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10587step0 = (fun i j => raw10587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10587step0 raw10587; decide +kernel
      have hl : raw10587step0Labels = raw10587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10587 raw10587Labels permutation346 hz
    mixedMoment B raw10587step0 raw10587step0Labels = mixedMoment B raw10587step1 raw10587step1Labels := by
      have ha : raw10587step1 = (fun i j => raw10587step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10587step1 raw10587step0; decide +kernel
      have hl : raw10587step1Labels = raw10587step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10587step0 raw10587step0Labels permutation38 permutation2
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw10588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10588 raw10588Labels = mixedMoment B node5133 node5133Labels := by
  calc
    mixedMoment B raw10588 raw10588Labels = mixedMoment B raw10588step0 raw10588step0Labels := by
      have ha : raw10588step0 = (fun i j => raw10588 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10588step0 raw10588; decide +kernel
      have hl : raw10588step0Labels = raw10588Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10588 raw10588Labels permutation182 permutation2
    _ = mixedMoment B node5133 node5133Labels := by rfl

def raw10589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10589step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10589 raw10589Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw10589 raw10589Labels = mixedMoment B raw10589step0 raw10589step0Labels := by
      have hz : ∀ j, raw10589 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10589step0 = (fun i j => raw10589 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10589step0 raw10589; decide +kernel
      have hl : raw10589step0Labels = raw10589Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10589 raw10589Labels permutation346 hz
    mixedMoment B raw10589step0 raw10589step0Labels = mixedMoment B raw10589step1 raw10589step1Labels := by
      have ha : raw10589step1 = (fun i j => raw10589step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10589step1 raw10589step0; decide +kernel
      have hl : raw10589step1Labels = raw10589step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10589step0 raw10589step0Labels permutation38 permutation2
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw10590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10590step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10590step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10590 raw10590Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw10590 raw10590Labels = mixedMoment B raw10590step0 raw10590step0Labels := by
      have hz : ∀ j, raw10590 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10590step0 = (fun i j => raw10590 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10590step0 raw10590; decide +kernel
      have hl : raw10590step0Labels = raw10590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10590 raw10590Labels permutation520 hz
    mixedMoment B raw10590step0 raw10590step0Labels = mixedMoment B raw10590step1 raw10590step1Labels := by
      have hz : ∀ j, raw10590step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10590step1 = (fun i j => raw10590step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10590step1 raw10590step0; decide +kernel
      have hl : raw10590step1Labels = raw10590step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10590step0 raw10590step0Labels permutation80 hz
    mixedMoment B raw10590step1 raw10590step1Labels = mixedMoment B raw10590step2 raw10590step2Labels := by
      have ha : raw10590step2 = (fun i j => raw10590step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10590step2 raw10590step1; decide +kernel
      have hl : raw10590step2Labels = raw10590step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10590step1 raw10590step1Labels permutation10 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw10591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw10591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10591 raw10591Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw10591 raw10591Labels = mixedMoment B raw10591step0 raw10591step0Labels := by
      have hz : ∀ j, raw10591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10591step0 = (fun i j => raw10591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10591step0 raw10591; decide +kernel
      have hl : raw10591step0Labels = raw10591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10591 raw10591Labels permutation346 hz
    mixedMoment B raw10591step0 raw10591step0Labels = mixedMoment B raw10591step1 raw10591step1Labels := by
      have ha : raw10591step1 = (fun i j => raw10591step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10591step1 raw10591step0; decide +kernel
      have hl : raw10591step1Labels = raw10591step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10591step0 raw10591step0Labels permutation38 permutation2
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw10592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10592 raw10592Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw10592 raw10592Labels = mixedMoment B raw10592step0 raw10592step0Labels := by
      have hz : ∀ j, raw10592 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10592step0 = (fun i j => raw10592 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10592step0 raw10592; decide +kernel
      have hl : raw10592step0Labels = raw10592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10592 raw10592Labels permutation265 hz
    mixedMoment B raw10592step0 raw10592step0Labels = mixedMoment B raw10592step1 raw10592step1Labels := by
      have ha : raw10592step1 = (fun i j => raw10592step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10592step1 raw10592step0; decide +kernel
      have hl : raw10592step1Labels = raw10592step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10592step0 raw10592step0Labels permutation38 permutation2
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw10593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10593 raw10593Labels = mixedMoment B node5133 node5133Labels := by
  calc
    mixedMoment B raw10593 raw10593Labels = mixedMoment B raw10593step0 raw10593step0Labels := by
      have ha : raw10593step0 = (fun i j => raw10593 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10593step0 raw10593; decide +kernel
      have hl : raw10593step0Labels = raw10593Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10593 raw10593Labels permutation158 permutation2
    _ = mixedMoment B node5133 node5133Labels := by rfl

def raw10594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10594 raw10594Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw10594 raw10594Labels = mixedMoment B raw10594step0 raw10594step0Labels := by
      have hz : ∀ j, raw10594 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10594step0 = (fun i j => raw10594 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10594step0 raw10594; decide +kernel
      have hl : raw10594step0Labels = raw10594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10594 raw10594Labels permutation265 hz
    mixedMoment B raw10594step0 raw10594step0Labels = mixedMoment B raw10594step1 raw10594step1Labels := by
      have ha : raw10594step1 = (fun i j => raw10594step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10594step1 raw10594step0; decide +kernel
      have hl : raw10594step1Labels = raw10594step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10594step0 raw10594step0Labels permutation38 permutation2
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw10595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10595step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10595step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10595 raw10595Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw10595 raw10595Labels = mixedMoment B raw10595step0 raw10595step0Labels := by
      have hz : ∀ j, raw10595 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10595step0 = (fun i j => raw10595 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10595step0 raw10595; decide +kernel
      have hl : raw10595step0Labels = raw10595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10595 raw10595Labels permutation520 hz
    mixedMoment B raw10595step0 raw10595step0Labels = mixedMoment B raw10595step1 raw10595step1Labels := by
      have hz : ∀ j, raw10595step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10595step1 = (fun i j => raw10595step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10595step1 raw10595step0; decide +kernel
      have hl : raw10595step1Labels = raw10595step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10595step0 raw10595step0Labels permutation56 hz
    mixedMoment B raw10595step1 raw10595step1Labels = mixedMoment B raw10595step2 raw10595step2Labels := by
      have ha : raw10595step2 = (fun i j => raw10595step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10595step2 raw10595step1; decide +kernel
      have hl : raw10595step2Labels = raw10595step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10595step1 raw10595step1Labels permutation10 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw10596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw10596step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10596 raw10596Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw10596 raw10596Labels = mixedMoment B raw10596step0 raw10596step0Labels := by
      have hz : ∀ j, raw10596 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10596step0 = (fun i j => raw10596 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10596step0 raw10596; decide +kernel
      have hl : raw10596step0Labels = raw10596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10596 raw10596Labels permutation265 hz
    mixedMoment B raw10596step0 raw10596step0Labels = mixedMoment B raw10596step1 raw10596step1Labels := by
      have ha : raw10596step1 = (fun i j => raw10596step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10596step1 raw10596step0; decide +kernel
      have hl : raw10596step1Labels = raw10596step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10596step0 raw10596step0Labels permutation38 permutation2
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw10597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10597step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10597 raw10597Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw10597 raw10597Labels = mixedMoment B raw10597step0 raw10597step0Labels := by
      have hz : ∀ j, raw10597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10597step0 = (fun i j => raw10597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10597step0 raw10597; decide +kernel
      have hl : raw10597step0Labels = raw10597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10597 raw10597Labels permutation346 hz
    mixedMoment B raw10597step0 raw10597step0Labels = mixedMoment B raw10597step1 raw10597step1Labels := by
      have hz : ∀ j, raw10597step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10597step1 = (fun i j => raw10597step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10597step1 raw10597step0; decide +kernel
      have hl : raw10597step1Labels = raw10597step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10597step0 raw10597step0Labels permutation56 hz
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw10598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10598 raw10598Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10598 raw10598Labels = mixedMoment B raw10598step0 raw10598step0Labels := by
      have hz : ∀ j, raw10598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10598step0 = (fun i j => raw10598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10598step0 raw10598; decide +kernel
      have hl : raw10598step0Labels = raw10598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10598 raw10598Labels permutation346 hz
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw10599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10599 raw10599Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw10599 raw10599Labels = mixedMoment B raw10599step0 raw10599step0Labels := by
      have hz : ∀ j, raw10599 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10599step0 = (fun i j => raw10599 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10599step0 raw10599; decide +kernel
      have hl : raw10599step0Labels = raw10599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10599 raw10599Labels permutation265 hz
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw10600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10600step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw10600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10600 raw10600Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw10600 raw10600Labels = mixedMoment B raw10600step0 raw10600step0Labels := by
      have hz : ∀ j, raw10600 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10600step0 = (fun i j => raw10600 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10600step0 raw10600; decide +kernel
      have hl : raw10600step0Labels = raw10600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10600 raw10600Labels permutation520 hz
    mixedMoment B raw10600step0 raw10600step0Labels = mixedMoment B raw10600step1 raw10600step1Labels := by
      have hz : ∀ j, raw10600step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10600step1 = (fun i j => raw10600step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10600step1 raw10600step0; decide +kernel
      have hl : raw10600step1Labels = raw10600step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10600step0 raw10600step0Labels permutation80 hz
    mixedMoment B raw10600step1 raw10600step1Labels = mixedMoment B raw10600step2 raw10600step2Labels := by
      have hz : ∀ j, raw10600step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10600step2 = (fun i j => raw10600step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10600step2 raw10600step1; decide +kernel
      have hl : raw10600step2Labels = raw10600step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10600step1 raw10600step1Labels permutation14 hz
    _ = mixedMoment B node5305 node5305Labels := by rfl

def raw10601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10601step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10601step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10601step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw10601step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10601 raw10601Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw10601 raw10601Labels = mixedMoment B raw10601step0 raw10601step0Labels := by
      have hz : ∀ j, raw10601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10601step0 = (fun i j => raw10601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10601step0 raw10601; decide +kernel
      have hl : raw10601step0Labels = raw10601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10601 raw10601Labels permutation346 hz
    mixedMoment B raw10601step0 raw10601step0Labels = mixedMoment B raw10601step1 raw10601step1Labels := by
      have hz : ∀ j, raw10601step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10601step1 = (fun i j => raw10601step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10601step1 raw10601step0; decide +kernel
      have hl : raw10601step1Labels = raw10601step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10601step0 raw10601step0Labels permutation56 hz
    mixedMoment B raw10601step1 raw10601step1Labels = mixedMoment B raw10601step2 raw10601step2Labels := by
      have ha : raw10601step2 = (fun i j => raw10601step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10601step2 raw10601step1; decide +kernel
      have hl : raw10601step2Labels = raw10601step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10601step1 raw10601step1Labels permutation31 permutation6
    mixedMoment B raw10601step2 raw10601step2Labels = mixedMoment B raw10601step3 raw10601step3Labels := by
      have ha : raw10601step3 = raw10601step2 := by apply Matrix.ext; unfold raw10601step3 raw10601step2; decide +kernel
      have hl : raw10601step2Labels = labelEmbedding9 ∘ raw10601step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10601step2 raw10601step2Labels raw10601step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw10602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10602step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10602step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10602 raw10602Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw10602 raw10602Labels = mixedMoment B raw10602step0 raw10602step0Labels := by
      have hz : ∀ j, raw10602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10602step0 = (fun i j => raw10602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10602step0 raw10602; decide +kernel
      have hl : raw10602step0Labels = raw10602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10602 raw10602Labels permutation346 hz
    mixedMoment B raw10602step0 raw10602step0Labels = mixedMoment B raw10602step1 raw10602step1Labels := by
      have hz : ∀ j, raw10602step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10602step1 = (fun i j => raw10602step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10602step1 raw10602step0; decide +kernel
      have hl : raw10602step1Labels = raw10602step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10602step0 raw10602step0Labels permutation56 hz
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw10603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10603 raw10603Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw10603 raw10603Labels = mixedMoment B raw10603step0 raw10603step0Labels := by
      have hz : ∀ j, raw10603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10603step0 = (fun i j => raw10603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10603step0 raw10603; decide +kernel
      have hl : raw10603step0Labels = raw10603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10603 raw10603Labels permutation346 hz
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw10604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10604 raw10604Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw10604 raw10604Labels = mixedMoment B raw10604step0 raw10604step0Labels := by
      have hz : ∀ j, raw10604 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10604step0 = (fun i j => raw10604 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10604step0 raw10604; decide +kernel
      have hl : raw10604step0Labels = raw10604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10604 raw10604Labels permutation265 hz
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw10605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10605step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10605 raw10605Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw10605 raw10605Labels = mixedMoment B raw10605step0 raw10605step0Labels := by
      have hz : ∀ j, raw10605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10605step0 = (fun i j => raw10605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10605step0 raw10605; decide +kernel
      have hl : raw10605step0Labels = raw10605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10605 raw10605Labels permutation346 hz
    mixedMoment B raw10605step0 raw10605step0Labels = mixedMoment B raw10605step1 raw10605step1Labels := by
      have hz : ∀ j, raw10605step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10605step1 = (fun i j => raw10605step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10605step1 raw10605step0; decide +kernel
      have hl : raw10605step1Labels = raw10605step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10605step0 raw10605step0Labels permutation56 hz
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw10606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10606step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, -2, 0], ![1, 2, -3]]
def raw10606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10606step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw10606step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10606 raw10606Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw10606 raw10606Labels = mixedMoment B raw10606step0 raw10606step0Labels := by
      have hz : ∀ j, raw10606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10606step0 = (fun i j => raw10606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10606step0 raw10606; decide +kernel
      have hl : raw10606step0Labels = raw10606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10606 raw10606Labels permutation346 hz
    mixedMoment B raw10606step0 raw10606step0Labels = mixedMoment B raw10606step1 raw10606step1Labels := by
      have hz : ∀ j, raw10606step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10606step1 = (fun i j => raw10606step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10606step1 raw10606step0; decide +kernel
      have hl : raw10606step1Labels = raw10606step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10606step0 raw10606step0Labels permutation56 hz
    mixedMoment B raw10606step1 raw10606step1Labels = mixedMoment B raw10606step2 raw10606step2Labels := by
      have ha : raw10606step2 = (fun i j => raw10606step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10606step2 raw10606step1; decide +kernel
      have hl : raw10606step2Labels = raw10606step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10606step1 raw10606step1Labels permutation9 permutation2
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw10607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10607step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10607 raw10607Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw10607 raw10607Labels = mixedMoment B raw10607step0 raw10607step0Labels := by
      have hz : ∀ j, raw10607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10607step0 = (fun i j => raw10607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10607step0 raw10607; decide +kernel
      have hl : raw10607step0Labels = raw10607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10607 raw10607Labels permutation346 hz
    mixedMoment B raw10607step0 raw10607step0Labels = mixedMoment B raw10607step1 raw10607step1Labels := by
      have hz : ∀ j, raw10607step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10607step1 = (fun i j => raw10607step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10607step1 raw10607step0; decide +kernel
      have hl : raw10607step1Labels = raw10607step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10607step0 raw10607step0Labels permutation56 hz
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw10608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10608 raw10608Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw10608 raw10608Labels = mixedMoment B raw10608step0 raw10608step0Labels := by
      have hz : ∀ j, raw10608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10608step0 = (fun i j => raw10608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10608step0 raw10608; decide +kernel
      have hl : raw10608step0Labels = raw10608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10608 raw10608Labels permutation346 hz
    mixedMoment B raw10608step0 raw10608step0Labels = mixedMoment B raw10608step1 raw10608step1Labels := by
      have ha : raw10608step1 = (fun i j => raw10608step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10608step1 raw10608step0; decide +kernel
      have hl : raw10608step1Labels = raw10608step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10608step0 raw10608step0Labels permutation151 permutation2
    mixedMoment B raw10608step1 raw10608step1Labels = mixedMoment B raw10608step2 raw10608step2Labels := by
      have ha : raw10608step2 = -raw10608step1 := by apply Matrix.ext; change ∀ i j, raw10608step2 i j = -(raw10608step1 i j); unfold raw10608step2 raw10608step1; decide +kernel
      have hl : raw10608step2Labels = raw10608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw10609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10609step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10609 raw10609Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw10609 raw10609Labels = mixedMoment B raw10609step0 raw10609step0Labels := by
      have hz : ∀ j, raw10609 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10609step0 = (fun i j => raw10609 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10609step0 raw10609; decide +kernel
      have hl : raw10609step0Labels = raw10609Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10609 raw10609Labels permutation265 hz
    mixedMoment B raw10609step0 raw10609step0Labels = mixedMoment B raw10609step1 raw10609step1Labels := by
      have ha : raw10609step1 = (fun i j => raw10609step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10609step1 raw10609step0; decide +kernel
      have hl : raw10609step1Labels = raw10609step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10609step0 raw10609step0Labels permutation151 permutation2
    mixedMoment B raw10609step1 raw10609step1Labels = mixedMoment B raw10609step2 raw10609step2Labels := by
      have ha : raw10609step2 = -raw10609step1 := by apply Matrix.ext; change ∀ i j, raw10609step2 i j = -(raw10609step1 i j); unfold raw10609step2 raw10609step1; decide +kernel
      have hl : raw10609step2Labels = raw10609step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw10610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10610step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw10610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10610step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw10610step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10610step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw10610step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10610 raw10610Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw10610 raw10610Labels = mixedMoment B raw10610step0 raw10610step0Labels := by
      have hz : ∀ j, raw10610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10610step0 = (fun i j => raw10610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10610step0 raw10610; decide +kernel
      have hl : raw10610step0Labels = raw10610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10610 raw10610Labels permutation346 hz
    mixedMoment B raw10610step0 raw10610step0Labels = mixedMoment B raw10610step1 raw10610step1Labels := by
      have hz : ∀ j, raw10610step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10610step1 = (fun i j => raw10610step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10610step1 raw10610step0; decide +kernel
      have hl : raw10610step1Labels = raw10610step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10610step0 raw10610step0Labels permutation56 hz
    mixedMoment B raw10610step1 raw10610step1Labels = mixedMoment B raw10610step2 raw10610step2Labels := by
      have ha : raw10610step2 = (fun i j => raw10610step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10610step2 raw10610step1; decide +kernel
      have hl : raw10610step2Labels = raw10610step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10610step1 raw10610step1Labels permutation31 permutation2
    mixedMoment B raw10610step2 raw10610step2Labels = mixedMoment B raw10610step3 raw10610step3Labels := by
      have ha : raw10610step3 = -raw10610step2 := by apply Matrix.ext; change ∀ i j, raw10610step3 i j = -(raw10610step2 i j); unfold raw10610step3 raw10610step2; decide +kernel
      have hl : raw10610step3Labels = raw10610step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw10611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw10611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10611step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw10611step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10611step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![3, 0, -3]]
def raw10611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10611step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw10611step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10611step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw10611step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10611 raw10611Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw10611 raw10611Labels = mixedMoment B raw10611step0 raw10611step0Labels := by
      have hz : ∀ j, raw10611 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10611step0 = (fun i j => raw10611 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10611step0 raw10611; decide +kernel
      have hl : raw10611step0Labels = raw10611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10611 raw10611Labels permutation520 hz
    mixedMoment B raw10611step0 raw10611step0Labels = mixedMoment B raw10611step1 raw10611step1Labels := by
      have hz : ∀ j, raw10611step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10611step1 = (fun i j => raw10611step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10611step1 raw10611step0; decide +kernel
      have hl : raw10611step1Labels = raw10611step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10611step0 raw10611step0Labels permutation80 hz
    mixedMoment B raw10611step1 raw10611step1Labels = mixedMoment B raw10611step2 raw10611step2Labels := by
      have hz : ∀ j, raw10611step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10611step2 = (fun i j => raw10611step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10611step2 raw10611step1; decide +kernel
      have hl : raw10611step2Labels = raw10611step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10611step1 raw10611step1Labels permutation14 hz
    mixedMoment B raw10611step2 raw10611step2Labels = mixedMoment B raw10611step3 raw10611step3Labels := by
      have ha : raw10611step3 = (fun i j => raw10611step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10611step3 raw10611step2; decide +kernel
      have hl : raw10611step3Labels = raw10611step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10611step2 raw10611step2Labels permutation7 permutation2
    mixedMoment B raw10611step3 raw10611step3Labels = mixedMoment B raw10611step4 raw10611step4Labels := by
      have ha : raw10611step4 = -raw10611step3 := by apply Matrix.ext; change ∀ i j, raw10611step4 i j = -(raw10611step3 i j); unfold raw10611step4 raw10611step3; decide +kernel
      have hl : raw10611step4Labels = raw10611step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw10612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10612 raw10612Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw10612 raw10612Labels = mixedMoment B raw10612step0 raw10612step0Labels := by
      have hz : ∀ j, raw10612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10612step0 = (fun i j => raw10612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10612step0 raw10612; decide +kernel
      have hl : raw10612step0Labels = raw10612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10612 raw10612Labels permutation346 hz
    mixedMoment B raw10612step0 raw10612step0Labels = mixedMoment B raw10612step1 raw10612step1Labels := by
      have ha : raw10612step1 = (fun i j => raw10612step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10612step1 raw10612step0; decide +kernel
      have hl : raw10612step1Labels = raw10612step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10612step0 raw10612step0Labels permutation139 permutation6
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw10613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10613 raw10613Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw10613 raw10613Labels = mixedMoment B raw10613step0 raw10613step0Labels := by
      have hz : ∀ j, raw10613 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10613step0 = (fun i j => raw10613 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10613step0 raw10613; decide +kernel
      have hl : raw10613step0Labels = raw10613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10613 raw10613Labels permutation265 hz
    mixedMoment B raw10613step0 raw10613step0Labels = mixedMoment B raw10613step1 raw10613step1Labels := by
      have ha : raw10613step1 = (fun i j => raw10613step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10613step1 raw10613step0; decide +kernel
      have hl : raw10613step1Labels = raw10613step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10613step0 raw10613step0Labels permutation139 permutation6
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw10614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10614step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10614step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10614step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10614 raw10614Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw10614 raw10614Labels = mixedMoment B raw10614step0 raw10614step0Labels := by
      have hz : ∀ j, raw10614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10614step0 = (fun i j => raw10614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10614step0 raw10614; decide +kernel
      have hl : raw10614step0Labels = raw10614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10614 raw10614Labels permutation346 hz
    mixedMoment B raw10614step0 raw10614step0Labels = mixedMoment B raw10614step1 raw10614step1Labels := by
      have hz : ∀ j, raw10614step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10614step1 = (fun i j => raw10614step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10614step1 raw10614step0; decide +kernel
      have hl : raw10614step1Labels = raw10614step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10614step0 raw10614step0Labels permutation56 hz
    mixedMoment B raw10614step1 raw10614step1Labels = mixedMoment B raw10614step2 raw10614step2Labels := by
      have ha : raw10614step2 = (fun i j => raw10614step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10614step2 raw10614step1; decide +kernel
      have hl : raw10614step2Labels = raw10614step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10614step1 raw10614step1Labels permutation31 permutation6
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw10615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10615step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10615step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10615step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10615step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw10615step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10615step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw10615step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10615 raw10615Labels = mixedMoment B node3124 node3124Labels := by
  calc
    mixedMoment B raw10615 raw10615Labels = mixedMoment B raw10615step0 raw10615step0Labels := by
      have hz : ∀ j, raw10615 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10615step0 = (fun i j => raw10615 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10615step0 raw10615; decide +kernel
      have hl : raw10615step0Labels = raw10615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10615 raw10615Labels permutation520 hz
    mixedMoment B raw10615step0 raw10615step0Labels = mixedMoment B raw10615step1 raw10615step1Labels := by
      have hz : ∀ j, raw10615step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10615step1 = (fun i j => raw10615step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10615step1 raw10615step0; decide +kernel
      have hl : raw10615step1Labels = raw10615step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10615step0 raw10615step0Labels permutation80 hz
    mixedMoment B raw10615step1 raw10615step1Labels = mixedMoment B raw10615step2 raw10615step2Labels := by
      have hz : ∀ j, raw10615step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10615step2 = (fun i j => raw10615step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10615step2 raw10615step1; decide +kernel
      have hl : raw10615step2Labels = raw10615step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10615step1 raw10615step1Labels permutation14 hz
    mixedMoment B raw10615step2 raw10615step2Labels = mixedMoment B raw10615step3 raw10615step3Labels := by
      have ha : raw10615step3 = (fun i j => raw10615step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10615step3 raw10615step2; decide +kernel
      have hl : raw10615step3Labels = raw10615step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10615step2 raw10615step2Labels permutation7 permutation6
    _ = mixedMoment B node3124 node3124Labels := by rfl

def raw10616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10616step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10616step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10616step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10616 raw10616Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw10616 raw10616Labels = mixedMoment B raw10616step0 raw10616step0Labels := by
      have hz : ∀ j, raw10616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10616step0 = (fun i j => raw10616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10616step0 raw10616; decide +kernel
      have hl : raw10616step0Labels = raw10616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10616 raw10616Labels permutation346 hz
    mixedMoment B raw10616step0 raw10616step0Labels = mixedMoment B raw10616step1 raw10616step1Labels := by
      have hz : ∀ j, raw10616step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10616step1 = (fun i j => raw10616step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10616step1 raw10616step0; decide +kernel
      have hl : raw10616step1Labels = raw10616step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10616step0 raw10616step0Labels permutation56 hz
    mixedMoment B raw10616step1 raw10616step1Labels = mixedMoment B raw10616step2 raw10616step2Labels := by
      have ha : raw10616step2 = (fun i j => raw10616step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10616step2 raw10616step1; decide +kernel
      have hl : raw10616step2Labels = raw10616step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10616step1 raw10616step1Labels permutation31 permutation6
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw10617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10617step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10617 raw10617Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw10617 raw10617Labels = mixedMoment B raw10617step0 raw10617step0Labels := by
      have hz : ∀ j, raw10617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10617step0 = (fun i j => raw10617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10617step0 raw10617; decide +kernel
      have hl : raw10617step0Labels = raw10617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10617 raw10617Labels permutation346 hz
    mixedMoment B raw10617step0 raw10617step0Labels = mixedMoment B raw10617step1 raw10617step1Labels := by
      have ha : raw10617step1 = (fun i j => raw10617step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10617step1 raw10617step0; decide +kernel
      have hl : raw10617step1Labels = raw10617step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10617step0 raw10617step0Labels permutation38 permutation3
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw10618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10618 raw10618Labels = mixedMoment B node2940 node2940Labels := by
  calc
    mixedMoment B raw10618 raw10618Labels = mixedMoment B raw10618step0 raw10618step0Labels := by
      have ha : raw10618step0 = (fun i j => raw10618 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10618step0 raw10618; decide +kernel
      have hl : raw10618step0Labels = raw10618Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10618 raw10618Labels permutation182 permutation3
    _ = mixedMoment B node2940 node2940Labels := by rfl

def raw10619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10619step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10619step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10619 raw10619Labels = mixedMoment B node3003 node3003Labels := by
  calc
    mixedMoment B raw10619 raw10619Labels = mixedMoment B raw10619step0 raw10619step0Labels := by
      have hz : ∀ j, raw10619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10619step0 = (fun i j => raw10619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10619step0 raw10619; decide +kernel
      have hl : raw10619step0Labels = raw10619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10619 raw10619Labels permutation346 hz
    mixedMoment B raw10619step0 raw10619step0Labels = mixedMoment B raw10619step1 raw10619step1Labels := by
      have ha : raw10619step1 = (fun i j => raw10619step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10619step1 raw10619step0; decide +kernel
      have hl : raw10619step1Labels = raw10619step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10619step0 raw10619step0Labels permutation38 permutation3
    _ = mixedMoment B node3003 node3003Labels := by rfl

def raw10620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3]]
def raw10620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10620step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10620step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw10620step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10620step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10620 raw10620Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw10620 raw10620Labels = mixedMoment B raw10620step0 raw10620step0Labels := by
      have hz : ∀ j, raw10620 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10620step0 = (fun i j => raw10620 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10620step0 raw10620; decide +kernel
      have hl : raw10620step0Labels = raw10620Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10620 raw10620Labels permutation520 hz
    mixedMoment B raw10620step0 raw10620step0Labels = mixedMoment B raw10620step1 raw10620step1Labels := by
      have hz : ∀ j, raw10620step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10620step1 = (fun i j => raw10620step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10620step1 raw10620step0; decide +kernel
      have hl : raw10620step1Labels = raw10620step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10620step0 raw10620step0Labels permutation80 hz
    mixedMoment B raw10620step1 raw10620step1Labels = mixedMoment B raw10620step2 raw10620step2Labels := by
      have ha : raw10620step2 = (fun i j => raw10620step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10620step2 raw10620step1; decide +kernel
      have hl : raw10620step2Labels = raw10620step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10620step1 raw10620step1Labels permutation10 permutation3
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw10621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3]]
def raw10621step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10621 raw10621Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw10621 raw10621Labels = mixedMoment B raw10621step0 raw10621step0Labels := by
      have hz : ∀ j, raw10621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10621step0 = (fun i j => raw10621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10621step0 raw10621; decide +kernel
      have hl : raw10621step0Labels = raw10621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10621 raw10621Labels permutation346 hz
    mixedMoment B raw10621step0 raw10621step0Labels = mixedMoment B raw10621step1 raw10621step1Labels := by
      have ha : raw10621step1 = (fun i j => raw10621step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10621step1 raw10621step0; decide +kernel
      have hl : raw10621step1Labels = raw10621step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10621step0 raw10621step0Labels permutation139 permutation6
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw10622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10622step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10622 raw10622Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw10622 raw10622Labels = mixedMoment B raw10622step0 raw10622step0Labels := by
      have hz : ∀ j, raw10622 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10622step0 = (fun i j => raw10622 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10622step0 raw10622; decide +kernel
      have hl : raw10622step0Labels = raw10622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10622 raw10622Labels permutation265 hz
    mixedMoment B raw10622step0 raw10622step0Labels = mixedMoment B raw10622step1 raw10622step1Labels := by
      have ha : raw10622step1 = (fun i j => raw10622step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10622step1 raw10622step0; decide +kernel
      have hl : raw10622step1Labels = raw10622step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10622step0 raw10622step0Labels permutation38 permutation3
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw10623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10623 raw10623Labels = mixedMoment B node2940 node2940Labels := by
  calc
    mixedMoment B raw10623 raw10623Labels = mixedMoment B raw10623step0 raw10623step0Labels := by
      have ha : raw10623step0 = (fun i j => raw10623 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10623step0 raw10623; decide +kernel
      have hl : raw10623step0Labels = raw10623Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10623 raw10623Labels permutation158 permutation3
    _ = mixedMoment B node2940 node2940Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
