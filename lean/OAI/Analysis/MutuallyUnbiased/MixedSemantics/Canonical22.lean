import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2816Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2816step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2816step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2816 raw2816Labels = mixedMoment B node526 node526Labels := by
  calc
    mixedMoment B raw2816 raw2816Labels = mixedMoment B raw2816step0 raw2816step0Labels := by
      have hz : ∀ j, raw2816 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2816step0 = (fun i j => raw2816 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2816step0 raw2816; decide +kernel
      have hl : raw2816step0Labels = raw2816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2816 raw2816Labels permutation434 hz
    mixedMoment B raw2816step0 raw2816step0Labels = mixedMoment B raw2816step1 raw2816step1Labels := by
      have ha : raw2816step1 = (fun i j => raw2816step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2816step1 raw2816step0; decide +kernel
      have hl : raw2816step1Labels = raw2816step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2816step0 raw2816step0Labels permutation34 permutation2
    _ = mixedMoment B node526 node526Labels := by rfl

def raw2817 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![0, 0], ![1, -1], ![1, -1]]
def raw2817Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2817step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![0, 0], ![1, -1], ![1, -1]]
def raw2817step0Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2817step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw2817step1Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical2817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2817 raw2817Labels = mixedMoment B node7 node7Labels := by
  calc
    mixedMoment B raw2817 raw2817Labels = mixedMoment B raw2817step0 raw2817step0Labels := by
      have hz : ∀ j, raw2817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2817step0 = (fun i j => raw2817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2817step0 raw2817; decide +kernel
      have hl : raw2817step0Labels = raw2817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2817 raw2817Labels permutation434 hz
    mixedMoment B raw2817step0 raw2817step0Labels = mixedMoment B raw2817step1 raw2817step1Labels := by
      have hz : ∀ j, raw2817step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2817step1 = (fun i j => raw2817step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2817step1 raw2817step0; decide +kernel
      have hl : raw2817step1Labels = raw2817step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2817step0 raw2817step0Labels permutation80 hz
    _ = mixedMoment B node7 node7Labels := by rfl

def raw2818 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2818step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2818step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2818step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2818step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2818 raw2818Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2818 raw2818Labels = mixedMoment B raw2818step0 raw2818step0Labels := by
      have hz : ∀ j, raw2818 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2818step0 = (fun i j => raw2818 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2818step0 raw2818; decide +kernel
      have hl : raw2818step0Labels = raw2818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2818 raw2818Labels permutation434 hz
    mixedMoment B raw2818step0 raw2818step0Labels = mixedMoment B raw2818step1 raw2818step1Labels := by
      have hz : ∀ j, raw2818step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2818step1 = (fun i j => raw2818step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2818step1 raw2818step0; decide +kernel
      have hl : raw2818step1Labels = raw2818step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2818step0 raw2818step0Labels permutation80 hz
    mixedMoment B raw2818step1 raw2818step1Labels = mixedMoment B raw2818step2 raw2818step2Labels := by
      have ha : raw2818step2 = (fun i j => raw2818step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2818step2 raw2818step1; decide +kernel
      have hl : raw2818step2Labels = raw2818step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2818step1 raw2818step1Labels permutation11 permutation2
    mixedMoment B raw2818step2 raw2818step2Labels = mixedMoment B raw2818step3 raw2818step3Labels := by
      have ha : raw2818step3 = -raw2818step2 := by apply Matrix.ext; change ∀ i j, raw2818step3 i j = -(raw2818step2 i j); unfold raw2818step3 raw2818step2; decide +kernel
      have hl : raw2818step3Labels = raw2818step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2819 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2819 raw2819Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2819 raw2819Labels = mixedMoment B raw2819step0 raw2819step0Labels := by
      have hz : ∀ j, raw2819 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2819step0 = (fun i j => raw2819 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2819step0 raw2819; decide +kernel
      have hl : raw2819step0Labels = raw2819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2819 raw2819Labels permutation434 hz
    mixedMoment B raw2819step0 raw2819step0Labels = mixedMoment B raw2819step1 raw2819step1Labels := by
      have ha : raw2819step1 = (fun i j => raw2819step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2819step1 raw2819step0; decide +kernel
      have hl : raw2819step1Labels = raw2819step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2819step0 raw2819step0Labels permutation44 permutation2
    mixedMoment B raw2819step1 raw2819step1Labels = mixedMoment B raw2819step2 raw2819step2Labels := by
      have ha : raw2819step2 = -raw2819step1 := by apply Matrix.ext; change ∀ i j, raw2819step2 i j = -(raw2819step1 i j); unfold raw2819step2 raw2819step1; decide +kernel
      have hl : raw2819step2Labels = raw2819step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2820 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2820 raw2820Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2820 raw2820Labels = mixedMoment B raw2820step0 raw2820step0Labels := by
      have hz : ∀ j, raw2820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2820step0 = (fun i j => raw2820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2820step0 raw2820; decide +kernel
      have hl : raw2820step0Labels = raw2820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2820 raw2820Labels permutation346 hz
    mixedMoment B raw2820step0 raw2820step0Labels = mixedMoment B raw2820step1 raw2820step1Labels := by
      have ha : raw2820step1 = (fun i j => raw2820step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2820step1 raw2820step0; decide +kernel
      have hl : raw2820step1Labels = raw2820step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2820step0 raw2820step0Labels permutation44 permutation2
    mixedMoment B raw2820step1 raw2820step1Labels = mixedMoment B raw2820step2 raw2820step2Labels := by
      have ha : raw2820step2 = -raw2820step1 := by apply Matrix.ext; change ∀ i j, raw2820step2 i j = -(raw2820step1 i j); unfold raw2820step2 raw2820step1; decide +kernel
      have hl : raw2820step2Labels = raw2820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2821step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2]]
def raw2821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2821step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2821step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2821step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2821step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2821 raw2821Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2821 raw2821Labels = mixedMoment B raw2821step0 raw2821step0Labels := by
      have hz : ∀ j, raw2821 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2821step0 = (fun i j => raw2821 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2821step0 raw2821; decide +kernel
      have hl : raw2821step0Labels = raw2821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2821 raw2821Labels permutation520 hz
    mixedMoment B raw2821step0 raw2821step0Labels = mixedMoment B raw2821step1 raw2821step1Labels := by
      have hz : ∀ j, raw2821step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2821step1 = (fun i j => raw2821step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2821step1 raw2821step0; decide +kernel
      have hl : raw2821step1Labels = raw2821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2821step0 raw2821step0Labels permutation104 hz
    mixedMoment B raw2821step1 raw2821step1Labels = mixedMoment B raw2821step2 raw2821step2Labels := by
      have hz : ∀ j, raw2821step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2821step2 = (fun i j => raw2821step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2821step2 raw2821step1; decide +kernel
      have hl : raw2821step2Labels = raw2821step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2821step1 raw2821step1Labels permutation20 hz
    mixedMoment B raw2821step2 raw2821step2Labels = mixedMoment B raw2821step3 raw2821step3Labels := by
      have ha : raw2821step3 = (fun i j => raw2821step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw2821step3 raw2821step2; decide +kernel
      have hl : raw2821step3Labels = raw2821step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2821step2 raw2821step2Labels permutation2 permutation7
    mixedMoment B raw2821step3 raw2821step3Labels = mixedMoment B raw2821step4 raw2821step4Labels := by
      have ha : raw2821step4 = raw2821step3 := by apply Matrix.ext; unfold raw2821step4 raw2821step3; decide +kernel
      have hl : raw2821step3Labels = labelEmbedding10 ∘ raw2821step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2821step3 raw2821step3Labels raw2821step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw2822 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2822step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2822step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2822step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2822 raw2822Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw2822 raw2822Labels = mixedMoment B raw2822step0 raw2822step0Labels := by
      have hz : ∀ j, raw2822 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2822step0 = (fun i j => raw2822 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2822step0 raw2822; decide +kernel
      have hl : raw2822step0Labels = raw2822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2822 raw2822Labels permutation434 hz
    mixedMoment B raw2822step0 raw2822step0Labels = mixedMoment B raw2822step1 raw2822step1Labels := by
      have hz : ∀ j, raw2822step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2822step1 = (fun i j => raw2822step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2822step1 raw2822step0; decide +kernel
      have hl : raw2822step1Labels = raw2822step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2822step0 raw2822step0Labels permutation80 hz
    mixedMoment B raw2822step1 raw2822step1Labels = mixedMoment B raw2822step2 raw2822step2Labels := by
      have ha : raw2822step2 = (fun i j => raw2822step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2822step2 raw2822step1; decide +kernel
      have hl : raw2822step2Labels = raw2822step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2822step1 raw2822step1Labels permutation29 permutation2
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw2823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2823step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2823step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2823step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2823step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2823step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2823 raw2823Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw2823 raw2823Labels = mixedMoment B raw2823step0 raw2823step0Labels := by
      have hz : ∀ j, raw2823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2823step0 = (fun i j => raw2823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2823step0 raw2823; decide +kernel
      have hl : raw2823step0Labels = raw2823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2823 raw2823Labels permutation434 hz
    mixedMoment B raw2823step0 raw2823step0Labels = mixedMoment B raw2823step1 raw2823step1Labels := by
      have hz : ∀ j, raw2823step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2823step1 = (fun i j => raw2823step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2823step1 raw2823step0; decide +kernel
      have hl : raw2823step1Labels = raw2823step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2823step0 raw2823step0Labels permutation56 hz
    mixedMoment B raw2823step1 raw2823step1Labels = mixedMoment B raw2823step2 raw2823step2Labels := by
      have ha : raw2823step2 = (fun i j => raw2823step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2823step2 raw2823step1; decide +kernel
      have hl : raw2823step2Labels = raw2823step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2823step1 raw2823step1Labels permutation8 permutation6
    mixedMoment B raw2823step2 raw2823step2Labels = mixedMoment B raw2823step3 raw2823step3Labels := by
      have ha : raw2823step3 = raw2823step2 := by apply Matrix.ext; unfold raw2823step3 raw2823step2; decide +kernel
      have hl : raw2823step2Labels = labelEmbedding9 ∘ raw2823step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2823step2 raw2823step2Labels raw2823step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw2824 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2824step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2824step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2824step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2824step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2824step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2824 raw2824Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw2824 raw2824Labels = mixedMoment B raw2824step0 raw2824step0Labels := by
      have hz : ∀ j, raw2824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2824step0 = (fun i j => raw2824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2824step0 raw2824; decide +kernel
      have hl : raw2824step0Labels = raw2824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2824 raw2824Labels permutation346 hz
    mixedMoment B raw2824step0 raw2824step0Labels = mixedMoment B raw2824step1 raw2824step1Labels := by
      have hz : ∀ j, raw2824step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2824step1 = (fun i j => raw2824step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2824step1 raw2824step0; decide +kernel
      have hl : raw2824step1Labels = raw2824step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2824step0 raw2824step0Labels permutation56 hz
    mixedMoment B raw2824step1 raw2824step1Labels = mixedMoment B raw2824step2 raw2824step2Labels := by
      have ha : raw2824step2 = (fun i j => raw2824step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2824step2 raw2824step1; decide +kernel
      have hl : raw2824step2Labels = raw2824step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2824step1 raw2824step1Labels permutation8 permutation6
    mixedMoment B raw2824step2 raw2824step2Labels = mixedMoment B raw2824step3 raw2824step3Labels := by
      have ha : raw2824step3 = raw2824step2 := by apply Matrix.ext; unfold raw2824step3 raw2824step2; decide +kernel
      have hl : raw2824step2Labels = labelEmbedding9 ∘ raw2824step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2824step2 raw2824step2Labels raw2824step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw2825 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2825step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, -1, 2]]
def raw2825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2825step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 1, -2], ![-1, -1, 2]]
def raw2825step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2825step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1]]
def raw2825step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2825step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -1, -1]]
def raw2825step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2825 raw2825Labels = mixedMoment B node5496 node5496Labels := by
  calc
    mixedMoment B raw2825 raw2825Labels = mixedMoment B raw2825step0 raw2825step0Labels := by
      have hz : ∀ j, raw2825 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2825step0 = (fun i j => raw2825 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2825step0 raw2825; decide +kernel
      have hl : raw2825step0Labels = raw2825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2825 raw2825Labels permutation520 hz
    mixedMoment B raw2825step0 raw2825step0Labels = mixedMoment B raw2825step1 raw2825step1Labels := by
      have hz : ∀ j, raw2825step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2825step1 = (fun i j => raw2825step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2825step1 raw2825step0; decide +kernel
      have hl : raw2825step1Labels = raw2825step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2825step0 raw2825step0Labels permutation104 hz
    mixedMoment B raw2825step1 raw2825step1Labels = mixedMoment B raw2825step2 raw2825step2Labels := by
      have hz : ∀ j, raw2825step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2825step2 = (fun i j => raw2825step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2825step2 raw2825step1; decide +kernel
      have hl : raw2825step2Labels = raw2825step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2825step1 raw2825step1Labels permutation20 hz
    mixedMoment B raw2825step2 raw2825step2Labels = mixedMoment B raw2825step3 raw2825step3Labels := by
      have hz : ∀ j, raw2825step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2825step3 = (fun i j => raw2825step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2825step3 raw2825step2; decide +kernel
      have hl : raw2825step3Labels = raw2825step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2825step2 raw2825step2Labels permutation4 hz
    mixedMoment B raw2825step3 raw2825step3Labels = mixedMoment B raw2825step4 raw2825step4Labels := by
      have ha : raw2825step4 = (fun i j => raw2825step3 (permutation0 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2825step4 raw2825step3; decide +kernel
      have hl : raw2825step4Labels = raw2825step3Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2825step3 raw2825step3Labels permutation0 permutation6
    mixedMoment B raw2825step4 raw2825step4Labels = mixedMoment B raw2825step5 raw2825step5Labels := by
      have ha : raw2825step5 = raw2825step4 := by apply Matrix.ext; unfold raw2825step5 raw2825step4; decide +kernel
      have hl : raw2825step4Labels = labelEmbedding9 ∘ raw2825step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2825step4 raw2825step4Labels raw2825step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5496 node5496Labels := by rfl

def raw2826 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2826step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2826step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2826step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2826step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2826 raw2826Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2826 raw2826Labels = mixedMoment B raw2826step0 raw2826step0Labels := by
      have hz : ∀ j, raw2826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2826step0 = (fun i j => raw2826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2826step0 raw2826; decide +kernel
      have hl : raw2826step0Labels = raw2826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2826 raw2826Labels permutation434 hz
    mixedMoment B raw2826step0 raw2826step0Labels = mixedMoment B raw2826step1 raw2826step1Labels := by
      have ha : raw2826step1 = (fun i j => raw2826step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2826step1 raw2826step0; decide +kernel
      have hl : raw2826step1Labels = raw2826step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2826step0 raw2826step0Labels permutation32 permutation4
    mixedMoment B raw2826step1 raw2826step1Labels = mixedMoment B raw2826step2 raw2826step2Labels := by
      have ha : raw2826step2 = -raw2826step1 := by apply Matrix.ext; change ∀ i j, raw2826step2 i j = -(raw2826step1 i j); unfold raw2826step2 raw2826step1; decide +kernel
      have hl : raw2826step2Labels = raw2826step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2826step2 raw2826step2Labels = mixedMoment B raw2826step3 raw2826step3Labels := by
      have ha : raw2826step3 = raw2826step2 := by apply Matrix.ext; unfold raw2826step3 raw2826step2; decide +kernel
      have hl : raw2826step2Labels = labelEmbedding7 ∘ raw2826step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2826step2 raw2826step2Labels raw2826step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2827 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2827step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2827step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2827 raw2827Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw2827 raw2827Labels = mixedMoment B raw2827step0 raw2827step0Labels := by
      have hz : ∀ j, raw2827 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2827step0 = (fun i j => raw2827 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2827step0 raw2827; decide +kernel
      have hl : raw2827step0Labels = raw2827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2827 raw2827Labels permutation434 hz
    mixedMoment B raw2827step0 raw2827step0Labels = mixedMoment B raw2827step1 raw2827step1Labels := by
      have ha : raw2827step1 = (fun i j => raw2827step0 (permutation74 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2827step1 raw2827step0; decide +kernel
      have hl : raw2827step1Labels = raw2827step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2827step0 raw2827step0Labels permutation74 permutation3
    mixedMoment B raw2827step1 raw2827step1Labels = mixedMoment B raw2827step2 raw2827step2Labels := by
      have ha : raw2827step2 = raw2827step1 := by apply Matrix.ext; unfold raw2827step2 raw2827step1; decide +kernel
      have hl : raw2827step1Labels = labelEmbedding6 ∘ raw2827step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2827step1 raw2827step1Labels raw2827step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw2828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2828step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2828 raw2828Labels = mixedMoment B node5488 node5488Labels := by
  calc
    mixedMoment B raw2828 raw2828Labels = mixedMoment B raw2828step0 raw2828step0Labels := by
      have ha : raw2828step0 = (fun i j => raw2828 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2828step0 raw2828; decide +kernel
      have hl : raw2828step0Labels = raw2828Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2828 raw2828Labels permutation158 permutation6
    mixedMoment B raw2828step0 raw2828step0Labels = mixedMoment B raw2828step1 raw2828step1Labels := by
      have ha : raw2828step1 = raw2828step0 := by apply Matrix.ext; unfold raw2828step1 raw2828step0; decide +kernel
      have hl : raw2828step0Labels = labelEmbedding9 ∘ raw2828step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2828step0 raw2828step0Labels raw2828step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5488 node5488Labels := by rfl

def raw2829 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2829step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2829step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2829step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2829step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2829step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2829 raw2829Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw2829 raw2829Labels = mixedMoment B raw2829step0 raw2829step0Labels := by
      have hz : ∀ j, raw2829 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2829step0 = (fun i j => raw2829 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2829step0 raw2829; decide +kernel
      have hl : raw2829step0Labels = raw2829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2829 raw2829Labels permutation520 hz
    mixedMoment B raw2829step0 raw2829step0Labels = mixedMoment B raw2829step1 raw2829step1Labels := by
      have hz : ∀ j, raw2829step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2829step1 = (fun i j => raw2829step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2829step1 raw2829step0; decide +kernel
      have hl : raw2829step1Labels = raw2829step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2829step0 raw2829step0Labels permutation104 hz
    mixedMoment B raw2829step1 raw2829step1Labels = mixedMoment B raw2829step2 raw2829step2Labels := by
      have ha : raw2829step2 = (fun i j => raw2829step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2829step2 raw2829step1; decide +kernel
      have hl : raw2829step2Labels = raw2829step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2829step1 raw2829step1Labels permutation8 permutation6
    mixedMoment B raw2829step2 raw2829step2Labels = mixedMoment B raw2829step3 raw2829step3Labels := by
      have ha : raw2829step3 = raw2829step2 := by apply Matrix.ext; unfold raw2829step3 raw2829step2; decide +kernel
      have hl : raw2829step2Labels = labelEmbedding9 ∘ raw2829step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2829step2 raw2829step2Labels raw2829step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw2830 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2830 raw2830Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2830 raw2830Labels = mixedMoment B raw2830step0 raw2830step0Labels := by
      have hz : ∀ j, raw2830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2830step0 = (fun i j => raw2830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2830step0 raw2830; decide +kernel
      have hl : raw2830step0Labels = raw2830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2830 raw2830Labels permutation434 hz
    mixedMoment B raw2830step0 raw2830step0Labels = mixedMoment B raw2830step1 raw2830step1Labels := by
      have ha : raw2830step1 = (fun i j => raw2830step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2830step1 raw2830step0; decide +kernel
      have hl : raw2830step1Labels = raw2830step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2830step0 raw2830step0Labels permutation137 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2831 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2831step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2831 raw2831Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw2831 raw2831Labels = mixedMoment B raw2831step0 raw2831step0Labels := by
      have hz : ∀ j, raw2831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2831step0 = (fun i j => raw2831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2831step0 raw2831; decide +kernel
      have hl : raw2831step0Labels = raw2831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2831 raw2831Labels permutation346 hz
    mixedMoment B raw2831step0 raw2831step0Labels = mixedMoment B raw2831step1 raw2831step1Labels := by
      have ha : raw2831step1 = (fun i j => raw2831step0 (permutation74 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2831step1 raw2831step0; decide +kernel
      have hl : raw2831step1Labels = raw2831step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2831step0 raw2831step0Labels permutation74 permutation3
    mixedMoment B raw2831step1 raw2831step1Labels = mixedMoment B raw2831step2 raw2831step2Labels := by
      have ha : raw2831step2 = raw2831step1 := by apply Matrix.ext; unfold raw2831step2 raw2831step1; decide +kernel
      have hl : raw2831step1Labels = labelEmbedding6 ∘ raw2831step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2831step1 raw2831step1Labels raw2831step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw2832 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2832step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2832 raw2832Labels = mixedMoment B node5488 node5488Labels := by
  calc
    mixedMoment B raw2832 raw2832Labels = mixedMoment B raw2832step0 raw2832step0Labels := by
      have ha : raw2832step0 = (fun i j => raw2832 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2832step0 raw2832; decide +kernel
      have hl : raw2832step0Labels = raw2832Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2832 raw2832Labels permutation152 permutation6
    mixedMoment B raw2832step0 raw2832step0Labels = mixedMoment B raw2832step1 raw2832step1Labels := by
      have ha : raw2832step1 = raw2832step0 := by apply Matrix.ext; unfold raw2832step1 raw2832step0; decide +kernel
      have hl : raw2832step0Labels = labelEmbedding9 ∘ raw2832step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2832step0 raw2832step0Labels raw2832step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5488 node5488Labels := by rfl

def raw2833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2833step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2833step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2833step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2833step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2833 raw2833Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw2833 raw2833Labels = mixedMoment B raw2833step0 raw2833step0Labels := by
      have hz : ∀ j, raw2833 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2833step0 = (fun i j => raw2833 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2833step0 raw2833; decide +kernel
      have hl : raw2833step0Labels = raw2833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2833 raw2833Labels permutation520 hz
    mixedMoment B raw2833step0 raw2833step0Labels = mixedMoment B raw2833step1 raw2833step1Labels := by
      have hz : ∀ j, raw2833step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2833step1 = (fun i j => raw2833step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2833step1 raw2833step0; decide +kernel
      have hl : raw2833step1Labels = raw2833step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2833step0 raw2833step0Labels permutation80 hz
    mixedMoment B raw2833step1 raw2833step1Labels = mixedMoment B raw2833step2 raw2833step2Labels := by
      have ha : raw2833step2 = (fun i j => raw2833step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2833step2 raw2833step1; decide +kernel
      have hl : raw2833step2Labels = raw2833step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2833step1 raw2833step1Labels permutation8 permutation6
    mixedMoment B raw2833step2 raw2833step2Labels = mixedMoment B raw2833step3 raw2833step3Labels := by
      have ha : raw2833step3 = raw2833step2 := by apply Matrix.ext; unfold raw2833step3 raw2833step2; decide +kernel
      have hl : raw2833step2Labels = labelEmbedding9 ∘ raw2833step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2833step2 raw2833step2Labels raw2833step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw2834 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2834step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2834step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2834step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2834step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2834step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2834step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2834step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2834 raw2834Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2834 raw2834Labels = mixedMoment B raw2834step0 raw2834step0Labels := by
      have hz : ∀ j, raw2834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2834step0 = (fun i j => raw2834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2834step0 raw2834; decide +kernel
      have hl : raw2834step0Labels = raw2834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2834 raw2834Labels permutation434 hz
    mixedMoment B raw2834step0 raw2834step0Labels = mixedMoment B raw2834step1 raw2834step1Labels := by
      have hz : ∀ j, raw2834step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2834step1 = (fun i j => raw2834step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2834step1 raw2834step0; decide +kernel
      have hl : raw2834step1Labels = raw2834step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2834step0 raw2834step0Labels permutation80 hz
    mixedMoment B raw2834step1 raw2834step1Labels = mixedMoment B raw2834step2 raw2834step2Labels := by
      have ha : raw2834step2 = (fun i j => raw2834step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2834step2 raw2834step1; decide +kernel
      have hl : raw2834step2Labels = raw2834step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2834step1 raw2834step1Labels permutation9 permutation4
    mixedMoment B raw2834step2 raw2834step2Labels = mixedMoment B raw2834step3 raw2834step3Labels := by
      have ha : raw2834step3 = -raw2834step2 := by apply Matrix.ext; change ∀ i j, raw2834step3 i j = -(raw2834step2 i j); unfold raw2834step3 raw2834step2; decide +kernel
      have hl : raw2834step3Labels = raw2834step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2834step3 raw2834step3Labels = mixedMoment B raw2834step4 raw2834step4Labels := by
      have ha : raw2834step4 = raw2834step3 := by apply Matrix.ext; unfold raw2834step4 raw2834step3; decide +kernel
      have hl : raw2834step3Labels = labelEmbedding7 ∘ raw2834step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2834step3 raw2834step3Labels raw2834step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2835step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2835step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2835step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2835 raw2835Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw2835 raw2835Labels = mixedMoment B raw2835step0 raw2835step0Labels := by
      have hz : ∀ j, raw2835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2835step0 = (fun i j => raw2835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2835step0 raw2835; decide +kernel
      have hl : raw2835step0Labels = raw2835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2835 raw2835Labels permutation434 hz
    mixedMoment B raw2835step0 raw2835step0Labels = mixedMoment B raw2835step1 raw2835step1Labels := by
      have hz : ∀ j, raw2835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2835step1 = (fun i j => raw2835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2835step1 raw2835step0; decide +kernel
      have hl : raw2835step1Labels = raw2835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2835step0 raw2835step0Labels permutation80 hz
    mixedMoment B raw2835step1 raw2835step1Labels = mixedMoment B raw2835step2 raw2835step2Labels := by
      have ha : raw2835step2 = (fun i j => raw2835step1 (permutation18 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2835step2 raw2835step1; decide +kernel
      have hl : raw2835step2Labels = raw2835step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2835step1 raw2835step1Labels permutation18 permutation3
    mixedMoment B raw2835step2 raw2835step2Labels = mixedMoment B raw2835step3 raw2835step3Labels := by
      have ha : raw2835step3 = raw2835step2 := by apply Matrix.ext; unfold raw2835step3 raw2835step2; decide +kernel
      have hl : raw2835step2Labels = labelEmbedding6 ∘ raw2835step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2835step2 raw2835step2Labels raw2835step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

def raw2836 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2836step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2836step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2836step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2836step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2836 raw2836Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw2836 raw2836Labels = mixedMoment B raw2836step0 raw2836step0Labels := by
      have hz : ∀ j, raw2836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2836step0 = (fun i j => raw2836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2836step0 raw2836; decide +kernel
      have hl : raw2836step0Labels = raw2836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2836 raw2836Labels permutation434 hz
    mixedMoment B raw2836step0 raw2836step0Labels = mixedMoment B raw2836step1 raw2836step1Labels := by
      have ha : raw2836step1 = (fun i j => raw2836step0 (permutation108 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2836step1 raw2836step0; decide +kernel
      have hl : raw2836step1Labels = raw2836step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2836step0 raw2836step0Labels permutation108 permutation3
    mixedMoment B raw2836step1 raw2836step1Labels = mixedMoment B raw2836step2 raw2836step2Labels := by
      have ha : raw2836step2 = -raw2836step1 := by apply Matrix.ext; change ∀ i j, raw2836step2 i j = -(raw2836step1 i j); unfold raw2836step2 raw2836step1; decide +kernel
      have hl : raw2836step2Labels = raw2836step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2836step2 raw2836step2Labels = mixedMoment B raw2836step3 raw2836step3Labels := by
      have ha : raw2836step3 = raw2836step2 := by apply Matrix.ext; unfold raw2836step3 raw2836step2; decide +kernel
      have hl : raw2836step2Labels = labelEmbedding6 ∘ raw2836step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2836step2 raw2836step2Labels raw2836step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw2837 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2]]
def raw2837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2837step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2837step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2837step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2837step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2837 raw2837Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw2837 raw2837Labels = mixedMoment B raw2837step0 raw2837step0Labels := by
      have hz : ∀ j, raw2837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2837step0 = (fun i j => raw2837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2837step0 raw2837; decide +kernel
      have hl : raw2837step0Labels = raw2837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2837 raw2837Labels permutation346 hz
    mixedMoment B raw2837step0 raw2837step0Labels = mixedMoment B raw2837step1 raw2837step1Labels := by
      have ha : raw2837step1 = (fun i j => raw2837step0 (permutation108 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2837step1 raw2837step0; decide +kernel
      have hl : raw2837step1Labels = raw2837step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2837step0 raw2837step0Labels permutation108 permutation3
    mixedMoment B raw2837step1 raw2837step1Labels = mixedMoment B raw2837step2 raw2837step2Labels := by
      have ha : raw2837step2 = -raw2837step1 := by apply Matrix.ext; change ∀ i j, raw2837step2 i j = -(raw2837step1 i j); unfold raw2837step2 raw2837step1; decide +kernel
      have hl : raw2837step2Labels = raw2837step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2837step2 raw2837step2Labels = mixedMoment B raw2837step3 raw2837step3Labels := by
      have ha : raw2837step3 = raw2837step2 := by apply Matrix.ext; unfold raw2837step3 raw2837step2; decide +kernel
      have hl : raw2837step2Labels = labelEmbedding6 ∘ raw2837step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2837step2 raw2837step2Labels raw2837step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw2838 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2838step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2838 raw2838Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2838 raw2838Labels = mixedMoment B raw2838step0 raw2838step0Labels := by
      have hz : ∀ j, raw2838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2838step0 = (fun i j => raw2838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2838step0 raw2838; decide +kernel
      have hl : raw2838step0Labels = raw2838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2838 raw2838Labels permutation434 hz
    mixedMoment B raw2838step0 raw2838step0Labels = mixedMoment B raw2838step1 raw2838step1Labels := by
      have hz : ∀ j, raw2838step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2838step1 = (fun i j => raw2838step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2838step1 raw2838step0; decide +kernel
      have hl : raw2838step1Labels = raw2838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2838step0 raw2838step0Labels permutation80 hz
    mixedMoment B raw2838step1 raw2838step1Labels = mixedMoment B raw2838step2 raw2838step2Labels := by
      have ha : raw2838step2 = (fun i j => raw2838step1 (permutation28 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2838step2 raw2838step1; decide +kernel
      have hl : raw2838step2Labels = raw2838step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2838step1 raw2838step1Labels permutation28 permutation2
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2839 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2839step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2839step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2839step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2839step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2839step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2839step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2839 raw2839Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw2839 raw2839Labels = mixedMoment B raw2839step0 raw2839step0Labels := by
      have hz : ∀ j, raw2839 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2839step0 = (fun i j => raw2839 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2839step0 raw2839; decide +kernel
      have hl : raw2839step0Labels = raw2839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2839 raw2839Labels permutation434 hz
    mixedMoment B raw2839step0 raw2839step0Labels = mixedMoment B raw2839step1 raw2839step1Labels := by
      have hz : ∀ j, raw2839step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2839step1 = (fun i j => raw2839step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2839step1 raw2839step0; decide +kernel
      have hl : raw2839step1Labels = raw2839step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2839step0 raw2839step0Labels permutation80 hz
    mixedMoment B raw2839step1 raw2839step1Labels = mixedMoment B raw2839step2 raw2839step2Labels := by
      have ha : raw2839step2 = (fun i j => raw2839step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2839step2 raw2839step1; decide +kernel
      have hl : raw2839step2Labels = raw2839step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2839step1 raw2839step1Labels permutation31 permutation4
    mixedMoment B raw2839step2 raw2839step2Labels = mixedMoment B raw2839step3 raw2839step3Labels := by
      have ha : raw2839step3 = raw2839step2 := by apply Matrix.ext; unfold raw2839step3 raw2839step2; decide +kernel
      have hl : raw2839step2Labels = labelEmbedding7 ∘ raw2839step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2839step2 raw2839step2Labels raw2839step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw2840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2840step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2840step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2840step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2840step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2840 raw2840Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2840 raw2840Labels = mixedMoment B raw2840step0 raw2840step0Labels := by
      have hz : ∀ j, raw2840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2840step0 = (fun i j => raw2840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2840step0 raw2840; decide +kernel
      have hl : raw2840step0Labels = raw2840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2840 raw2840Labels permutation434 hz
    mixedMoment B raw2840step0 raw2840step0Labels = mixedMoment B raw2840step1 raw2840step1Labels := by
      have hz : ∀ j, raw2840step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2840step1 = (fun i j => raw2840step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2840step1 raw2840step0; decide +kernel
      have hl : raw2840step1Labels = raw2840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2840step0 raw2840step0Labels permutation80 hz
    mixedMoment B raw2840step1 raw2840step1Labels = mixedMoment B raw2840step2 raw2840step2Labels := by
      have ha : raw2840step2 = (fun i j => raw2840step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2840step2 raw2840step1; decide +kernel
      have hl : raw2840step2Labels = raw2840step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2840step1 raw2840step1Labels permutation30 permutation4
    mixedMoment B raw2840step2 raw2840step2Labels = mixedMoment B raw2840step3 raw2840step3Labels := by
      have ha : raw2840step3 = raw2840step2 := by apply Matrix.ext; unfold raw2840step3 raw2840step2; decide +kernel
      have hl : raw2840step2Labels = labelEmbedding7 ∘ raw2840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2840step2 raw2840step2Labels raw2840step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2841 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2841step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2841step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2841 raw2841Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2841 raw2841Labels = mixedMoment B raw2841step0 raw2841step0Labels := by
      have hz : ∀ j, raw2841 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2841step0 = (fun i j => raw2841 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2841step0 raw2841; decide +kernel
      have hl : raw2841step0Labels = raw2841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2841 raw2841Labels permutation434 hz
    mixedMoment B raw2841step0 raw2841step0Labels = mixedMoment B raw2841step1 raw2841step1Labels := by
      have ha : raw2841step1 = (fun i j => raw2841step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2841step1 raw2841step0; decide +kernel
      have hl : raw2841step1Labels = raw2841step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2841step0 raw2841step0Labels permutation149 permutation4
    mixedMoment B raw2841step1 raw2841step1Labels = mixedMoment B raw2841step2 raw2841step2Labels := by
      have ha : raw2841step2 = raw2841step1 := by apply Matrix.ext; unfold raw2841step2 raw2841step1; decide +kernel
      have hl : raw2841step1Labels = labelEmbedding7 ∘ raw2841step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2841step1 raw2841step1Labels raw2841step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2]]
def raw2842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2842step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2842step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2842 raw2842Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2842 raw2842Labels = mixedMoment B raw2842step0 raw2842step0Labels := by
      have hz : ∀ j, raw2842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2842step0 = (fun i j => raw2842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2842step0 raw2842; decide +kernel
      have hl : raw2842step0Labels = raw2842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2842 raw2842Labels permutation346 hz
    mixedMoment B raw2842step0 raw2842step0Labels = mixedMoment B raw2842step1 raw2842step1Labels := by
      have ha : raw2842step1 = (fun i j => raw2842step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2842step1 raw2842step0; decide +kernel
      have hl : raw2842step1Labels = raw2842step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2842step0 raw2842step0Labels permutation149 permutation4
    mixedMoment B raw2842step1 raw2842step1Labels = mixedMoment B raw2842step2 raw2842step2Labels := by
      have ha : raw2842step2 = raw2842step1 := by apply Matrix.ext; unfold raw2842step2 raw2842step1; decide +kernel
      have hl : raw2842step1Labels = labelEmbedding7 ∘ raw2842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2842step1 raw2842step1Labels raw2842step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2843step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2843step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -2, 2]]
def raw2843step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2843step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2843step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2843step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2843step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2843step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2843step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2843 raw2843Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2843 raw2843Labels = mixedMoment B raw2843step0 raw2843step0Labels := by
      have hz : ∀ j, raw2843 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2843step0 = (fun i j => raw2843 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2843step0 raw2843; decide +kernel
      have hl : raw2843step0Labels = raw2843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2843 raw2843Labels permutation520 hz
    mixedMoment B raw2843step0 raw2843step0Labels = mixedMoment B raw2843step1 raw2843step1Labels := by
      have hz : ∀ j, raw2843step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2843step1 = (fun i j => raw2843step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2843step1 raw2843step0; decide +kernel
      have hl : raw2843step1Labels = raw2843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2843step0 raw2843step0Labels permutation104 hz
    mixedMoment B raw2843step1 raw2843step1Labels = mixedMoment B raw2843step2 raw2843step2Labels := by
      have hz : ∀ j, raw2843step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2843step2 = (fun i j => raw2843step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2843step2 raw2843step1; decide +kernel
      have hl : raw2843step2Labels = raw2843step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2843step1 raw2843step1Labels permutation20 hz
    mixedMoment B raw2843step2 raw2843step2Labels = mixedMoment B raw2843step3 raw2843step3Labels := by
      have ha : raw2843step3 = (fun i j => raw2843step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2843step3 raw2843step2; decide +kernel
      have hl : raw2843step3Labels = raw2843step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2843step2 raw2843step2Labels permutation7 permutation6
    mixedMoment B raw2843step3 raw2843step3Labels = mixedMoment B raw2843step4 raw2843step4Labels := by
      have ha : raw2843step4 = -raw2843step3 := by apply Matrix.ext; change ∀ i j, raw2843step4 i j = -(raw2843step3 i j); unfold raw2843step4 raw2843step3; decide +kernel
      have hl : raw2843step4Labels = raw2843step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2843step4 raw2843step4Labels = mixedMoment B raw2843step5 raw2843step5Labels := by
      have ha : raw2843step5 = raw2843step4 := by apply Matrix.ext; unfold raw2843step5 raw2843step4; decide +kernel
      have hl : raw2843step4Labels = labelEmbedding9 ∘ raw2843step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2843step4 raw2843step4Labels raw2843step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw2844 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2844Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2844step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2844step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2844step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2844 raw2844Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw2844 raw2844Labels = mixedMoment B raw2844step0 raw2844step0Labels := by
      have hz : ∀ j, raw2844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2844step0 = (fun i j => raw2844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2844step0 raw2844; decide +kernel
      have hl : raw2844step0Labels = raw2844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2844 raw2844Labels permutation434 hz
    mixedMoment B raw2844step0 raw2844step0Labels = mixedMoment B raw2844step1 raw2844step1Labels := by
      have ha : raw2844step1 = (fun i j => raw2844step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2844step1 raw2844step0; decide +kernel
      have hl : raw2844step1Labels = raw2844step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2844step0 raw2844step0Labels permutation32 permutation4
    mixedMoment B raw2844step1 raw2844step1Labels = mixedMoment B raw2844step2 raw2844step2Labels := by
      have ha : raw2844step2 = -raw2844step1 := by apply Matrix.ext; change ∀ i j, raw2844step2 i j = -(raw2844step1 i j); unfold raw2844step2 raw2844step1; decide +kernel
      have hl : raw2844step2Labels = raw2844step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node494 node494Labels := by rfl

def raw2845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2845Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2845step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2845step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2845 raw2845Labels = mixedMoment B node500 node500Labels := by
  calc
    mixedMoment B raw2845 raw2845Labels = mixedMoment B raw2845step0 raw2845step0Labels := by
      have hz : ∀ j, raw2845 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2845step0 = (fun i j => raw2845 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2845step0 raw2845; decide +kernel
      have hl : raw2845step0Labels = raw2845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2845 raw2845Labels permutation434 hz
    mixedMoment B raw2845step0 raw2845step0Labels = mixedMoment B raw2845step1 raw2845step1Labels := by
      have ha : raw2845step1 = (fun i j => raw2845step0 (permutation74 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2845step1 raw2845step0; decide +kernel
      have hl : raw2845step1Labels = raw2845step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2845step0 raw2845step0Labels permutation74 permutation3
    _ = mixedMoment B node500 node500Labels := by rfl

def raw2846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2846Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2846step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2846step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2846step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2846 raw2846Labels = mixedMoment B node527 node527Labels := by
  calc
    mixedMoment B raw2846 raw2846Labels = mixedMoment B raw2846step0 raw2846step0Labels := by
      have hz : ∀ j, raw2846 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2846step0 = (fun i j => raw2846 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2846step0 raw2846; decide +kernel
      have hl : raw2846step0Labels = raw2846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2846 raw2846Labels permutation434 hz
    mixedMoment B raw2846step0 raw2846step0Labels = mixedMoment B raw2846step1 raw2846step1Labels := by
      have hz : ∀ j, raw2846step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2846step1 = (fun i j => raw2846step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2846step1 raw2846step0; decide +kernel
      have hl : raw2846step1Labels = raw2846step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2846step0 raw2846step0Labels permutation80 hz
    mixedMoment B raw2846step1 raw2846step1Labels = mixedMoment B raw2846step2 raw2846step2Labels := by
      have ha : raw2846step2 = (fun i j => raw2846step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2846step2 raw2846step1; decide +kernel
      have hl : raw2846step2Labels = raw2846step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2846step1 raw2846step1Labels permutation8 permutation6
    _ = mixedMoment B node527 node527Labels := by rfl

def raw2847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2847Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2847step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2847 raw2847Labels = mixedMoment B node524 node524Labels := by
  calc
    mixedMoment B raw2847 raw2847Labels = mixedMoment B raw2847step0 raw2847step0Labels := by
      have ha : raw2847step0 = (fun i j => raw2847 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2847step0 raw2847; decide +kernel
      have hl : raw2847step0Labels = raw2847Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2847 raw2847Labels permutation158 permutation6
    _ = mixedMoment B node524 node524Labels := by rfl

def raw2848 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2848Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2848step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2848step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2848step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2848step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2848step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2848 raw2848Labels = mixedMoment B node527 node527Labels := by
  calc
    mixedMoment B raw2848 raw2848Labels = mixedMoment B raw2848step0 raw2848step0Labels := by
      have hz : ∀ j, raw2848 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2848step0 = (fun i j => raw2848 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2848step0 raw2848; decide +kernel
      have hl : raw2848step0Labels = raw2848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2848 raw2848Labels permutation520 hz
    mixedMoment B raw2848step0 raw2848step0Labels = mixedMoment B raw2848step1 raw2848step1Labels := by
      have hz : ∀ j, raw2848step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2848step1 = (fun i j => raw2848step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2848step1 raw2848step0; decide +kernel
      have hl : raw2848step1Labels = raw2848step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2848step0 raw2848step0Labels permutation104 hz
    mixedMoment B raw2848step1 raw2848step1Labels = mixedMoment B raw2848step2 raw2848step2Labels := by
      have ha : raw2848step2 = (fun i j => raw2848step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2848step2 raw2848step1; decide +kernel
      have hl : raw2848step2Labels = raw2848step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2848step1 raw2848step1Labels permutation8 permutation6
    _ = mixedMoment B node527 node527Labels := by rfl

def raw2849 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2849Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2849step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2849step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2849 raw2849Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw2849 raw2849Labels = mixedMoment B raw2849step0 raw2849step0Labels := by
      have hz : ∀ j, raw2849 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2849step0 = (fun i j => raw2849 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2849step0 raw2849; decide +kernel
      have hl : raw2849step0Labels = raw2849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2849 raw2849Labels permutation434 hz
    mixedMoment B raw2849step0 raw2849step0Labels = mixedMoment B raw2849step1 raw2849step1Labels := by
      have ha : raw2849step1 = (fun i j => raw2849step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2849step1 raw2849step0; decide +kernel
      have hl : raw2849step1Labels = raw2849step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2849step0 raw2849step0Labels permutation137 permutation2
    _ = mixedMoment B node494 node494Labels := by rfl

def raw2850 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![0, 0], ![0, 0], ![-2, 2]]
def raw2850Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2850step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![0, 0], ![-2, 2]]
def raw2850step0Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2850step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![0, 0], ![-2, 2]]
def raw2850step1Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2850step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![0, 0], ![-2, 2]]
def raw2850step2Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2850step3 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]
def raw2850step3Labels : Fin 2 → Fin 1 := ![0, 0]

def raw2850step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw2850step4Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical2850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2850 raw2850Labels = mixedMoment B node6 node6Labels := by
  calc
    mixedMoment B raw2850 raw2850Labels = mixedMoment B raw2850step0 raw2850step0Labels := by
      have hz : ∀ j, raw2850 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2850step0 = (fun i j => raw2850 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2850step0 raw2850; decide +kernel
      have hl : raw2850step0Labels = raw2850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2850 raw2850Labels permutation520 hz
    mixedMoment B raw2850step0 raw2850step0Labels = mixedMoment B raw2850step1 raw2850step1Labels := by
      have hz : ∀ j, raw2850step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2850step1 = (fun i j => raw2850step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2850step1 raw2850step0; decide +kernel
      have hl : raw2850step1Labels = raw2850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2850step0 raw2850step0Labels permutation104 hz
    mixedMoment B raw2850step1 raw2850step1Labels = mixedMoment B raw2850step2 raw2850step2Labels := by
      have hz : ∀ j, raw2850step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2850step2 = (fun i j => raw2850step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2850step2 raw2850step1; decide +kernel
      have hl : raw2850step2Labels = raw2850step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2850step1 raw2850step1Labels permutation20 hz
    mixedMoment B raw2850step2 raw2850step2Labels = mixedMoment B raw2850step3 raw2850step3Labels := by
      have hz : ∀ j, raw2850step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2850step3 = (fun i j => raw2850step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2850step3 raw2850step2; decide +kernel
      have hl : raw2850step3Labels = raw2850step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2850step2 raw2850step2Labels permutation4 hz
    mixedMoment B raw2850step3 raw2850step3Labels = mixedMoment B raw2850step4 raw2850step4Labels := by
      have ha : raw2850step4 = (fun i j => raw2850step3 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2850step4 raw2850step3; decide +kernel
      have hl : raw2850step4Labels = raw2850step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2850step3 raw2850step3Labels permutation1 permutation0
    _ = mixedMoment B node6 node6Labels := by rfl

def raw2851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2851step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2851step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2851 raw2851Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw2851 raw2851Labels = mixedMoment B raw2851step0 raw2851step0Labels := by
      have hz : ∀ j, raw2851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2851step0 = (fun i j => raw2851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2851step0 raw2851; decide +kernel
      have hl : raw2851step0Labels = raw2851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2851 raw2851Labels permutation434 hz
    mixedMoment B raw2851step0 raw2851step0Labels = mixedMoment B raw2851step1 raw2851step1Labels := by
      have hz : ∀ j, raw2851step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2851step1 = (fun i j => raw2851step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2851step1 raw2851step0; decide +kernel
      have hl : raw2851step1Labels = raw2851step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2851step0 raw2851step0Labels permutation80 hz
    mixedMoment B raw2851step1 raw2851step1Labels = mixedMoment B raw2851step2 raw2851step2Labels := by
      have ha : raw2851step2 = (fun i j => raw2851step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2851step2 raw2851step1; decide +kernel
      have hl : raw2851step2Labels = raw2851step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2851step1 raw2851step1Labels permutation31 permutation2
    mixedMoment B raw2851step2 raw2851step2Labels = mixedMoment B raw2851step3 raw2851step3Labels := by
      have ha : raw2851step3 = -raw2851step2 := by apply Matrix.ext; change ∀ i j, raw2851step3 i j = -(raw2851step2 i j); unfold raw2851step3 raw2851step2; decide +kernel
      have hl : raw2851step3Labels = raw2851step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw2852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2852step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2852step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2852step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2852step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2852 raw2852Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw2852 raw2852Labels = mixedMoment B raw2852step0 raw2852step0Labels := by
      have hz : ∀ j, raw2852 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2852step0 = (fun i j => raw2852 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2852step0 raw2852; decide +kernel
      have hl : raw2852step0Labels = raw2852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2852 raw2852Labels permutation434 hz
    mixedMoment B raw2852step0 raw2852step0Labels = mixedMoment B raw2852step1 raw2852step1Labels := by
      have hz : ∀ j, raw2852step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2852step1 = (fun i j => raw2852step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2852step1 raw2852step0; decide +kernel
      have hl : raw2852step1Labels = raw2852step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2852step0 raw2852step0Labels permutation56 hz
    mixedMoment B raw2852step1 raw2852step1Labels = mixedMoment B raw2852step2 raw2852step2Labels := by
      have ha : raw2852step2 = (fun i j => raw2852step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2852step2 raw2852step1; decide +kernel
      have hl : raw2852step2Labels = raw2852step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2852step1 raw2852step1Labels permutation31 permutation2
    mixedMoment B raw2852step2 raw2852step2Labels = mixedMoment B raw2852step3 raw2852step3Labels := by
      have ha : raw2852step3 = -raw2852step2 := by apply Matrix.ext; change ∀ i j, raw2852step3 i j = -(raw2852step2 i j); unfold raw2852step3 raw2852step2; decide +kernel
      have hl : raw2852step3Labels = raw2852step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw2853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2853step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2853step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2853step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2853step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2853step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2853 raw2853Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw2853 raw2853Labels = mixedMoment B raw2853step0 raw2853step0Labels := by
      have hz : ∀ j, raw2853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2853step0 = (fun i j => raw2853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2853step0 raw2853; decide +kernel
      have hl : raw2853step0Labels = raw2853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2853 raw2853Labels permutation346 hz
    mixedMoment B raw2853step0 raw2853step0Labels = mixedMoment B raw2853step1 raw2853step1Labels := by
      have hz : ∀ j, raw2853step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2853step1 = (fun i j => raw2853step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2853step1 raw2853step0; decide +kernel
      have hl : raw2853step1Labels = raw2853step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2853step0 raw2853step0Labels permutation56 hz
    mixedMoment B raw2853step1 raw2853step1Labels = mixedMoment B raw2853step2 raw2853step2Labels := by
      have ha : raw2853step2 = (fun i j => raw2853step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2853step2 raw2853step1; decide +kernel
      have hl : raw2853step2Labels = raw2853step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2853step1 raw2853step1Labels permutation31 permutation2
    mixedMoment B raw2853step2 raw2853step2Labels = mixedMoment B raw2853step3 raw2853step3Labels := by
      have ha : raw2853step3 = -raw2853step2 := by apply Matrix.ext; change ∀ i j, raw2853step3 i j = -(raw2853step2 i j); unfold raw2853step3 raw2853step2; decide +kernel
      have hl : raw2853step3Labels = raw2853step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw2854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2854step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2854step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2854step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2]]
def raw2854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2854step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2854step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw2854step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2854step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw2854step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2854step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw2854step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2854step6Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2854 raw2854Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2854 raw2854Labels = mixedMoment B raw2854step0 raw2854step0Labels := by
      have hz : ∀ j, raw2854 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2854step0 = (fun i j => raw2854 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2854step0 raw2854; decide +kernel
      have hl : raw2854step0Labels = raw2854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2854 raw2854Labels permutation434 hz
    mixedMoment B raw2854step0 raw2854step0Labels = mixedMoment B raw2854step1 raw2854step1Labels := by
      have hz : ∀ j, raw2854step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2854step1 = (fun i j => raw2854step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2854step1 raw2854step0; decide +kernel
      have hl : raw2854step1Labels = raw2854step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2854step0 raw2854step0Labels permutation80 hz
    mixedMoment B raw2854step1 raw2854step1Labels = mixedMoment B raw2854step2 raw2854step2Labels := by
      have hz : ∀ j, raw2854step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2854step2 = (fun i j => raw2854step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2854step2 raw2854step1; decide +kernel
      have hl : raw2854step2Labels = raw2854step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2854step1 raw2854step1Labels permutation14 hz
    mixedMoment B raw2854step2 raw2854step2Labels = mixedMoment B raw2854step3 raw2854step3Labels := by
      have hz : ∀ i, raw2854step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw2854step3 = (fun i j => raw2854step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw2854step3 raw2854step2; decide +kernel
      have hl : raw2854step3Labels = (fun j => raw2854step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2854step2 raw2854step2Labels permutation4 hz
    mixedMoment B raw2854step3 raw2854step3Labels = mixedMoment B raw2854step4 raw2854step4Labels := by
      have ha : raw2854step4 = (fun i j => raw2854step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2854step4 raw2854step3; decide +kernel
      have hl : raw2854step4Labels = raw2854step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2854step3 raw2854step3Labels permutation6 permutation0
    mixedMoment B raw2854step4 raw2854step4Labels = mixedMoment B raw2854step5 raw2854step5Labels := by
      have ha : raw2854step5 = -raw2854step4 := by apply Matrix.ext; change ∀ i j, raw2854step5 i j = -(raw2854step4 i j); unfold raw2854step5 raw2854step4; decide +kernel
      have hl : raw2854step5Labels = raw2854step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2854step5 raw2854step5Labels = mixedMoment B raw2854step6 raw2854step6Labels := by
      have ha : raw2854step6 = raw2854step5 := by apply Matrix.ext; unfold raw2854step6 raw2854step5; decide +kernel
      have hl : raw2854step5Labels = labelEmbedding2 ∘ raw2854step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2854step5 raw2854step5Labels raw2854step6Labels labelEmbedding2 hl
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw2855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 1, -2]]
def raw2855step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2855step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2855step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2855step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2855step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2855 raw2855Labels = mixedMoment B node5495 node5495Labels := by
  calc
    mixedMoment B raw2855 raw2855Labels = mixedMoment B raw2855step0 raw2855step0Labels := by
      have hz : ∀ j, raw2855 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2855step0 = (fun i j => raw2855 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2855step0 raw2855; decide +kernel
      have hl : raw2855step0Labels = raw2855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2855 raw2855Labels permutation434 hz
    mixedMoment B raw2855step0 raw2855step0Labels = mixedMoment B raw2855step1 raw2855step1Labels := by
      have hz : ∀ j, raw2855step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2855step1 = (fun i j => raw2855step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2855step1 raw2855step0; decide +kernel
      have hl : raw2855step1Labels = raw2855step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2855step0 raw2855step0Labels permutation80 hz
    mixedMoment B raw2855step1 raw2855step1Labels = mixedMoment B raw2855step2 raw2855step2Labels := by
      have hz : ∀ j, raw2855step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2855step2 = (fun i j => raw2855step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2855step2 raw2855step1; decide +kernel
      have hl : raw2855step2Labels = raw2855step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2855step1 raw2855step1Labels permutation14 hz
    mixedMoment B raw2855step2 raw2855step2Labels = mixedMoment B raw2855step3 raw2855step3Labels := by
      have ha : raw2855step3 = (fun i j => raw2855step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2855step3 raw2855step2; decide +kernel
      have hl : raw2855step3Labels = raw2855step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2855step2 raw2855step2Labels permutation6 permutation6
    mixedMoment B raw2855step3 raw2855step3Labels = mixedMoment B raw2855step4 raw2855step4Labels := by
      have ha : raw2855step4 = raw2855step3 := by apply Matrix.ext; unfold raw2855step4 raw2855step3; decide +kernel
      have hl : raw2855step3Labels = labelEmbedding9 ∘ raw2855step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2855step3 raw2855step3Labels raw2855step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5495 node5495Labels := by rfl

def raw2856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2856step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2856step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2856step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2856step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2856step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2856 raw2856Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2856 raw2856Labels = mixedMoment B raw2856step0 raw2856step0Labels := by
      have hz : ∀ j, raw2856 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2856step0 = (fun i j => raw2856 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2856step0 raw2856; decide +kernel
      have hl : raw2856step0Labels = raw2856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2856 raw2856Labels permutation434 hz
    mixedMoment B raw2856step0 raw2856step0Labels = mixedMoment B raw2856step1 raw2856step1Labels := by
      have hz : ∀ j, raw2856step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2856step1 = (fun i j => raw2856step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2856step1 raw2856step0; decide +kernel
      have hl : raw2856step1Labels = raw2856step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2856step0 raw2856step0Labels permutation80 hz
    mixedMoment B raw2856step1 raw2856step1Labels = mixedMoment B raw2856step2 raw2856step2Labels := by
      have ha : raw2856step2 = (fun i j => raw2856step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2856step2 raw2856step1; decide +kernel
      have hl : raw2856step2Labels = raw2856step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2856step1 raw2856step1Labels permutation10 permutation3
    mixedMoment B raw2856step2 raw2856step2Labels = mixedMoment B raw2856step3 raw2856step3Labels := by
      have ha : raw2856step3 = raw2856step2 := by apply Matrix.ext; unfold raw2856step3 raw2856step2; decide +kernel
      have hl : raw2856step2Labels = labelEmbedding6 ∘ raw2856step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2856step2 raw2856step2Labels raw2856step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw2857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2857step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2857step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2857step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2857step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2857 raw2857Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw2857 raw2857Labels = mixedMoment B raw2857step0 raw2857step0Labels := by
      have hz : ∀ j, raw2857 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2857step0 = (fun i j => raw2857 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2857step0 raw2857; decide +kernel
      have hl : raw2857step0Labels = raw2857Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2857 raw2857Labels permutation434 hz
    mixedMoment B raw2857step0 raw2857step0Labels = mixedMoment B raw2857step1 raw2857step1Labels := by
      have ha : raw2857step1 = (fun i j => raw2857step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2857step1 raw2857step0; decide +kernel
      have hl : raw2857step1Labels = raw2857step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2857step0 raw2857step0Labels permutation139 permutation2
    mixedMoment B raw2857step1 raw2857step1Labels = mixedMoment B raw2857step2 raw2857step2Labels := by
      have ha : raw2857step2 = -raw2857step1 := by apply Matrix.ext; change ∀ i j, raw2857step2 i j = -(raw2857step1 i j); unfold raw2857step2 raw2857step1; decide +kernel
      have hl : raw2857step2Labels = raw2857step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw2858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2858step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2858step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2858 raw2858Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw2858 raw2858Labels = mixedMoment B raw2858step0 raw2858step0Labels := by
      have hz : ∀ j, raw2858 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2858step0 = (fun i j => raw2858 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2858step0 raw2858; decide +kernel
      have hl : raw2858step0Labels = raw2858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2858 raw2858Labels permutation346 hz
    mixedMoment B raw2858step0 raw2858step0Labels = mixedMoment B raw2858step1 raw2858step1Labels := by
      have ha : raw2858step1 = (fun i j => raw2858step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2858step1 raw2858step0; decide +kernel
      have hl : raw2858step1Labels = raw2858step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2858step0 raw2858step0Labels permutation139 permutation2
    mixedMoment B raw2858step1 raw2858step1Labels = mixedMoment B raw2858step2 raw2858step2Labels := by
      have ha : raw2858step2 = -raw2858step1 := by apply Matrix.ext; change ∀ i j, raw2858step2 i j = -(raw2858step1 i j); unfold raw2858step2 raw2858step1; decide +kernel
      have hl : raw2858step2Labels = raw2858step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw2859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw2859step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2859step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2859 raw2859Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw2859 raw2859Labels = mixedMoment B raw2859step0 raw2859step0Labels := by
      have hz : ∀ j, raw2859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2859step0 = (fun i j => raw2859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2859step0 raw2859; decide +kernel
      have hl : raw2859step0Labels = raw2859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2859 raw2859Labels permutation434 hz
    mixedMoment B raw2859step0 raw2859step0Labels = mixedMoment B raw2859step1 raw2859step1Labels := by
      have hz : ∀ j, raw2859step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2859step1 = (fun i j => raw2859step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2859step1 raw2859step0; decide +kernel
      have hl : raw2859step1Labels = raw2859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2859step0 raw2859step0Labels permutation80 hz
    mixedMoment B raw2859step1 raw2859step1Labels = mixedMoment B raw2859step2 raw2859step2Labels := by
      have ha : raw2859step2 = (fun i j => raw2859step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2859step2 raw2859step1; decide +kernel
      have hl : raw2859step2Labels = raw2859step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2859step1 raw2859step1Labels permutation29 permutation2
    mixedMoment B raw2859step2 raw2859step2Labels = mixedMoment B raw2859step3 raw2859step3Labels := by
      have ha : raw2859step3 = -raw2859step2 := by apply Matrix.ext; change ∀ i j, raw2859step3 i j = -(raw2859step2 i j); unfold raw2859step3 raw2859step2; decide +kernel
      have hl : raw2859step3Labels = raw2859step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw2860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2860step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2860step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2860step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2860 raw2860Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw2860 raw2860Labels = mixedMoment B raw2860step0 raw2860step0Labels := by
      have hz : ∀ j, raw2860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2860step0 = (fun i j => raw2860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2860step0 raw2860; decide +kernel
      have hl : raw2860step0Labels = raw2860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2860 raw2860Labels permutation434 hz
    mixedMoment B raw2860step0 raw2860step0Labels = mixedMoment B raw2860step1 raw2860step1Labels := by
      have hz : ∀ j, raw2860step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2860step1 = (fun i j => raw2860step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2860step1 raw2860step0; decide +kernel
      have hl : raw2860step1Labels = raw2860step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2860step0 raw2860step0Labels permutation80 hz
    mixedMoment B raw2860step1 raw2860step1Labels = mixedMoment B raw2860step2 raw2860step2Labels := by
      have ha : raw2860step2 = (fun i j => raw2860step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2860step2 raw2860step1; decide +kernel
      have hl : raw2860step2Labels = raw2860step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2860step1 raw2860step1Labels permutation10 permutation2
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw2861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2861step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2861step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2861step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2861step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2861step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2861 raw2861Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2861 raw2861Labels = mixedMoment B raw2861step0 raw2861step0Labels := by
      have hz : ∀ j, raw2861 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2861step0 = (fun i j => raw2861 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2861step0 raw2861; decide +kernel
      have hl : raw2861step0Labels = raw2861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2861 raw2861Labels permutation434 hz
    mixedMoment B raw2861step0 raw2861step0Labels = mixedMoment B raw2861step1 raw2861step1Labels := by
      have hz : ∀ j, raw2861step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2861step1 = (fun i j => raw2861step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2861step1 raw2861step0; decide +kernel
      have hl : raw2861step1Labels = raw2861step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2861step0 raw2861step0Labels permutation56 hz
    mixedMoment B raw2861step1 raw2861step1Labels = mixedMoment B raw2861step2 raw2861step2Labels := by
      have ha : raw2861step2 = (fun i j => raw2861step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2861step2 raw2861step1; decide +kernel
      have hl : raw2861step2Labels = raw2861step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2861step1 raw2861step1Labels permutation10 permutation3
    mixedMoment B raw2861step2 raw2861step2Labels = mixedMoment B raw2861step3 raw2861step3Labels := by
      have ha : raw2861step3 = raw2861step2 := by apply Matrix.ext; unfold raw2861step3 raw2861step2; decide +kernel
      have hl : raw2861step2Labels = labelEmbedding6 ∘ raw2861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2861step2 raw2861step2Labels raw2861step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw2862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2862step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2862step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2862 raw2862Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw2862 raw2862Labels = mixedMoment B raw2862step0 raw2862step0Labels := by
      have hz : ∀ j, raw2862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2862step0 = (fun i j => raw2862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2862step0 raw2862; decide +kernel
      have hl : raw2862step0Labels = raw2862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2862 raw2862Labels permutation434 hz
    mixedMoment B raw2862step0 raw2862step0Labels = mixedMoment B raw2862step1 raw2862step1Labels := by
      have ha : raw2862step1 = (fun i j => raw2862step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2862step1 raw2862step0; decide +kernel
      have hl : raw2862step1Labels = raw2862step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2862step0 raw2862step0Labels permutation145 permutation2
    mixedMoment B raw2862step1 raw2862step1Labels = mixedMoment B raw2862step2 raw2862step2Labels := by
      have ha : raw2862step2 = -raw2862step1 := by apply Matrix.ext; change ∀ i j, raw2862step2 i j = -(raw2862step1 i j); unfold raw2862step2 raw2862step1; decide +kernel
      have hl : raw2862step2Labels = raw2862step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw2863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2863 raw2863Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw2863 raw2863Labels = mixedMoment B raw2863step0 raw2863step0Labels := by
      have hz : ∀ j, raw2863 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2863step0 = (fun i j => raw2863 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2863step0 raw2863; decide +kernel
      have hl : raw2863step0Labels = raw2863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2863 raw2863Labels permutation265 hz
    mixedMoment B raw2863step0 raw2863step0Labels = mixedMoment B raw2863step1 raw2863step1Labels := by
      have ha : raw2863step1 = (fun i j => raw2863step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2863step1 raw2863step0; decide +kernel
      have hl : raw2863step1Labels = raw2863step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2863step0 raw2863step0Labels permutation139 permutation2
    mixedMoment B raw2863step1 raw2863step1Labels = mixedMoment B raw2863step2 raw2863step2Labels := by
      have ha : raw2863step2 = -raw2863step1 := by apply Matrix.ext; change ∀ i j, raw2863step2 i j = -(raw2863step1 i j); unfold raw2863step2 raw2863step1; decide +kernel
      have hl : raw2863step2Labels = raw2863step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw2864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw2864step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2864step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2864step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2864 raw2864Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw2864 raw2864Labels = mixedMoment B raw2864step0 raw2864step0Labels := by
      have hz : ∀ j, raw2864 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2864step0 = (fun i j => raw2864 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2864step0 raw2864; decide +kernel
      have hl : raw2864step0Labels = raw2864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2864 raw2864Labels permutation434 hz
    mixedMoment B raw2864step0 raw2864step0Labels = mixedMoment B raw2864step1 raw2864step1Labels := by
      have hz : ∀ j, raw2864step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2864step1 = (fun i j => raw2864step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2864step1 raw2864step0; decide +kernel
      have hl : raw2864step1Labels = raw2864step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2864step0 raw2864step0Labels permutation56 hz
    mixedMoment B raw2864step1 raw2864step1Labels = mixedMoment B raw2864step2 raw2864step2Labels := by
      have ha : raw2864step2 = (fun i j => raw2864step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2864step2 raw2864step1; decide +kernel
      have hl : raw2864step2Labels = raw2864step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2864step1 raw2864step1Labels permutation29 permutation2
    mixedMoment B raw2864step2 raw2864step2Labels = mixedMoment B raw2864step3 raw2864step3Labels := by
      have ha : raw2864step3 = -raw2864step2 := by apply Matrix.ext; change ∀ i j, raw2864step3 i j = -(raw2864step2 i j); unfold raw2864step3 raw2864step2; decide +kernel
      have hl : raw2864step3Labels = raw2864step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw2865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2865step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2865step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2865 raw2865Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw2865 raw2865Labels = mixedMoment B raw2865step0 raw2865step0Labels := by
      have hz : ∀ j, raw2865 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2865step0 = (fun i j => raw2865 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2865step0 raw2865; decide +kernel
      have hl : raw2865step0Labels = raw2865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2865 raw2865Labels permutation434 hz
    mixedMoment B raw2865step0 raw2865step0Labels = mixedMoment B raw2865step1 raw2865step1Labels := by
      have hz : ∀ j, raw2865step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2865step1 = (fun i j => raw2865step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2865step1 raw2865step0; decide +kernel
      have hl : raw2865step1Labels = raw2865step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2865step0 raw2865step0Labels permutation56 hz
    mixedMoment B raw2865step1 raw2865step1Labels = mixedMoment B raw2865step2 raw2865step2Labels := by
      have ha : raw2865step2 = (fun i j => raw2865step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2865step2 raw2865step1; decide +kernel
      have hl : raw2865step2Labels = raw2865step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2865step1 raw2865step1Labels permutation10 permutation2
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw2866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2866step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2866step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2866step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2866 raw2866Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2866 raw2866Labels = mixedMoment B raw2866step0 raw2866step0Labels := by
      have hz : ∀ j, raw2866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2866step0 = (fun i j => raw2866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2866step0 raw2866; decide +kernel
      have hl : raw2866step0Labels = raw2866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2866 raw2866Labels permutation346 hz
    mixedMoment B raw2866step0 raw2866step0Labels = mixedMoment B raw2866step1 raw2866step1Labels := by
      have hz : ∀ j, raw2866step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2866step1 = (fun i j => raw2866step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2866step1 raw2866step0; decide +kernel
      have hl : raw2866step1Labels = raw2866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2866step0 raw2866step0Labels permutation56 hz
    mixedMoment B raw2866step1 raw2866step1Labels = mixedMoment B raw2866step2 raw2866step2Labels := by
      have ha : raw2866step2 = (fun i j => raw2866step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2866step2 raw2866step1; decide +kernel
      have hl : raw2866step2Labels = raw2866step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2866step1 raw2866step1Labels permutation10 permutation3
    mixedMoment B raw2866step2 raw2866step2Labels = mixedMoment B raw2866step3 raw2866step3Labels := by
      have ha : raw2866step3 = raw2866step2 := by apply Matrix.ext; unfold raw2866step3 raw2866step2; decide +kernel
      have hl : raw2866step2Labels = labelEmbedding6 ∘ raw2866step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2866step2 raw2866step2Labels raw2866step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw2867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2867step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2867 raw2867Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw2867 raw2867Labels = mixedMoment B raw2867step0 raw2867step0Labels := by
      have hz : ∀ j, raw2867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2867step0 = (fun i j => raw2867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2867step0 raw2867; decide +kernel
      have hl : raw2867step0Labels = raw2867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2867 raw2867Labels permutation346 hz
    mixedMoment B raw2867step0 raw2867step0Labels = mixedMoment B raw2867step1 raw2867step1Labels := by
      have ha : raw2867step1 = (fun i j => raw2867step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2867step1 raw2867step0; decide +kernel
      have hl : raw2867step1Labels = raw2867step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2867step0 raw2867step0Labels permutation145 permutation2
    mixedMoment B raw2867step1 raw2867step1Labels = mixedMoment B raw2867step2 raw2867step2Labels := by
      have ha : raw2867step2 = -raw2867step1 := by apply Matrix.ext; change ∀ i j, raw2867step2 i j = -(raw2867step1 i j); unfold raw2867step2 raw2867step1; decide +kernel
      have hl : raw2867step2Labels = raw2867step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw2868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw2868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2868step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2868 raw2868Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw2868 raw2868Labels = mixedMoment B raw2868step0 raw2868step0Labels := by
      have hz : ∀ j, raw2868 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2868step0 = (fun i j => raw2868 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2868step0 raw2868; decide +kernel
      have hl : raw2868step0Labels = raw2868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2868 raw2868Labels permutation265 hz
    mixedMoment B raw2868step0 raw2868step0Labels = mixedMoment B raw2868step1 raw2868step1Labels := by
      have ha : raw2868step1 = (fun i j => raw2868step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2868step1 raw2868step0; decide +kernel
      have hl : raw2868step1Labels = raw2868step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2868step0 raw2868step0Labels permutation145 permutation2
    mixedMoment B raw2868step1 raw2868step1Labels = mixedMoment B raw2868step2 raw2868step2Labels := by
      have ha : raw2868step2 = -raw2868step1 := by apply Matrix.ext; change ∀ i j, raw2868step2 i j = -(raw2868step1 i j); unfold raw2868step2 raw2868step1; decide +kernel
      have hl : raw2868step2Labels = raw2868step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw2869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2]]
def raw2869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw2869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2869step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2869step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2869 raw2869Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw2869 raw2869Labels = mixedMoment B raw2869step0 raw2869step0Labels := by
      have hz : ∀ j, raw2869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2869step0 = (fun i j => raw2869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2869step0 raw2869; decide +kernel
      have hl : raw2869step0Labels = raw2869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2869 raw2869Labels permutation346 hz
    mixedMoment B raw2869step0 raw2869step0Labels = mixedMoment B raw2869step1 raw2869step1Labels := by
      have hz : ∀ j, raw2869step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2869step1 = (fun i j => raw2869step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2869step1 raw2869step0; decide +kernel
      have hl : raw2869step1Labels = raw2869step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2869step0 raw2869step0Labels permutation56 hz
    mixedMoment B raw2869step1 raw2869step1Labels = mixedMoment B raw2869step2 raw2869step2Labels := by
      have ha : raw2869step2 = (fun i j => raw2869step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2869step2 raw2869step1; decide +kernel
      have hl : raw2869step2Labels = raw2869step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2869step1 raw2869step1Labels permutation29 permutation2
    mixedMoment B raw2869step2 raw2869step2Labels = mixedMoment B raw2869step3 raw2869step3Labels := by
      have ha : raw2869step3 = -raw2869step2 := by apply Matrix.ext; change ∀ i j, raw2869step3 i j = -(raw2869step2 i j); unfold raw2869step3 raw2869step2; decide +kernel
      have hl : raw2869step3Labels = raw2869step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw2870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2]]
def raw2870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2870 raw2870Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw2870 raw2870Labels = mixedMoment B raw2870step0 raw2870step0Labels := by
      have hz : ∀ j, raw2870 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2870step0 = (fun i j => raw2870 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2870step0 raw2870; decide +kernel
      have hl : raw2870step0Labels = raw2870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2870 raw2870Labels permutation346 hz
    mixedMoment B raw2870step0 raw2870step0Labels = mixedMoment B raw2870step1 raw2870step1Labels := by
      have hz : ∀ j, raw2870step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2870step1 = (fun i j => raw2870step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2870step1 raw2870step0; decide +kernel
      have hl : raw2870step1Labels = raw2870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2870step0 raw2870step0Labels permutation56 hz
    mixedMoment B raw2870step1 raw2870step1Labels = mixedMoment B raw2870step2 raw2870step2Labels := by
      have ha : raw2870step2 = (fun i j => raw2870step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2870step2 raw2870step1; decide +kernel
      have hl : raw2870step2Labels = raw2870step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2870step1 raw2870step1Labels permutation10 permutation2
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw2871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw2871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2871step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2871step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2871step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2871step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2871 raw2871Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2871 raw2871Labels = mixedMoment B raw2871step0 raw2871step0Labels := by
      have hz : ∀ j, raw2871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2871step0 = (fun i j => raw2871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2871step0 raw2871; decide +kernel
      have hl : raw2871step0Labels = raw2871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2871 raw2871Labels permutation434 hz
    mixedMoment B raw2871step0 raw2871step0Labels = mixedMoment B raw2871step1 raw2871step1Labels := by
      have hz : ∀ j, raw2871step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2871step1 = (fun i j => raw2871step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2871step1 raw2871step0; decide +kernel
      have hl : raw2871step1Labels = raw2871step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2871step0 raw2871step0Labels permutation80 hz
    mixedMoment B raw2871step1 raw2871step1Labels = mixedMoment B raw2871step2 raw2871step2Labels := by
      have hz : ∀ j, raw2871step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2871step2 = (fun i j => raw2871step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2871step2 raw2871step1; decide +kernel
      have hl : raw2871step2Labels = raw2871step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2871step1 raw2871step1Labels permutation14 hz
    mixedMoment B raw2871step2 raw2871step2Labels = mixedMoment B raw2871step3 raw2871step3Labels := by
      have ha : raw2871step3 = (fun i j => raw2871step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2871step3 raw2871step2; decide +kernel
      have hl : raw2871step3Labels = raw2871step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2871step2 raw2871step2Labels permutation2 permutation3
    mixedMoment B raw2871step3 raw2871step3Labels = mixedMoment B raw2871step4 raw2871step4Labels := by
      have ha : raw2871step4 = raw2871step3 := by apply Matrix.ext; unfold raw2871step4 raw2871step3; decide +kernel
      have hl : raw2871step3Labels = labelEmbedding6 ∘ raw2871step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2871step3 raw2871step3Labels raw2871step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw2872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2872step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2872step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2872step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2872 raw2872Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2872 raw2872Labels = mixedMoment B raw2872step0 raw2872step0Labels := by
      have hz : ∀ j, raw2872 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2872step0 = (fun i j => raw2872 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2872step0 raw2872; decide +kernel
      have hl : raw2872step0Labels = raw2872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2872 raw2872Labels permutation434 hz
    mixedMoment B raw2872step0 raw2872step0Labels = mixedMoment B raw2872step1 raw2872step1Labels := by
      have hz : ∀ j, raw2872step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2872step1 = (fun i j => raw2872step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2872step1 raw2872step0; decide +kernel
      have hl : raw2872step1Labels = raw2872step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2872step0 raw2872step0Labels permutation80 hz
    mixedMoment B raw2872step1 raw2872step1Labels = mixedMoment B raw2872step2 raw2872step2Labels := by
      have ha : raw2872step2 = (fun i j => raw2872step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2872step2 raw2872step1; decide +kernel
      have hl : raw2872step2Labels = raw2872step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2872step1 raw2872step1Labels permutation31 permutation2
    mixedMoment B raw2872step2 raw2872step2Labels = mixedMoment B raw2872step3 raw2872step3Labels := by
      have ha : raw2872step3 = -raw2872step2 := by apply Matrix.ext; change ∀ i j, raw2872step3 i j = -(raw2872step2 i j); unfold raw2872step3 raw2872step2; decide +kernel
      have hl : raw2872step3Labels = raw2872step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw2873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2873step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2873step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2873 raw2873Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2873 raw2873Labels = mixedMoment B raw2873step0 raw2873step0Labels := by
      have hz : ∀ j, raw2873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2873step0 = (fun i j => raw2873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2873step0 raw2873; decide +kernel
      have hl : raw2873step0Labels = raw2873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2873 raw2873Labels permutation434 hz
    mixedMoment B raw2873step0 raw2873step0Labels = mixedMoment B raw2873step1 raw2873step1Labels := by
      have hz : ∀ j, raw2873step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2873step1 = (fun i j => raw2873step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2873step1 raw2873step0; decide +kernel
      have hl : raw2873step1Labels = raw2873step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2873step0 raw2873step0Labels permutation56 hz
    mixedMoment B raw2873step1 raw2873step1Labels = mixedMoment B raw2873step2 raw2873step2Labels := by
      have ha : raw2873step2 = (fun i j => raw2873step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2873step2 raw2873step1; decide +kernel
      have hl : raw2873step2Labels = raw2873step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2873step1 raw2873step1Labels permutation31 permutation2
    mixedMoment B raw2873step2 raw2873step2Labels = mixedMoment B raw2873step3 raw2873step3Labels := by
      have ha : raw2873step3 = -raw2873step2 := by apply Matrix.ext; change ∀ i j, raw2873step3 i j = -(raw2873step2 i j); unfold raw2873step3 raw2873step2; decide +kernel
      have hl : raw2873step3Labels = raw2873step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw2874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw2874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2874step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2874step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2874 raw2874Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2874 raw2874Labels = mixedMoment B raw2874step0 raw2874step0Labels := by
      have hz : ∀ j, raw2874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2874step0 = (fun i j => raw2874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2874step0 raw2874; decide +kernel
      have hl : raw2874step0Labels = raw2874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2874 raw2874Labels permutation346 hz
    mixedMoment B raw2874step0 raw2874step0Labels = mixedMoment B raw2874step1 raw2874step1Labels := by
      have hz : ∀ j, raw2874step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2874step1 = (fun i j => raw2874step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2874step1 raw2874step0; decide +kernel
      have hl : raw2874step1Labels = raw2874step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2874step0 raw2874step0Labels permutation56 hz
    mixedMoment B raw2874step1 raw2874step1Labels = mixedMoment B raw2874step2 raw2874step2Labels := by
      have ha : raw2874step2 = (fun i j => raw2874step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2874step2 raw2874step1; decide +kernel
      have hl : raw2874step2Labels = raw2874step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2874step1 raw2874step1Labels permutation31 permutation2
    mixedMoment B raw2874step2 raw2874step2Labels = mixedMoment B raw2874step3 raw2874step3Labels := by
      have ha : raw2874step3 = -raw2874step2 := by apply Matrix.ext; change ∀ i j, raw2874step3 i j = -(raw2874step2 i j); unfold raw2874step3 raw2874step2; decide +kernel
      have hl : raw2874step3Labels = raw2874step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw2875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw2875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw2875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2875step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw2875step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2875step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2875step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2875 raw2875Labels = mixedMoment B node5494 node5494Labels := by
  calc
    mixedMoment B raw2875 raw2875Labels = mixedMoment B raw2875step0 raw2875step0Labels := by
      have hz : ∀ j, raw2875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2875step0 = (fun i j => raw2875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2875step0 raw2875; decide +kernel
      have hl : raw2875step0Labels = raw2875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2875 raw2875Labels permutation434 hz
    mixedMoment B raw2875step0 raw2875step0Labels = mixedMoment B raw2875step1 raw2875step1Labels := by
      have hz : ∀ j, raw2875step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2875step1 = (fun i j => raw2875step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2875step1 raw2875step0; decide +kernel
      have hl : raw2875step1Labels = raw2875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2875step0 raw2875step0Labels permutation80 hz
    mixedMoment B raw2875step1 raw2875step1Labels = mixedMoment B raw2875step2 raw2875step2Labels := by
      have hz : ∀ j, raw2875step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2875step2 = (fun i j => raw2875step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2875step2 raw2875step1; decide +kernel
      have hl : raw2875step2Labels = raw2875step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2875step1 raw2875step1Labels permutation14 hz
    _ = mixedMoment B node5494 node5494Labels := by rfl

def raw2876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![3, -1, -2]]
def raw2876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw2876step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2876step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw2876step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2876 raw2876Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw2876 raw2876Labels = mixedMoment B raw2876step0 raw2876step0Labels := by
      have hz : ∀ j, raw2876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2876step0 = (fun i j => raw2876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2876step0 raw2876; decide +kernel
      have hl : raw2876step0Labels = raw2876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2876 raw2876Labels permutation434 hz
    mixedMoment B raw2876step0 raw2876step0Labels = mixedMoment B raw2876step1 raw2876step1Labels := by
      have hz : ∀ j, raw2876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2876step1 = (fun i j => raw2876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2876step1 raw2876step0; decide +kernel
      have hl : raw2876step1Labels = raw2876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2876step0 raw2876step0Labels permutation80 hz
    mixedMoment B raw2876step1 raw2876step1Labels = mixedMoment B raw2876step2 raw2876step2Labels := by
      have hz : ∀ j, raw2876step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2876step2 = (fun i j => raw2876step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2876step2 raw2876step1; decide +kernel
      have hl : raw2876step2Labels = raw2876step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2876step1 raw2876step1Labels permutation14 hz
    mixedMoment B raw2876step2 raw2876step2Labels = mixedMoment B raw2876step3 raw2876step3Labels := by
      have ha : raw2876step3 = (fun i j => raw2876step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2876step3 raw2876step2; decide +kernel
      have hl : raw2876step3Labels = raw2876step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2876step2 raw2876step2Labels permutation7 permutation2
    mixedMoment B raw2876step3 raw2876step3Labels = mixedMoment B raw2876step4 raw2876step4Labels := by
      have ha : raw2876step4 = -raw2876step3 := by apply Matrix.ext; change ∀ i j, raw2876step4 i j = -(raw2876step3 i j); unfold raw2876step4 raw2876step3; decide +kernel
      have hl : raw2876step4Labels = raw2876step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw2877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2877step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2877step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2877step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2877 raw2877Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2877 raw2877Labels = mixedMoment B raw2877step0 raw2877step0Labels := by
      have hz : ∀ j, raw2877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2877step0 = (fun i j => raw2877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2877step0 raw2877; decide +kernel
      have hl : raw2877step0Labels = raw2877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2877 raw2877Labels permutation434 hz
    mixedMoment B raw2877step0 raw2877step0Labels = mixedMoment B raw2877step1 raw2877step1Labels := by
      have hz : ∀ j, raw2877step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2877step1 = (fun i j => raw2877step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2877step1 raw2877step0; decide +kernel
      have hl : raw2877step1Labels = raw2877step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2877step0 raw2877step0Labels permutation80 hz
    mixedMoment B raw2877step1 raw2877step1Labels = mixedMoment B raw2877step2 raw2877step2Labels := by
      have ha : raw2877step2 = (fun i j => raw2877step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2877step2 raw2877step1; decide +kernel
      have hl : raw2877step2Labels = raw2877step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2877step1 raw2877step1Labels permutation31 permutation2
    mixedMoment B raw2877step2 raw2877step2Labels = mixedMoment B raw2877step3 raw2877step3Labels := by
      have ha : raw2877step3 = -raw2877step2 := by apply Matrix.ext; change ∀ i j, raw2877step3 i j = -(raw2877step2 i j); unfold raw2877step3 raw2877step2; decide +kernel
      have hl : raw2877step3Labels = raw2877step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw2878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2878step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2878step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2878 raw2878Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2878 raw2878Labels = mixedMoment B raw2878step0 raw2878step0Labels := by
      have hz : ∀ j, raw2878 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2878step0 = (fun i j => raw2878 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2878step0 raw2878; decide +kernel
      have hl : raw2878step0Labels = raw2878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2878 raw2878Labels permutation434 hz
    mixedMoment B raw2878step0 raw2878step0Labels = mixedMoment B raw2878step1 raw2878step1Labels := by
      have hz : ∀ j, raw2878step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2878step1 = (fun i j => raw2878step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2878step1 raw2878step0; decide +kernel
      have hl : raw2878step1Labels = raw2878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2878step0 raw2878step0Labels permutation56 hz
    mixedMoment B raw2878step1 raw2878step1Labels = mixedMoment B raw2878step2 raw2878step2Labels := by
      have ha : raw2878step2 = (fun i j => raw2878step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2878step2 raw2878step1; decide +kernel
      have hl : raw2878step2Labels = raw2878step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2878step1 raw2878step1Labels permutation31 permutation2
    mixedMoment B raw2878step2 raw2878step2Labels = mixedMoment B raw2878step3 raw2878step3Labels := by
      have ha : raw2878step3 = -raw2878step2 := by apply Matrix.ext; change ∀ i j, raw2878step3 i j = -(raw2878step2 i j); unfold raw2878step3 raw2878step2; decide +kernel
      have hl : raw2878step3Labels = raw2878step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw2879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2]]
def raw2879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2879step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2879step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2879 raw2879Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2879 raw2879Labels = mixedMoment B raw2879step0 raw2879step0Labels := by
      have hz : ∀ j, raw2879 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2879step0 = (fun i j => raw2879 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2879step0 raw2879; decide +kernel
      have hl : raw2879step0Labels = raw2879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2879 raw2879Labels permutation346 hz
    mixedMoment B raw2879step0 raw2879step0Labels = mixedMoment B raw2879step1 raw2879step1Labels := by
      have hz : ∀ j, raw2879step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2879step1 = (fun i j => raw2879step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2879step1 raw2879step0; decide +kernel
      have hl : raw2879step1Labels = raw2879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2879step0 raw2879step0Labels permutation56 hz
    mixedMoment B raw2879step1 raw2879step1Labels = mixedMoment B raw2879step2 raw2879step2Labels := by
      have ha : raw2879step2 = (fun i j => raw2879step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2879step2 raw2879step1; decide +kernel
      have hl : raw2879step2Labels = raw2879step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2879step1 raw2879step1Labels permutation31 permutation2
    mixedMoment B raw2879step2 raw2879step2Labels = mixedMoment B raw2879step3 raw2879step3Labels := by
      have ha : raw2879step3 = -raw2879step2 := by apply Matrix.ext; change ∀ i j, raw2879step3 i j = -(raw2879step2 i j); unfold raw2879step3 raw2879step2; decide +kernel
      have hl : raw2879step3Labels = raw2879step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw2880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw2880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw2880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2]]
def raw2880step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![3, -1, -2]]
def raw2880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw2880step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2880step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw2880step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2880 raw2880Labels = mixedMoment B node5309 node5309Labels := by
  calc
    mixedMoment B raw2880 raw2880Labels = mixedMoment B raw2880step0 raw2880step0Labels := by
      have hz : ∀ j, raw2880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2880step0 = (fun i j => raw2880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2880step0 raw2880; decide +kernel
      have hl : raw2880step0Labels = raw2880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2880 raw2880Labels permutation434 hz
    mixedMoment B raw2880step0 raw2880step0Labels = mixedMoment B raw2880step1 raw2880step1Labels := by
      have hz : ∀ j, raw2880step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2880step1 = (fun i j => raw2880step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2880step1 raw2880step0; decide +kernel
      have hl : raw2880step1Labels = raw2880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2880step0 raw2880step0Labels permutation80 hz
    mixedMoment B raw2880step1 raw2880step1Labels = mixedMoment B raw2880step2 raw2880step2Labels := by
      have hz : ∀ j, raw2880step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2880step2 = (fun i j => raw2880step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2880step2 raw2880step1; decide +kernel
      have hl : raw2880step2Labels = raw2880step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2880step1 raw2880step1Labels permutation14 hz
    mixedMoment B raw2880step2 raw2880step2Labels = mixedMoment B raw2880step3 raw2880step3Labels := by
      have ha : raw2880step3 = (fun i j => raw2880step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2880step3 raw2880step2; decide +kernel
      have hl : raw2880step3Labels = raw2880step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2880step2 raw2880step2Labels permutation7 permutation2
    mixedMoment B raw2880step3 raw2880step3Labels = mixedMoment B raw2880step4 raw2880step4Labels := by
      have ha : raw2880step4 = -raw2880step3 := by apply Matrix.ext; change ∀ i j, raw2880step4 i j = -(raw2880step3 i j); unfold raw2880step4 raw2880step3; decide +kernel
      have hl : raw2880step4Labels = raw2880step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5309 node5309Labels := by rfl

def raw2881 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2881step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2881step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2881step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2881step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2881step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2881 raw2881Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2881 raw2881Labels = mixedMoment B raw2881step0 raw2881step0Labels := by
      have hz : ∀ j, raw2881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2881step0 = (fun i j => raw2881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2881step0 raw2881; decide +kernel
      have hl : raw2881step0Labels = raw2881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2881 raw2881Labels permutation434 hz
    mixedMoment B raw2881step0 raw2881step0Labels = mixedMoment B raw2881step1 raw2881step1Labels := by
      have hz : ∀ j, raw2881step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2881step1 = (fun i j => raw2881step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2881step1 raw2881step0; decide +kernel
      have hl : raw2881step1Labels = raw2881step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2881step0 raw2881step0Labels permutation80 hz
    mixedMoment B raw2881step1 raw2881step1Labels = mixedMoment B raw2881step2 raw2881step2Labels := by
      have ha : raw2881step2 = (fun i j => raw2881step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2881step2 raw2881step1; decide +kernel
      have hl : raw2881step2Labels = raw2881step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2881step1 raw2881step1Labels permutation29 permutation6
    mixedMoment B raw2881step2 raw2881step2Labels = mixedMoment B raw2881step3 raw2881step3Labels := by
      have ha : raw2881step3 = -raw2881step2 := by apply Matrix.ext; change ∀ i j, raw2881step3 i j = -(raw2881step2 i j); unfold raw2881step3 raw2881step2; decide +kernel
      have hl : raw2881step3Labels = raw2881step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2881step3 raw2881step3Labels = mixedMoment B raw2881step4 raw2881step4Labels := by
      have ha : raw2881step4 = raw2881step3 := by apply Matrix.ext; unfold raw2881step4 raw2881step3; decide +kernel
      have hl : raw2881step3Labels = labelEmbedding9 ∘ raw2881step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2881step3 raw2881step3Labels raw2881step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2882 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2882step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2882step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2882step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2882step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2882step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2882 raw2882Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2882 raw2882Labels = mixedMoment B raw2882step0 raw2882step0Labels := by
      have hz : ∀ j, raw2882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2882step0 = (fun i j => raw2882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2882step0 raw2882; decide +kernel
      have hl : raw2882step0Labels = raw2882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2882 raw2882Labels permutation434 hz
    mixedMoment B raw2882step0 raw2882step0Labels = mixedMoment B raw2882step1 raw2882step1Labels := by
      have hz : ∀ j, raw2882step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2882step1 = (fun i j => raw2882step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2882step1 raw2882step0; decide +kernel
      have hl : raw2882step1Labels = raw2882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2882step0 raw2882step0Labels permutation56 hz
    mixedMoment B raw2882step1 raw2882step1Labels = mixedMoment B raw2882step2 raw2882step2Labels := by
      have ha : raw2882step2 = (fun i j => raw2882step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2882step2 raw2882step1; decide +kernel
      have hl : raw2882step2Labels = raw2882step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2882step1 raw2882step1Labels permutation29 permutation6
    mixedMoment B raw2882step2 raw2882step2Labels = mixedMoment B raw2882step3 raw2882step3Labels := by
      have ha : raw2882step3 = -raw2882step2 := by apply Matrix.ext; change ∀ i j, raw2882step3 i j = -(raw2882step2 i j); unfold raw2882step3 raw2882step2; decide +kernel
      have hl : raw2882step3Labels = raw2882step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2882step3 raw2882step3Labels = mixedMoment B raw2882step4 raw2882step4Labels := by
      have ha : raw2882step4 = raw2882step3 := by apply Matrix.ext; unfold raw2882step4 raw2882step3; decide +kernel
      have hl : raw2882step3Labels = labelEmbedding9 ∘ raw2882step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2882step3 raw2882step3Labels raw2882step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2883 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2883step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2883step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2883step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2883step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2883step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2883step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2883step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2883 raw2883Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2883 raw2883Labels = mixedMoment B raw2883step0 raw2883step0Labels := by
      have hz : ∀ j, raw2883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2883step0 = (fun i j => raw2883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2883step0 raw2883; decide +kernel
      have hl : raw2883step0Labels = raw2883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2883 raw2883Labels permutation346 hz
    mixedMoment B raw2883step0 raw2883step0Labels = mixedMoment B raw2883step1 raw2883step1Labels := by
      have hz : ∀ j, raw2883step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2883step1 = (fun i j => raw2883step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2883step1 raw2883step0; decide +kernel
      have hl : raw2883step1Labels = raw2883step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2883step0 raw2883step0Labels permutation56 hz
    mixedMoment B raw2883step1 raw2883step1Labels = mixedMoment B raw2883step2 raw2883step2Labels := by
      have ha : raw2883step2 = (fun i j => raw2883step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2883step2 raw2883step1; decide +kernel
      have hl : raw2883step2Labels = raw2883step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2883step1 raw2883step1Labels permutation29 permutation6
    mixedMoment B raw2883step2 raw2883step2Labels = mixedMoment B raw2883step3 raw2883step3Labels := by
      have ha : raw2883step3 = -raw2883step2 := by apply Matrix.ext; change ∀ i j, raw2883step3 i j = -(raw2883step2 i j); unfold raw2883step3 raw2883step2; decide +kernel
      have hl : raw2883step3Labels = raw2883step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2883step3 raw2883step3Labels = mixedMoment B raw2883step4 raw2883step4Labels := by
      have ha : raw2883step4 = raw2883step3 := by apply Matrix.ext; unfold raw2883step4 raw2883step3; decide +kernel
      have hl : raw2883step3Labels = labelEmbedding9 ∘ raw2883step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2883step3 raw2883step3Labels raw2883step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2884 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2884step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![0, -2, 2]]
def raw2884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw2884step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2884step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2884step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2884 raw2884Labels = mixedMoment B node5456 node5456Labels := by
  calc
    mixedMoment B raw2884 raw2884Labels = mixedMoment B raw2884step0 raw2884step0Labels := by
      have hz : ∀ j, raw2884 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2884step0 = (fun i j => raw2884 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2884step0 raw2884; decide +kernel
      have hl : raw2884step0Labels = raw2884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2884 raw2884Labels permutation434 hz
    mixedMoment B raw2884step0 raw2884step0Labels = mixedMoment B raw2884step1 raw2884step1Labels := by
      have hz : ∀ j, raw2884step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2884step1 = (fun i j => raw2884step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2884step1 raw2884step0; decide +kernel
      have hl : raw2884step1Labels = raw2884step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2884step0 raw2884step0Labels permutation80 hz
    mixedMoment B raw2884step1 raw2884step1Labels = mixedMoment B raw2884step2 raw2884step2Labels := by
      have hz : ∀ j, raw2884step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2884step2 = (fun i j => raw2884step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2884step2 raw2884step1; decide +kernel
      have hl : raw2884step2Labels = raw2884step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2884step1 raw2884step1Labels permutation14 hz
    mixedMoment B raw2884step2 raw2884step2Labels = mixedMoment B raw2884step3 raw2884step3Labels := by
      have ha : raw2884step3 = (fun i j => raw2884step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2884step3 raw2884step2; decide +kernel
      have hl : raw2884step3Labels = raw2884step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2884step2 raw2884step2Labels permutation3 permutation2
    mixedMoment B raw2884step3 raw2884step3Labels = mixedMoment B raw2884step4 raw2884step4Labels := by
      have ha : raw2884step4 = -raw2884step3 := by apply Matrix.ext; change ∀ i j, raw2884step4 i j = -(raw2884step3 i j); unfold raw2884step4 raw2884step3; decide +kernel
      have hl : raw2884step4Labels = raw2884step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5456 node5456Labels := by rfl

def raw2885 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2]]
def raw2885step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2885step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2885step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2885step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2885step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2885 raw2885Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2885 raw2885Labels = mixedMoment B raw2885step0 raw2885step0Labels := by
      have hz : ∀ j, raw2885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2885step0 = (fun i j => raw2885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2885step0 raw2885; decide +kernel
      have hl : raw2885step0Labels = raw2885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2885 raw2885Labels permutation434 hz
    mixedMoment B raw2885step0 raw2885step0Labels = mixedMoment B raw2885step1 raw2885step1Labels := by
      have hz : ∀ j, raw2885step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2885step1 = (fun i j => raw2885step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2885step1 raw2885step0; decide +kernel
      have hl : raw2885step1Labels = raw2885step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2885step0 raw2885step0Labels permutation80 hz
    mixedMoment B raw2885step1 raw2885step1Labels = mixedMoment B raw2885step2 raw2885step2Labels := by
      have hz : ∀ j, raw2885step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2885step2 = (fun i j => raw2885step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2885step2 raw2885step1; decide +kernel
      have hl : raw2885step2Labels = raw2885step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2885step1 raw2885step1Labels permutation14 hz
    mixedMoment B raw2885step2 raw2885step2Labels = mixedMoment B raw2885step3 raw2885step3Labels := by
      have ha : raw2885step3 = (fun i j => raw2885step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw2885step3 raw2885step2; decide +kernel
      have hl : raw2885step3Labels = raw2885step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2885step2 raw2885step2Labels permutation2 permutation7
    mixedMoment B raw2885step3 raw2885step3Labels = mixedMoment B raw2885step4 raw2885step4Labels := by
      have ha : raw2885step4 = raw2885step3 := by apply Matrix.ext; unfold raw2885step4 raw2885step3; decide +kernel
      have hl : raw2885step3Labels = labelEmbedding10 ∘ raw2885step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2885step3 raw2885step3Labels raw2885step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw2886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2886step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2886step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2886step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2886 raw2886Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw2886 raw2886Labels = mixedMoment B raw2886step0 raw2886step0Labels := by
      have hz : ∀ j, raw2886 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2886step0 = (fun i j => raw2886 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2886step0 raw2886; decide +kernel
      have hl : raw2886step0Labels = raw2886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2886 raw2886Labels permutation434 hz
    mixedMoment B raw2886step0 raw2886step0Labels = mixedMoment B raw2886step1 raw2886step1Labels := by
      have hz : ∀ j, raw2886step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2886step1 = (fun i j => raw2886step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2886step1 raw2886step0; decide +kernel
      have hl : raw2886step1Labels = raw2886step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2886step0 raw2886step0Labels permutation80 hz
    mixedMoment B raw2886step1 raw2886step1Labels = mixedMoment B raw2886step2 raw2886step2Labels := by
      have ha : raw2886step2 = (fun i j => raw2886step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2886step2 raw2886step1; decide +kernel
      have hl : raw2886step2Labels = raw2886step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2886step1 raw2886step1Labels permutation29 permutation4
    mixedMoment B raw2886step2 raw2886step2Labels = mixedMoment B raw2886step3 raw2886step3Labels := by
      have ha : raw2886step3 = raw2886step2 := by apply Matrix.ext; unfold raw2886step3 raw2886step2; decide +kernel
      have hl : raw2886step2Labels = labelEmbedding7 ∘ raw2886step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2886step2 raw2886step2Labels raw2886step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw2887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2887step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2887 raw2887Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2887 raw2887Labels = mixedMoment B raw2887step0 raw2887step0Labels := by
      have hz : ∀ j, raw2887 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2887step0 = (fun i j => raw2887 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2887step0 raw2887; decide +kernel
      have hl : raw2887step0Labels = raw2887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2887 raw2887Labels permutation434 hz
    mixedMoment B raw2887step0 raw2887step0Labels = mixedMoment B raw2887step1 raw2887step1Labels := by
      have ha : raw2887step1 = (fun i j => raw2887step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2887step1 raw2887step0; decide +kernel
      have hl : raw2887step1Labels = raw2887step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2887step0 raw2887step0Labels permutation137 permutation4
    mixedMoment B raw2887step1 raw2887step1Labels = mixedMoment B raw2887step2 raw2887step2Labels := by
      have ha : raw2887step2 = raw2887step1 := by apply Matrix.ext; unfold raw2887step2 raw2887step1; decide +kernel
      have hl : raw2887step1Labels = labelEmbedding7 ∘ raw2887step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2887step1 raw2887step1Labels raw2887step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2888 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2888step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2888 raw2888Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2888 raw2888Labels = mixedMoment B raw2888step0 raw2888step0Labels := by
      have hz : ∀ j, raw2888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2888step0 = (fun i j => raw2888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2888step0 raw2888; decide +kernel
      have hl : raw2888step0Labels = raw2888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2888 raw2888Labels permutation346 hz
    mixedMoment B raw2888step0 raw2888step0Labels = mixedMoment B raw2888step1 raw2888step1Labels := by
      have ha : raw2888step1 = (fun i j => raw2888step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2888step1 raw2888step0; decide +kernel
      have hl : raw2888step1Labels = raw2888step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2888step0 raw2888step0Labels permutation137 permutation4
    mixedMoment B raw2888step1 raw2888step1Labels = mixedMoment B raw2888step2 raw2888step2Labels := by
      have ha : raw2888step2 = raw2888step1 := by apply Matrix.ext; unfold raw2888step2 raw2888step1; decide +kernel
      have hl : raw2888step1Labels = labelEmbedding7 ∘ raw2888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2888step1 raw2888step1Labels raw2888step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2889 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2889step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2889step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2889step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2889 raw2889Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2889 raw2889Labels = mixedMoment B raw2889step0 raw2889step0Labels := by
      have hz : ∀ j, raw2889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2889step0 = (fun i j => raw2889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2889step0 raw2889; decide +kernel
      have hl : raw2889step0Labels = raw2889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2889 raw2889Labels permutation434 hz
    mixedMoment B raw2889step0 raw2889step0Labels = mixedMoment B raw2889step1 raw2889step1Labels := by
      have hz : ∀ j, raw2889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2889step1 = (fun i j => raw2889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2889step1 raw2889step0; decide +kernel
      have hl : raw2889step1Labels = raw2889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2889step0 raw2889step0Labels permutation80 hz
    mixedMoment B raw2889step1 raw2889step1Labels = mixedMoment B raw2889step2 raw2889step2Labels := by
      have ha : raw2889step2 = (fun i j => raw2889step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2889step2 raw2889step1; decide +kernel
      have hl : raw2889step2Labels = raw2889step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2889step1 raw2889step1Labels permutation28 permutation4
    mixedMoment B raw2889step2 raw2889step2Labels = mixedMoment B raw2889step3 raw2889step3Labels := by
      have ha : raw2889step3 = raw2889step2 := by apply Matrix.ext; unfold raw2889step3 raw2889step2; decide +kernel
      have hl : raw2889step2Labels = labelEmbedding7 ∘ raw2889step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2889step2 raw2889step2Labels raw2889step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2890 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2890step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2890step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2890step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2890 raw2890Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw2890 raw2890Labels = mixedMoment B raw2890step0 raw2890step0Labels := by
      have hz : ∀ j, raw2890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2890step0 = (fun i j => raw2890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2890step0 raw2890; decide +kernel
      have hl : raw2890step0Labels = raw2890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2890 raw2890Labels permutation434 hz
    mixedMoment B raw2890step0 raw2890step0Labels = mixedMoment B raw2890step1 raw2890step1Labels := by
      have hz : ∀ j, raw2890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2890step1 = (fun i j => raw2890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2890step1 raw2890step0; decide +kernel
      have hl : raw2890step1Labels = raw2890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2890step0 raw2890step0Labels permutation80 hz
    mixedMoment B raw2890step1 raw2890step1Labels = mixedMoment B raw2890step2 raw2890step2Labels := by
      have ha : raw2890step2 = (fun i j => raw2890step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2890step2 raw2890step1; decide +kernel
      have hl : raw2890step2Labels = raw2890step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2890step1 raw2890step1Labels permutation10 permutation6
    mixedMoment B raw2890step2 raw2890step2Labels = mixedMoment B raw2890step3 raw2890step3Labels := by
      have ha : raw2890step3 = raw2890step2 := by apply Matrix.ext; unfold raw2890step3 raw2890step2; decide +kernel
      have hl : raw2890step2Labels = labelEmbedding9 ∘ raw2890step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2890step2 raw2890step2Labels raw2890step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw2891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2891step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2891step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2891 raw2891Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw2891 raw2891Labels = mixedMoment B raw2891step0 raw2891step0Labels := by
      have hz : ∀ j, raw2891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2891step0 = (fun i j => raw2891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2891step0 raw2891; decide +kernel
      have hl : raw2891step0Labels = raw2891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2891 raw2891Labels permutation434 hz
    mixedMoment B raw2891step0 raw2891step0Labels = mixedMoment B raw2891step1 raw2891step1Labels := by
      have hz : ∀ j, raw2891step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2891step1 = (fun i j => raw2891step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2891step1 raw2891step0; decide +kernel
      have hl : raw2891step1Labels = raw2891step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2891step0 raw2891step0Labels permutation56 hz
    mixedMoment B raw2891step1 raw2891step1Labels = mixedMoment B raw2891step2 raw2891step2Labels := by
      have ha : raw2891step2 = (fun i j => raw2891step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2891step2 raw2891step1; decide +kernel
      have hl : raw2891step2Labels = raw2891step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2891step1 raw2891step1Labels permutation29 permutation4
    mixedMoment B raw2891step2 raw2891step2Labels = mixedMoment B raw2891step3 raw2891step3Labels := by
      have ha : raw2891step3 = raw2891step2 := by apply Matrix.ext; unfold raw2891step3 raw2891step2; decide +kernel
      have hl : raw2891step2Labels = labelEmbedding7 ∘ raw2891step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2891step2 raw2891step2Labels raw2891step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw2892 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2892step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2892 raw2892Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2892 raw2892Labels = mixedMoment B raw2892step0 raw2892step0Labels := by
      have hz : ∀ j, raw2892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2892step0 = (fun i j => raw2892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2892step0 raw2892; decide +kernel
      have hl : raw2892step0Labels = raw2892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2892 raw2892Labels permutation434 hz
    mixedMoment B raw2892step0 raw2892step0Labels = mixedMoment B raw2892step1 raw2892step1Labels := by
      have ha : raw2892step1 = (fun i j => raw2892step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2892step1 raw2892step0; decide +kernel
      have hl : raw2892step1Labels = raw2892step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2892step0 raw2892step0Labels permutation143 permutation4
    mixedMoment B raw2892step1 raw2892step1Labels = mixedMoment B raw2892step2 raw2892step2Labels := by
      have ha : raw2892step2 = raw2892step1 := by apply Matrix.ext; unfold raw2892step2 raw2892step1; decide +kernel
      have hl : raw2892step1Labels = labelEmbedding7 ∘ raw2892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2892step1 raw2892step1Labels raw2892step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2893 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2893step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2893 raw2893Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2893 raw2893Labels = mixedMoment B raw2893step0 raw2893step0Labels := by
      have hz : ∀ j, raw2893 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2893step0 = (fun i j => raw2893 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2893step0 raw2893; decide +kernel
      have hl : raw2893step0Labels = raw2893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2893 raw2893Labels permutation265 hz
    mixedMoment B raw2893step0 raw2893step0Labels = mixedMoment B raw2893step1 raw2893step1Labels := by
      have ha : raw2893step1 = (fun i j => raw2893step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2893step1 raw2893step0; decide +kernel
      have hl : raw2893step1Labels = raw2893step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2893step0 raw2893step0Labels permutation137 permutation4
    mixedMoment B raw2893step1 raw2893step1Labels = mixedMoment B raw2893step2 raw2893step2Labels := by
      have ha : raw2893step2 = raw2893step1 := by apply Matrix.ext; unfold raw2893step2 raw2893step1; decide +kernel
      have hl : raw2893step1Labels = labelEmbedding7 ∘ raw2893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2893step1 raw2893step1Labels raw2893step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2894step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2894step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2894step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2894 raw2894Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2894 raw2894Labels = mixedMoment B raw2894step0 raw2894step0Labels := by
      have hz : ∀ j, raw2894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2894step0 = (fun i j => raw2894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2894step0 raw2894; decide +kernel
      have hl : raw2894step0Labels = raw2894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2894 raw2894Labels permutation434 hz
    mixedMoment B raw2894step0 raw2894step0Labels = mixedMoment B raw2894step1 raw2894step1Labels := by
      have hz : ∀ j, raw2894step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2894step1 = (fun i j => raw2894step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2894step1 raw2894step0; decide +kernel
      have hl : raw2894step1Labels = raw2894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2894step0 raw2894step0Labels permutation56 hz
    mixedMoment B raw2894step1 raw2894step1Labels = mixedMoment B raw2894step2 raw2894step2Labels := by
      have ha : raw2894step2 = (fun i j => raw2894step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2894step2 raw2894step1; decide +kernel
      have hl : raw2894step2Labels = raw2894step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2894step1 raw2894step1Labels permutation28 permutation4
    mixedMoment B raw2894step2 raw2894step2Labels = mixedMoment B raw2894step3 raw2894step3Labels := by
      have ha : raw2894step3 = raw2894step2 := by apply Matrix.ext; unfold raw2894step3 raw2894step2; decide +kernel
      have hl : raw2894step2Labels = labelEmbedding7 ∘ raw2894step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2894step2 raw2894step2Labels raw2894step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2895 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2895step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2895step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2895step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2895 raw2895Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw2895 raw2895Labels = mixedMoment B raw2895step0 raw2895step0Labels := by
      have hz : ∀ j, raw2895 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2895step0 = (fun i j => raw2895 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2895step0 raw2895; decide +kernel
      have hl : raw2895step0Labels = raw2895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2895 raw2895Labels permutation434 hz
    mixedMoment B raw2895step0 raw2895step0Labels = mixedMoment B raw2895step1 raw2895step1Labels := by
      have hz : ∀ j, raw2895step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2895step1 = (fun i j => raw2895step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2895step1 raw2895step0; decide +kernel
      have hl : raw2895step1Labels = raw2895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2895step0 raw2895step0Labels permutation56 hz
    mixedMoment B raw2895step1 raw2895step1Labels = mixedMoment B raw2895step2 raw2895step2Labels := by
      have ha : raw2895step2 = (fun i j => raw2895step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2895step2 raw2895step1; decide +kernel
      have hl : raw2895step2Labels = raw2895step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2895step1 raw2895step1Labels permutation10 permutation6
    mixedMoment B raw2895step2 raw2895step2Labels = mixedMoment B raw2895step3 raw2895step3Labels := by
      have ha : raw2895step3 = raw2895step2 := by apply Matrix.ext; unfold raw2895step3 raw2895step2; decide +kernel
      have hl : raw2895step2Labels = labelEmbedding9 ∘ raw2895step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2895step2 raw2895step2Labels raw2895step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw2896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2896step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2896 raw2896Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw2896 raw2896Labels = mixedMoment B raw2896step0 raw2896step0Labels := by
      have hz : ∀ j, raw2896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2896step0 = (fun i j => raw2896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2896step0 raw2896; decide +kernel
      have hl : raw2896step0Labels = raw2896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2896 raw2896Labels permutation346 hz
    mixedMoment B raw2896step0 raw2896step0Labels = mixedMoment B raw2896step1 raw2896step1Labels := by
      have hz : ∀ j, raw2896step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2896step1 = (fun i j => raw2896step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2896step1 raw2896step0; decide +kernel
      have hl : raw2896step1Labels = raw2896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2896step0 raw2896step0Labels permutation56 hz
    mixedMoment B raw2896step1 raw2896step1Labels = mixedMoment B raw2896step2 raw2896step2Labels := by
      have ha : raw2896step2 = (fun i j => raw2896step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2896step2 raw2896step1; decide +kernel
      have hl : raw2896step2Labels = raw2896step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2896step1 raw2896step1Labels permutation29 permutation4
    mixedMoment B raw2896step2 raw2896step2Labels = mixedMoment B raw2896step3 raw2896step3Labels := by
      have ha : raw2896step3 = raw2896step2 := by apply Matrix.ext; unfold raw2896step3 raw2896step2; decide +kernel
      have hl : raw2896step2Labels = labelEmbedding7 ∘ raw2896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2896step2 raw2896step2Labels raw2896step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw2897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2897 raw2897Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2897 raw2897Labels = mixedMoment B raw2897step0 raw2897step0Labels := by
      have hz : ∀ j, raw2897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2897step0 = (fun i j => raw2897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2897step0 raw2897; decide +kernel
      have hl : raw2897step0Labels = raw2897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2897 raw2897Labels permutation346 hz
    mixedMoment B raw2897step0 raw2897step0Labels = mixedMoment B raw2897step1 raw2897step1Labels := by
      have ha : raw2897step1 = (fun i j => raw2897step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2897step1 raw2897step0; decide +kernel
      have hl : raw2897step1Labels = raw2897step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2897step0 raw2897step0Labels permutation143 permutation4
    mixedMoment B raw2897step1 raw2897step1Labels = mixedMoment B raw2897step2 raw2897step2Labels := by
      have ha : raw2897step2 = raw2897step1 := by apply Matrix.ext; unfold raw2897step2 raw2897step1; decide +kernel
      have hl : raw2897step1Labels = labelEmbedding7 ∘ raw2897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2897step1 raw2897step1Labels raw2897step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2898step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2898 raw2898Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2898 raw2898Labels = mixedMoment B raw2898step0 raw2898step0Labels := by
      have hz : ∀ j, raw2898 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2898step0 = (fun i j => raw2898 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2898step0 raw2898; decide +kernel
      have hl : raw2898step0Labels = raw2898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2898 raw2898Labels permutation265 hz
    mixedMoment B raw2898step0 raw2898step0Labels = mixedMoment B raw2898step1 raw2898step1Labels := by
      have ha : raw2898step1 = (fun i j => raw2898step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2898step1 raw2898step0; decide +kernel
      have hl : raw2898step1Labels = raw2898step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2898step0 raw2898step0Labels permutation143 permutation4
    mixedMoment B raw2898step1 raw2898step1Labels = mixedMoment B raw2898step2 raw2898step2Labels := by
      have ha : raw2898step2 = raw2898step1 := by apply Matrix.ext; unfold raw2898step2 raw2898step1; decide +kernel
      have hl : raw2898step1Labels = labelEmbedding7 ∘ raw2898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2898step1 raw2898step1Labels raw2898step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2]]
def raw2899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2899step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2899step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2899step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2899step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2899 raw2899Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2899 raw2899Labels = mixedMoment B raw2899step0 raw2899step0Labels := by
      have hz : ∀ j, raw2899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2899step0 = (fun i j => raw2899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2899step0 raw2899; decide +kernel
      have hl : raw2899step0Labels = raw2899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2899 raw2899Labels permutation346 hz
    mixedMoment B raw2899step0 raw2899step0Labels = mixedMoment B raw2899step1 raw2899step1Labels := by
      have hz : ∀ j, raw2899step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2899step1 = (fun i j => raw2899step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2899step1 raw2899step0; decide +kernel
      have hl : raw2899step1Labels = raw2899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2899step0 raw2899step0Labels permutation56 hz
    mixedMoment B raw2899step1 raw2899step1Labels = mixedMoment B raw2899step2 raw2899step2Labels := by
      have ha : raw2899step2 = (fun i j => raw2899step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2899step2 raw2899step1; decide +kernel
      have hl : raw2899step2Labels = raw2899step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2899step1 raw2899step1Labels permutation28 permutation4
    mixedMoment B raw2899step2 raw2899step2Labels = mixedMoment B raw2899step3 raw2899step3Labels := by
      have ha : raw2899step3 = raw2899step2 := by apply Matrix.ext; unfold raw2899step3 raw2899step2; decide +kernel
      have hl : raw2899step2Labels = labelEmbedding7 ∘ raw2899step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2899step2 raw2899step2Labels raw2899step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2900 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2900step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2900step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2900 raw2900Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw2900 raw2900Labels = mixedMoment B raw2900step0 raw2900step0Labels := by
      have hz : ∀ j, raw2900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2900step0 = (fun i j => raw2900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2900step0 raw2900; decide +kernel
      have hl : raw2900step0Labels = raw2900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2900 raw2900Labels permutation346 hz
    mixedMoment B raw2900step0 raw2900step0Labels = mixedMoment B raw2900step1 raw2900step1Labels := by
      have hz : ∀ j, raw2900step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2900step1 = (fun i j => raw2900step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2900step1 raw2900step0; decide +kernel
      have hl : raw2900step1Labels = raw2900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2900step0 raw2900step0Labels permutation56 hz
    mixedMoment B raw2900step1 raw2900step1Labels = mixedMoment B raw2900step2 raw2900step2Labels := by
      have ha : raw2900step2 = (fun i j => raw2900step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2900step2 raw2900step1; decide +kernel
      have hl : raw2900step2Labels = raw2900step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2900step1 raw2900step1Labels permutation10 permutation6
    mixedMoment B raw2900step2 raw2900step2Labels = mixedMoment B raw2900step3 raw2900step3Labels := by
      have ha : raw2900step3 = raw2900step2 := by apply Matrix.ext; unfold raw2900step3 raw2900step2; decide +kernel
      have hl : raw2900step2Labels = labelEmbedding9 ∘ raw2900step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2900step2 raw2900step2Labels raw2900step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw2901 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, -2, 2]]
def raw2901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 2, -2], ![0, -2, 2]]
def raw2901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2901step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![2, -2], ![-2, 2]]
def raw2901step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw2901step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw2901step5Labels : Fin 2 → Fin 3 := ![1, 2]

def raw2901step6 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw2901step6Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2901 raw2901Labels = mixedMoment B node4094 node4094Labels := by
  calc
    mixedMoment B raw2901 raw2901Labels = mixedMoment B raw2901step0 raw2901step0Labels := by
      have hz : ∀ j, raw2901 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2901step0 = (fun i j => raw2901 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2901step0 raw2901; decide +kernel
      have hl : raw2901step0Labels = raw2901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2901 raw2901Labels permutation520 hz
    mixedMoment B raw2901step0 raw2901step0Labels = mixedMoment B raw2901step1 raw2901step1Labels := by
      have hz : ∀ j, raw2901step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2901step1 = (fun i j => raw2901step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2901step1 raw2901step0; decide +kernel
      have hl : raw2901step1Labels = raw2901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2901step0 raw2901step0Labels permutation104 hz
    mixedMoment B raw2901step1 raw2901step1Labels = mixedMoment B raw2901step2 raw2901step2Labels := by
      have hz : ∀ j, raw2901step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2901step2 = (fun i j => raw2901step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2901step2 raw2901step1; decide +kernel
      have hl : raw2901step2Labels = raw2901step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2901step1 raw2901step1Labels permutation20 hz
    mixedMoment B raw2901step2 raw2901step2Labels = mixedMoment B raw2901step3 raw2901step3Labels := by
      have hz : ∀ j, raw2901step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2901step3 = (fun i j => raw2901step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2901step3 raw2901step2; decide +kernel
      have hl : raw2901step3Labels = raw2901step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2901step2 raw2901step2Labels permutation4 hz
    mixedMoment B raw2901step3 raw2901step3Labels = mixedMoment B raw2901step4 raw2901step4Labels := by
      have hz : ∀ i, raw2901step3 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw2901step4 = (fun i j => raw2901step3 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw2901step4 raw2901step3; decide +kernel
      have hl : raw2901step4Labels = (fun j => raw2901step3Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2901step3 raw2901step3Labels permutation2 hz
    mixedMoment B raw2901step4 raw2901step4Labels = mixedMoment B raw2901step5 raw2901step5Labels := by
      have ha : raw2901step5 = (fun i j => raw2901step4 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2901step5 raw2901step4; decide +kernel
      have hl : raw2901step5Labels = raw2901step4Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2901step4 raw2901step4Labels permutation1 permutation0
    mixedMoment B raw2901step5 raw2901step5Labels = mixedMoment B raw2901step6 raw2901step6Labels := by
      have ha : raw2901step6 = raw2901step5 := by apply Matrix.ext; unfold raw2901step6 raw2901step5; decide +kernel
      have hl : raw2901step5Labels = labelEmbedding3 ∘ raw2901step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2901step5 raw2901step5Labels raw2901step6Labels labelEmbedding3 hl
    _ = mixedMoment B node4094 node4094Labels := by rfl

def raw2902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -2, 2]]
def raw2902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2902step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2902step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2902step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2902step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2902step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2902step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2902 raw2902Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2902 raw2902Labels = mixedMoment B raw2902step0 raw2902step0Labels := by
      have hz : ∀ j, raw2902 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2902step0 = (fun i j => raw2902 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2902step0 raw2902; decide +kernel
      have hl : raw2902step0Labels = raw2902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2902 raw2902Labels permutation520 hz
    mixedMoment B raw2902step0 raw2902step0Labels = mixedMoment B raw2902step1 raw2902step1Labels := by
      have hz : ∀ j, raw2902step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2902step1 = (fun i j => raw2902step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2902step1 raw2902step0; decide +kernel
      have hl : raw2902step1Labels = raw2902step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2902step0 raw2902step0Labels permutation104 hz
    mixedMoment B raw2902step1 raw2902step1Labels = mixedMoment B raw2902step2 raw2902step2Labels := by
      have hz : ∀ j, raw2902step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2902step2 = (fun i j => raw2902step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2902step2 raw2902step1; decide +kernel
      have hl : raw2902step2Labels = raw2902step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2902step1 raw2902step1Labels permutation14 hz
    mixedMoment B raw2902step2 raw2902step2Labels = mixedMoment B raw2902step3 raw2902step3Labels := by
      have ha : raw2902step3 = (fun i j => raw2902step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2902step3 raw2902step2; decide +kernel
      have hl : raw2902step3Labels = raw2902step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2902step2 raw2902step2Labels permutation7 permutation6
    mixedMoment B raw2902step3 raw2902step3Labels = mixedMoment B raw2902step4 raw2902step4Labels := by
      have ha : raw2902step4 = -raw2902step3 := by apply Matrix.ext; change ∀ i j, raw2902step4 i j = -(raw2902step3 i j); unfold raw2902step4 raw2902step3; decide +kernel
      have hl : raw2902step4Labels = raw2902step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2902step4 raw2902step4Labels = mixedMoment B raw2902step5 raw2902step5Labels := by
      have ha : raw2902step5 = raw2902step4 := by apply Matrix.ext; unfold raw2902step5 raw2902step4; decide +kernel
      have hl : raw2902step4Labels = labelEmbedding9 ∘ raw2902step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2902step4 raw2902step4Labels raw2902step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw2903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2]]
def raw2903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2]]
def raw2903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -2, 2]]
def raw2903step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2903step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2903step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2903step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2903step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2903step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2903step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2903 raw2903Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2903 raw2903Labels = mixedMoment B raw2903step0 raw2903step0Labels := by
      have hz : ∀ j, raw2903 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2903step0 = (fun i j => raw2903 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2903step0 raw2903; decide +kernel
      have hl : raw2903step0Labels = raw2903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2903 raw2903Labels permutation520 hz
    mixedMoment B raw2903step0 raw2903step0Labels = mixedMoment B raw2903step1 raw2903step1Labels := by
      have hz : ∀ j, raw2903step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2903step1 = (fun i j => raw2903step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2903step1 raw2903step0; decide +kernel
      have hl : raw2903step1Labels = raw2903step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2903step0 raw2903step0Labels permutation80 hz
    mixedMoment B raw2903step1 raw2903step1Labels = mixedMoment B raw2903step2 raw2903step2Labels := by
      have hz : ∀ j, raw2903step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2903step2 = (fun i j => raw2903step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2903step2 raw2903step1; decide +kernel
      have hl : raw2903step2Labels = raw2903step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2903step1 raw2903step1Labels permutation14 hz
    mixedMoment B raw2903step2 raw2903step2Labels = mixedMoment B raw2903step3 raw2903step3Labels := by
      have ha : raw2903step3 = (fun i j => raw2903step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2903step3 raw2903step2; decide +kernel
      have hl : raw2903step3Labels = raw2903step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2903step2 raw2903step2Labels permutation7 permutation6
    mixedMoment B raw2903step3 raw2903step3Labels = mixedMoment B raw2903step4 raw2903step4Labels := by
      have ha : raw2903step4 = -raw2903step3 := by apply Matrix.ext; change ∀ i j, raw2903step4 i j = -(raw2903step3 i j); unfold raw2903step4 raw2903step3; decide +kernel
      have hl : raw2903step4Labels = raw2903step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2903step4 raw2903step4Labels = mixedMoment B raw2903step5 raw2903step5Labels := by
      have ha : raw2903step5 = raw2903step4 := by apply Matrix.ext; unfold raw2903step5 raw2903step4; decide +kernel
      have hl : raw2903step4Labels = labelEmbedding9 ∘ raw2903step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2903step4 raw2903step4Labels raw2903step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw2904 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -3, 2]]
def raw2904step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2904step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw2904step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2904step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw2904step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2904 raw2904Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw2904 raw2904Labels = mixedMoment B raw2904step0 raw2904step0Labels := by
      have hz : ∀ j, raw2904 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2904step0 = (fun i j => raw2904 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2904step0 raw2904; decide +kernel
      have hl : raw2904step0Labels = raw2904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2904 raw2904Labels permutation434 hz
    mixedMoment B raw2904step0 raw2904step0Labels = mixedMoment B raw2904step1 raw2904step1Labels := by
      have hz : ∀ j, raw2904step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2904step1 = (fun i j => raw2904step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2904step1 raw2904step0; decide +kernel
      have hl : raw2904step1Labels = raw2904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2904step0 raw2904step0Labels permutation80 hz
    mixedMoment B raw2904step1 raw2904step1Labels = mixedMoment B raw2904step2 raw2904step2Labels := by
      have hz : ∀ j, raw2904step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2904step2 = (fun i j => raw2904step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2904step2 raw2904step1; decide +kernel
      have hl : raw2904step2Labels = raw2904step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2904step1 raw2904step1Labels permutation14 hz
    mixedMoment B raw2904step2 raw2904step2Labels = mixedMoment B raw2904step3 raw2904step3Labels := by
      have ha : raw2904step3 = (fun i j => raw2904step2 (permutation7 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2904step3 raw2904step2; decide +kernel
      have hl : raw2904step3Labels = raw2904step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2904step2 raw2904step2Labels permutation7 permutation4
    mixedMoment B raw2904step3 raw2904step3Labels = mixedMoment B raw2904step4 raw2904step4Labels := by
      have ha : raw2904step4 = raw2904step3 := by apply Matrix.ext; unfold raw2904step4 raw2904step3; decide +kernel
      have hl : raw2904step3Labels = labelEmbedding7 ∘ raw2904step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2904step3 raw2904step3Labels raw2904step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw2905 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2905step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2905step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2905step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2905 raw2905Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw2905 raw2905Labels = mixedMoment B raw2905step0 raw2905step0Labels := by
      have hz : ∀ j, raw2905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2905step0 = (fun i j => raw2905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2905step0 raw2905; decide +kernel
      have hl : raw2905step0Labels = raw2905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2905 raw2905Labels permutation434 hz
    mixedMoment B raw2905step0 raw2905step0Labels = mixedMoment B raw2905step1 raw2905step1Labels := by
      have hz : ∀ j, raw2905step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2905step1 = (fun i j => raw2905step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2905step1 raw2905step0; decide +kernel
      have hl : raw2905step1Labels = raw2905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2905step0 raw2905step0Labels permutation80 hz
    mixedMoment B raw2905step1 raw2905step1Labels = mixedMoment B raw2905step2 raw2905step2Labels := by
      have ha : raw2905step2 = (fun i j => raw2905step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2905step2 raw2905step1; decide +kernel
      have hl : raw2905step2Labels = raw2905step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2905step1 raw2905step1Labels permutation29 permutation4
    mixedMoment B raw2905step2 raw2905step2Labels = mixedMoment B raw2905step3 raw2905step3Labels := by
      have ha : raw2905step3 = raw2905step2 := by apply Matrix.ext; unfold raw2905step3 raw2905step2; decide +kernel
      have hl : raw2905step2Labels = labelEmbedding7 ∘ raw2905step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2905step2 raw2905step2Labels raw2905step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw2906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2906step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2906step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2906step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2906 raw2906Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw2906 raw2906Labels = mixedMoment B raw2906step0 raw2906step0Labels := by
      have hz : ∀ j, raw2906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2906step0 = (fun i j => raw2906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2906step0 raw2906; decide +kernel
      have hl : raw2906step0Labels = raw2906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2906 raw2906Labels permutation434 hz
    mixedMoment B raw2906step0 raw2906step0Labels = mixedMoment B raw2906step1 raw2906step1Labels := by
      have hz : ∀ j, raw2906step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2906step1 = (fun i j => raw2906step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2906step1 raw2906step0; decide +kernel
      have hl : raw2906step1Labels = raw2906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2906step0 raw2906step0Labels permutation56 hz
    mixedMoment B raw2906step1 raw2906step1Labels = mixedMoment B raw2906step2 raw2906step2Labels := by
      have ha : raw2906step2 = (fun i j => raw2906step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2906step2 raw2906step1; decide +kernel
      have hl : raw2906step2Labels = raw2906step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2906step1 raw2906step1Labels permutation29 permutation4
    mixedMoment B raw2906step2 raw2906step2Labels = mixedMoment B raw2906step3 raw2906step3Labels := by
      have ha : raw2906step3 = raw2906step2 := by apply Matrix.ext; unfold raw2906step3 raw2906step2; decide +kernel
      have hl : raw2906step2Labels = labelEmbedding7 ∘ raw2906step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2906step2 raw2906step2Labels raw2906step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw2907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2907step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2]]
def raw2907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2907step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2907step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2907step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2907step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2907 raw2907Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw2907 raw2907Labels = mixedMoment B raw2907step0 raw2907step0Labels := by
      have hz : ∀ j, raw2907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2907step0 = (fun i j => raw2907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2907step0 raw2907; decide +kernel
      have hl : raw2907step0Labels = raw2907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2907 raw2907Labels permutation346 hz
    mixedMoment B raw2907step0 raw2907step0Labels = mixedMoment B raw2907step1 raw2907step1Labels := by
      have hz : ∀ j, raw2907step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2907step1 = (fun i j => raw2907step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2907step1 raw2907step0; decide +kernel
      have hl : raw2907step1Labels = raw2907step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2907step0 raw2907step0Labels permutation56 hz
    mixedMoment B raw2907step1 raw2907step1Labels = mixedMoment B raw2907step2 raw2907step2Labels := by
      have ha : raw2907step2 = (fun i j => raw2907step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2907step2 raw2907step1; decide +kernel
      have hl : raw2907step2Labels = raw2907step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2907step1 raw2907step1Labels permutation29 permutation4
    mixedMoment B raw2907step2 raw2907step2Labels = mixedMoment B raw2907step3 raw2907step3Labels := by
      have ha : raw2907step3 = raw2907step2 := by apply Matrix.ext; unfold raw2907step3 raw2907step2; decide +kernel
      have hl : raw2907step2Labels = labelEmbedding7 ∘ raw2907step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2907step2 raw2907step2Labels raw2907step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw2908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2]]
def raw2908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2]]
def raw2908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2]]
def raw2908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -3, 2]]
def raw2908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2908step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2908step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2908step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2908step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2908 raw2908Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2908 raw2908Labels = mixedMoment B raw2908step0 raw2908step0Labels := by
      have hz : ∀ j, raw2908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2908step0 = (fun i j => raw2908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2908step0 raw2908; decide +kernel
      have hl : raw2908step0Labels = raw2908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2908 raw2908Labels permutation434 hz
    mixedMoment B raw2908step0 raw2908step0Labels = mixedMoment B raw2908step1 raw2908step1Labels := by
      have hz : ∀ j, raw2908step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2908step1 = (fun i j => raw2908step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2908step1 raw2908step0; decide +kernel
      have hl : raw2908step1Labels = raw2908step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2908step0 raw2908step0Labels permutation80 hz
    mixedMoment B raw2908step1 raw2908step1Labels = mixedMoment B raw2908step2 raw2908step2Labels := by
      have hz : ∀ j, raw2908step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2908step2 = (fun i j => raw2908step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2908step2 raw2908step1; decide +kernel
      have hl : raw2908step2Labels = raw2908step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2908step1 raw2908step1Labels permutation14 hz
    mixedMoment B raw2908step2 raw2908step2Labels = mixedMoment B raw2908step3 raw2908step3Labels := by
      have ha : raw2908step3 = (fun i j => raw2908step2 (permutation6 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2908step3 raw2908step2; decide +kernel
      have hl : raw2908step3Labels = raw2908step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2908step2 raw2908step2Labels permutation6 permutation4
    mixedMoment B raw2908step3 raw2908step3Labels = mixedMoment B raw2908step4 raw2908step4Labels := by
      have ha : raw2908step4 = raw2908step3 := by apply Matrix.ext; unfold raw2908step4 raw2908step3; decide +kernel
      have hl : raw2908step3Labels = labelEmbedding7 ∘ raw2908step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2908step3 raw2908step3Labels raw2908step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw2909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2909step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2909step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2909step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2909step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2909step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2909step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2909step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2909step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2909 raw2909Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2909 raw2909Labels = mixedMoment B raw2909step0 raw2909step0Labels := by
      have hz : ∀ j, raw2909 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2909step0 = (fun i j => raw2909 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2909step0 raw2909; decide +kernel
      have hl : raw2909step0Labels = raw2909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2909 raw2909Labels permutation520 hz
    mixedMoment B raw2909step0 raw2909step0Labels = mixedMoment B raw2909step1 raw2909step1Labels := by
      have hz : ∀ j, raw2909step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2909step1 = (fun i j => raw2909step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2909step1 raw2909step0; decide +kernel
      have hl : raw2909step1Labels = raw2909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2909step0 raw2909step0Labels permutation104 hz
    mixedMoment B raw2909step1 raw2909step1Labels = mixedMoment B raw2909step2 raw2909step2Labels := by
      have hz : ∀ j, raw2909step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2909step2 = (fun i j => raw2909step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2909step2 raw2909step1; decide +kernel
      have hl : raw2909step2Labels = raw2909step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2909step1 raw2909step1Labels permutation20 hz
    mixedMoment B raw2909step2 raw2909step2Labels = mixedMoment B raw2909step3 raw2909step3Labels := by
      have hz : ∀ i, raw2909step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2909step3 = (fun i j => raw2909step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2909step3 raw2909step2; decide +kernel
      have hl : raw2909step3Labels = (fun j => raw2909step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2909step2 raw2909step2Labels permutation6 hz
    mixedMoment B raw2909step3 raw2909step3Labels = mixedMoment B raw2909step4 raw2909step4Labels := by
      have ha : raw2909step4 = (fun i j => raw2909step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2909step4 raw2909step3; decide +kernel
      have hl : raw2909step4Labels = raw2909step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2909step3 raw2909step3Labels permutation6 permutation0
    mixedMoment B raw2909step4 raw2909step4Labels = mixedMoment B raw2909step5 raw2909step5Labels := by
      have ha : raw2909step5 = -raw2909step4 := by apply Matrix.ext; change ∀ i j, raw2909step5 i j = -(raw2909step4 i j); unfold raw2909step5 raw2909step4; decide +kernel
      have hl : raw2909step5Labels = raw2909step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw2910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2910step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2910step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2910step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2910step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2910step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2910step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2910step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2910step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2910 raw2910Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2910 raw2910Labels = mixedMoment B raw2910step0 raw2910step0Labels := by
      have hz : ∀ j, raw2910 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2910step0 = (fun i j => raw2910 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2910step0 raw2910; decide +kernel
      have hl : raw2910step0Labels = raw2910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2910 raw2910Labels permutation520 hz
    mixedMoment B raw2910step0 raw2910step0Labels = mixedMoment B raw2910step1 raw2910step1Labels := by
      have hz : ∀ j, raw2910step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2910step1 = (fun i j => raw2910step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2910step1 raw2910step0; decide +kernel
      have hl : raw2910step1Labels = raw2910step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2910step0 raw2910step0Labels permutation104 hz
    mixedMoment B raw2910step1 raw2910step1Labels = mixedMoment B raw2910step2 raw2910step2Labels := by
      have hz : ∀ j, raw2910step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2910step2 = (fun i j => raw2910step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2910step2 raw2910step1; decide +kernel
      have hl : raw2910step2Labels = raw2910step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2910step1 raw2910step1Labels permutation14 hz
    mixedMoment B raw2910step2 raw2910step2Labels = mixedMoment B raw2910step3 raw2910step3Labels := by
      have hz : ∀ i, raw2910step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2910step3 = (fun i j => raw2910step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2910step3 raw2910step2; decide +kernel
      have hl : raw2910step3Labels = (fun j => raw2910step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2910step2 raw2910step2Labels permutation6 hz
    mixedMoment B raw2910step3 raw2910step3Labels = mixedMoment B raw2910step4 raw2910step4Labels := by
      have ha : raw2910step4 = (fun i j => raw2910step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2910step4 raw2910step3; decide +kernel
      have hl : raw2910step4Labels = raw2910step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2910step3 raw2910step3Labels permutation6 permutation0
    mixedMoment B raw2910step4 raw2910step4Labels = mixedMoment B raw2910step5 raw2910step5Labels := by
      have ha : raw2910step5 = -raw2910step4 := by apply Matrix.ext; change ∀ i j, raw2910step5 i j = -(raw2910step4 i j); unfold raw2910step5 raw2910step4; decide +kernel
      have hl : raw2910step5Labels = raw2910step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw2911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2911step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2911step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2911step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2911step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2911step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2911step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2911step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2911step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2911 raw2911Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2911 raw2911Labels = mixedMoment B raw2911step0 raw2911step0Labels := by
      have hz : ∀ j, raw2911 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2911step0 = (fun i j => raw2911 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2911step0 raw2911; decide +kernel
      have hl : raw2911step0Labels = raw2911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2911 raw2911Labels permutation520 hz
    mixedMoment B raw2911step0 raw2911step0Labels = mixedMoment B raw2911step1 raw2911step1Labels := by
      have hz : ∀ j, raw2911step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2911step1 = (fun i j => raw2911step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2911step1 raw2911step0; decide +kernel
      have hl : raw2911step1Labels = raw2911step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2911step0 raw2911step0Labels permutation80 hz
    mixedMoment B raw2911step1 raw2911step1Labels = mixedMoment B raw2911step2 raw2911step2Labels := by
      have hz : ∀ j, raw2911step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2911step2 = (fun i j => raw2911step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2911step2 raw2911step1; decide +kernel
      have hl : raw2911step2Labels = raw2911step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2911step1 raw2911step1Labels permutation14 hz
    mixedMoment B raw2911step2 raw2911step2Labels = mixedMoment B raw2911step3 raw2911step3Labels := by
      have hz : ∀ i, raw2911step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2911step3 = (fun i j => raw2911step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2911step3 raw2911step2; decide +kernel
      have hl : raw2911step3Labels = (fun j => raw2911step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2911step2 raw2911step2Labels permutation6 hz
    mixedMoment B raw2911step3 raw2911step3Labels = mixedMoment B raw2911step4 raw2911step4Labels := by
      have ha : raw2911step4 = (fun i j => raw2911step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2911step4 raw2911step3; decide +kernel
      have hl : raw2911step4Labels = raw2911step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2911step3 raw2911step3Labels permutation6 permutation0
    mixedMoment B raw2911step4 raw2911step4Labels = mixedMoment B raw2911step5 raw2911step5Labels := by
      have ha : raw2911step5 = -raw2911step4 := by apply Matrix.ext; change ∀ i j, raw2911step5 i j = -(raw2911step4 i j); unfold raw2911step5 raw2911step4; decide +kernel
      have hl : raw2911step5Labels = raw2911step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw2912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2912step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2912step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw2912step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2912step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw2912step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2912step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2912step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2912 raw2912Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2912 raw2912Labels = mixedMoment B raw2912step0 raw2912step0Labels := by
      have hz : ∀ j, raw2912 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2912step0 = (fun i j => raw2912 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2912step0 raw2912; decide +kernel
      have hl : raw2912step0Labels = raw2912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2912 raw2912Labels permutation434 hz
    mixedMoment B raw2912step0 raw2912step0Labels = mixedMoment B raw2912step1 raw2912step1Labels := by
      have hz : ∀ j, raw2912step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2912step1 = (fun i j => raw2912step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2912step1 raw2912step0; decide +kernel
      have hl : raw2912step1Labels = raw2912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2912step0 raw2912step0Labels permutation80 hz
    mixedMoment B raw2912step1 raw2912step1Labels = mixedMoment B raw2912step2 raw2912step2Labels := by
      have hz : ∀ j, raw2912step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2912step2 = (fun i j => raw2912step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2912step2 raw2912step1; decide +kernel
      have hl : raw2912step2Labels = raw2912step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2912step1 raw2912step1Labels permutation14 hz
    mixedMoment B raw2912step2 raw2912step2Labels = mixedMoment B raw2912step3 raw2912step3Labels := by
      have hz : ∀ i, raw2912step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2912step3 = (fun i j => raw2912step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2912step3 raw2912step2; decide +kernel
      have hl : raw2912step3Labels = (fun j => raw2912step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2912step2 raw2912step2Labels permutation6 hz
    mixedMoment B raw2912step3 raw2912step3Labels = mixedMoment B raw2912step4 raw2912step4Labels := by
      have ha : raw2912step4 = (fun i j => raw2912step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2912step4 raw2912step3; decide +kernel
      have hl : raw2912step4Labels = raw2912step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2912step3 raw2912step3Labels permutation6 permutation0
    mixedMoment B raw2912step4 raw2912step4Labels = mixedMoment B raw2912step5 raw2912step5Labels := by
      have ha : raw2912step5 = -raw2912step4 := by apply Matrix.ext; change ∀ i j, raw2912step5 i j = -(raw2912step4 i j); unfold raw2912step5 raw2912step4; decide +kernel
      have hl : raw2912step5Labels = raw2912step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw2913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2913step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]
def raw2913step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2913step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def raw2913step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2913 raw2913Labels = mixedMoment B node4097 node4097Labels := by
  calc
    mixedMoment B raw2913 raw2913Labels = mixedMoment B raw2913step0 raw2913step0Labels := by
      have hz : ∀ j, raw2913 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2913step0 = (fun i j => raw2913 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2913step0 raw2913; decide +kernel
      have hl : raw2913step0Labels = raw2913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913 raw2913Labels permutation520 hz
    mixedMoment B raw2913step0 raw2913step0Labels = mixedMoment B raw2913step1 raw2913step1Labels := by
      have hz : ∀ j, raw2913step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2913step1 = (fun i j => raw2913step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2913step1 raw2913step0; decide +kernel
      have hl : raw2913step1Labels = raw2913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913step0 raw2913step0Labels permutation104 hz
    mixedMoment B raw2913step1 raw2913step1Labels = mixedMoment B raw2913step2 raw2913step2Labels := by
      have hz : ∀ j, raw2913step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2913step2 = (fun i j => raw2913step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2913step2 raw2913step1; decide +kernel
      have hl : raw2913step2Labels = raw2913step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913step1 raw2913step1Labels permutation20 hz
    mixedMoment B raw2913step2 raw2913step2Labels = mixedMoment B raw2913step3 raw2913step3Labels := by
      have hz : ∀ j, raw2913step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2913step3 = (fun i j => raw2913step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2913step3 raw2913step2; decide +kernel
      have hl : raw2913step3Labels = raw2913step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2913step2 raw2913step2Labels permutation4 hz
    mixedMoment B raw2913step3 raw2913step3Labels = mixedMoment B raw2913step4 raw2913step4Labels := by
      have hz : ∀ i, raw2913step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2913step4 = (fun i j => raw2913step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2913step4 raw2913step3; decide +kernel
      have hl : raw2913step4Labels = (fun j => raw2913step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2913step3 raw2913step3Labels permutation6 hz
    _ = mixedMoment B node4097 node4097Labels := by rfl

def raw2914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2914step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2914step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2914step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2914step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2914step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2914 raw2914Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2914 raw2914Labels = mixedMoment B raw2914step0 raw2914step0Labels := by
      have hz : ∀ j, raw2914 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2914step0 = (fun i j => raw2914 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2914step0 raw2914; decide +kernel
      have hl : raw2914step0Labels = raw2914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914 raw2914Labels permutation520 hz
    mixedMoment B raw2914step0 raw2914step0Labels = mixedMoment B raw2914step1 raw2914step1Labels := by
      have hz : ∀ j, raw2914step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2914step1 = (fun i j => raw2914step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2914step1 raw2914step0; decide +kernel
      have hl : raw2914step1Labels = raw2914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914step0 raw2914step0Labels permutation104 hz
    mixedMoment B raw2914step1 raw2914step1Labels = mixedMoment B raw2914step2 raw2914step2Labels := by
      have hz : ∀ j, raw2914step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2914step2 = (fun i j => raw2914step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2914step2 raw2914step1; decide +kernel
      have hl : raw2914step2Labels = raw2914step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2914step1 raw2914step1Labels permutation20 hz
    mixedMoment B raw2914step2 raw2914step2Labels = mixedMoment B raw2914step3 raw2914step3Labels := by
      have hz : ∀ i, raw2914step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2914step3 = (fun i j => raw2914step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2914step3 raw2914step2; decide +kernel
      have hl : raw2914step3Labels = (fun j => raw2914step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2914step2 raw2914step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw2915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2915step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2915step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2915step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2915step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2915step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2915 raw2915Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2915 raw2915Labels = mixedMoment B raw2915step0 raw2915step0Labels := by
      have hz : ∀ j, raw2915 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2915step0 = (fun i j => raw2915 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2915step0 raw2915; decide +kernel
      have hl : raw2915step0Labels = raw2915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2915 raw2915Labels permutation520 hz
    mixedMoment B raw2915step0 raw2915step0Labels = mixedMoment B raw2915step1 raw2915step1Labels := by
      have hz : ∀ j, raw2915step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2915step1 = (fun i j => raw2915step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2915step1 raw2915step0; decide +kernel
      have hl : raw2915step1Labels = raw2915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2915step0 raw2915step0Labels permutation104 hz
    mixedMoment B raw2915step1 raw2915step1Labels = mixedMoment B raw2915step2 raw2915step2Labels := by
      have hz : ∀ i, raw2915step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2915step2 = (fun i j => raw2915step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2915step2 raw2915step1; decide +kernel
      have hl : raw2915step2Labels = (fun j => raw2915step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2915step1 raw2915step1Labels permutation6 hz
    mixedMoment B raw2915step2 raw2915step2Labels = mixedMoment B raw2915step3 raw2915step3Labels := by
      have ha : raw2915step3 = (fun i j => raw2915step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2915step3 raw2915step2; decide +kernel
      have hl : raw2915step3Labels = raw2915step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2915step2 raw2915step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2916step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2916step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2916step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2916step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2916step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2916 raw2916Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2916 raw2916Labels = mixedMoment B raw2916step0 raw2916step0Labels := by
      have hz : ∀ j, raw2916 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2916step0 = (fun i j => raw2916 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2916step0 raw2916; decide +kernel
      have hl : raw2916step0Labels = raw2916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2916 raw2916Labels permutation520 hz
    mixedMoment B raw2916step0 raw2916step0Labels = mixedMoment B raw2916step1 raw2916step1Labels := by
      have hz : ∀ j, raw2916step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2916step1 = (fun i j => raw2916step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2916step1 raw2916step0; decide +kernel
      have hl : raw2916step1Labels = raw2916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2916step0 raw2916step0Labels permutation80 hz
    mixedMoment B raw2916step1 raw2916step1Labels = mixedMoment B raw2916step2 raw2916step2Labels := by
      have hz : ∀ i, raw2916step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2916step2 = (fun i j => raw2916step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2916step2 raw2916step1; decide +kernel
      have hl : raw2916step2Labels = (fun j => raw2916step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2916step1 raw2916step1Labels permutation6 hz
    mixedMoment B raw2916step2 raw2916step2Labels = mixedMoment B raw2916step3 raw2916step3Labels := by
      have ha : raw2916step3 = (fun i j => raw2916step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2916step3 raw2916step2; decide +kernel
      have hl : raw2916step3Labels = raw2916step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2916step2 raw2916step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2917step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2917step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2917step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2917step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2917step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2917 raw2917Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2917 raw2917Labels = mixedMoment B raw2917step0 raw2917step0Labels := by
      have hz : ∀ j, raw2917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2917step0 = (fun i j => raw2917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2917step0 raw2917; decide +kernel
      have hl : raw2917step0Labels = raw2917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2917 raw2917Labels permutation434 hz
    mixedMoment B raw2917step0 raw2917step0Labels = mixedMoment B raw2917step1 raw2917step1Labels := by
      have hz : ∀ j, raw2917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2917step1 = (fun i j => raw2917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2917step1 raw2917step0; decide +kernel
      have hl : raw2917step1Labels = raw2917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2917step0 raw2917step0Labels permutation80 hz
    mixedMoment B raw2917step1 raw2917step1Labels = mixedMoment B raw2917step2 raw2917step2Labels := by
      have hz : ∀ i, raw2917step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2917step2 = (fun i j => raw2917step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2917step2 raw2917step1; decide +kernel
      have hl : raw2917step2Labels = (fun j => raw2917step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2917step1 raw2917step1Labels permutation6 hz
    mixedMoment B raw2917step2 raw2917step2Labels = mixedMoment B raw2917step3 raw2917step3Labels := by
      have ha : raw2917step3 = (fun i j => raw2917step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2917step3 raw2917step2; decide +kernel
      have hl : raw2917step3Labels = raw2917step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2917step2 raw2917step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2918step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2918step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2918step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2918step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2918step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2918 raw2918Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2918 raw2918Labels = mixedMoment B raw2918step0 raw2918step0Labels := by
      have hz : ∀ j, raw2918 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2918step0 = (fun i j => raw2918 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2918step0 raw2918; decide +kernel
      have hl : raw2918step0Labels = raw2918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2918 raw2918Labels permutation520 hz
    mixedMoment B raw2918step0 raw2918step0Labels = mixedMoment B raw2918step1 raw2918step1Labels := by
      have hz : ∀ j, raw2918step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2918step1 = (fun i j => raw2918step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2918step1 raw2918step0; decide +kernel
      have hl : raw2918step1Labels = raw2918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2918step0 raw2918step0Labels permutation104 hz
    mixedMoment B raw2918step1 raw2918step1Labels = mixedMoment B raw2918step2 raw2918step2Labels := by
      have hz : ∀ j, raw2918step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2918step2 = (fun i j => raw2918step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2918step2 raw2918step1; decide +kernel
      have hl : raw2918step2Labels = raw2918step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2918step1 raw2918step1Labels permutation20 hz
    mixedMoment B raw2918step2 raw2918step2Labels = mixedMoment B raw2918step3 raw2918step3Labels := by
      have hz : ∀ i, raw2918step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2918step3 = (fun i j => raw2918step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2918step3 raw2918step2; decide +kernel
      have hl : raw2918step3Labels = (fun j => raw2918step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2918step2 raw2918step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw2919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2919step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2919step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2919step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2919step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2919step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2919 raw2919Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2919 raw2919Labels = mixedMoment B raw2919step0 raw2919step0Labels := by
      have hz : ∀ j, raw2919 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2919step0 = (fun i j => raw2919 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2919step0 raw2919; decide +kernel
      have hl : raw2919step0Labels = raw2919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919 raw2919Labels permutation520 hz
    mixedMoment B raw2919step0 raw2919step0Labels = mixedMoment B raw2919step1 raw2919step1Labels := by
      have hz : ∀ j, raw2919step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2919step1 = (fun i j => raw2919step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2919step1 raw2919step0; decide +kernel
      have hl : raw2919step1Labels = raw2919step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919step0 raw2919step0Labels permutation104 hz
    mixedMoment B raw2919step1 raw2919step1Labels = mixedMoment B raw2919step2 raw2919step2Labels := by
      have hz : ∀ j, raw2919step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2919step2 = (fun i j => raw2919step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2919step2 raw2919step1; decide +kernel
      have hl : raw2919step2Labels = raw2919step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2919step1 raw2919step1Labels permutation14 hz
    mixedMoment B raw2919step2 raw2919step2Labels = mixedMoment B raw2919step3 raw2919step3Labels := by
      have hz : ∀ i, raw2919step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2919step3 = (fun i j => raw2919step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2919step3 raw2919step2; decide +kernel
      have hl : raw2919step3Labels = (fun j => raw2919step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2919step2 raw2919step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw2920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2920step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2920step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2920step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2920step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2920 raw2920Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2920 raw2920Labels = mixedMoment B raw2920step0 raw2920step0Labels := by
      have hz : ∀ j, raw2920 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2920step0 = (fun i j => raw2920 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2920step0 raw2920; decide +kernel
      have hl : raw2920step0Labels = raw2920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2920 raw2920Labels permutation520 hz
    mixedMoment B raw2920step0 raw2920step0Labels = mixedMoment B raw2920step1 raw2920step1Labels := by
      have hz : ∀ j, raw2920step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2920step1 = (fun i j => raw2920step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2920step1 raw2920step0; decide +kernel
      have hl : raw2920step1Labels = raw2920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2920step0 raw2920step0Labels permutation104 hz
    mixedMoment B raw2920step1 raw2920step1Labels = mixedMoment B raw2920step2 raw2920step2Labels := by
      have hz : ∀ i, raw2920step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2920step2 = (fun i j => raw2920step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2920step2 raw2920step1; decide +kernel
      have hl : raw2920step2Labels = (fun j => raw2920step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2920step1 raw2920step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2921step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2921step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2921step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2921step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2921step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2921step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2921 raw2921Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2921 raw2921Labels = mixedMoment B raw2921step0 raw2921step0Labels := by
      have hz : ∀ j, raw2921 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2921step0 = (fun i j => raw2921 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2921step0 raw2921; decide +kernel
      have hl : raw2921step0Labels = raw2921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2921 raw2921Labels permutation520 hz
    mixedMoment B raw2921step0 raw2921step0Labels = mixedMoment B raw2921step1 raw2921step1Labels := by
      have hz : ∀ j, raw2921step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2921step1 = (fun i j => raw2921step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2921step1 raw2921step0; decide +kernel
      have hl : raw2921step1Labels = raw2921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2921step0 raw2921step0Labels permutation56 hz
    mixedMoment B raw2921step1 raw2921step1Labels = mixedMoment B raw2921step2 raw2921step2Labels := by
      have hz : ∀ i, raw2921step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2921step2 = (fun i j => raw2921step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2921step2 raw2921step1; decide +kernel
      have hl : raw2921step2Labels = (fun j => raw2921step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2921step1 raw2921step1Labels permutation6 hz
    mixedMoment B raw2921step2 raw2921step2Labels = mixedMoment B raw2921step3 raw2921step3Labels := by
      have ha : raw2921step3 = (fun i j => raw2921step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2921step3 raw2921step2; decide +kernel
      have hl : raw2921step3Labels = raw2921step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2921step2 raw2921step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2922step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2922step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2922step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2922step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2922step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2922 raw2922Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2922 raw2922Labels = mixedMoment B raw2922step0 raw2922step0Labels := by
      have hz : ∀ j, raw2922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2922step0 = (fun i j => raw2922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2922step0 raw2922; decide +kernel
      have hl : raw2922step0Labels = raw2922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2922 raw2922Labels permutation434 hz
    mixedMoment B raw2922step0 raw2922step0Labels = mixedMoment B raw2922step1 raw2922step1Labels := by
      have hz : ∀ j, raw2922step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2922step1 = (fun i j => raw2922step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2922step1 raw2922step0; decide +kernel
      have hl : raw2922step1Labels = raw2922step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2922step0 raw2922step0Labels permutation56 hz
    mixedMoment B raw2922step1 raw2922step1Labels = mixedMoment B raw2922step2 raw2922step2Labels := by
      have hz : ∀ i, raw2922step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2922step2 = (fun i j => raw2922step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2922step2 raw2922step1; decide +kernel
      have hl : raw2922step2Labels = (fun j => raw2922step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2922step1 raw2922step1Labels permutation6 hz
    mixedMoment B raw2922step2 raw2922step2Labels = mixedMoment B raw2922step3 raw2922step3Labels := by
      have ha : raw2922step3 = (fun i j => raw2922step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2922step3 raw2922step2; decide +kernel
      have hl : raw2922step3Labels = raw2922step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2922step2 raw2922step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2923step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2923step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2923step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2923step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2923 raw2923Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2923 raw2923Labels = mixedMoment B raw2923step0 raw2923step0Labels := by
      have hz : ∀ j, raw2923 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2923step0 = (fun i j => raw2923 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2923step0 raw2923; decide +kernel
      have hl : raw2923step0Labels = raw2923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2923 raw2923Labels permutation520 hz
    mixedMoment B raw2923step0 raw2923step0Labels = mixedMoment B raw2923step1 raw2923step1Labels := by
      have hz : ∀ j, raw2923step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2923step1 = (fun i j => raw2923step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2923step1 raw2923step0; decide +kernel
      have hl : raw2923step1Labels = raw2923step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2923step0 raw2923step0Labels permutation104 hz
    mixedMoment B raw2923step1 raw2923step1Labels = mixedMoment B raw2923step2 raw2923step2Labels := by
      have hz : ∀ j, raw2923step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2923step2 = (fun i j => raw2923step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2923step2 raw2923step1; decide +kernel
      have hl : raw2923step2Labels = raw2923step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2923step1 raw2923step1Labels permutation14 hz
    mixedMoment B raw2923step2 raw2923step2Labels = mixedMoment B raw2923step3 raw2923step3Labels := by
      have hz : ∀ i, raw2923step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2923step3 = (fun i j => raw2923step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2923step3 raw2923step2; decide +kernel
      have hl : raw2923step3Labels = (fun j => raw2923step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2923step2 raw2923step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw2924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2924step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2924step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2924step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2924step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2924 raw2924Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2924 raw2924Labels = mixedMoment B raw2924step0 raw2924step0Labels := by
      have hz : ∀ j, raw2924 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2924step0 = (fun i j => raw2924 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2924step0 raw2924; decide +kernel
      have hl : raw2924step0Labels = raw2924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924 raw2924Labels permutation520 hz
    mixedMoment B raw2924step0 raw2924step0Labels = mixedMoment B raw2924step1 raw2924step1Labels := by
      have hz : ∀ j, raw2924step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2924step1 = (fun i j => raw2924step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2924step1 raw2924step0; decide +kernel
      have hl : raw2924step1Labels = raw2924step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step0 raw2924step0Labels permutation80 hz
    mixedMoment B raw2924step1 raw2924step1Labels = mixedMoment B raw2924step2 raw2924step2Labels := by
      have hz : ∀ j, raw2924step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2924step2 = (fun i j => raw2924step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2924step2 raw2924step1; decide +kernel
      have hl : raw2924step2Labels = raw2924step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2924step1 raw2924step1Labels permutation14 hz
    mixedMoment B raw2924step2 raw2924step2Labels = mixedMoment B raw2924step3 raw2924step3Labels := by
      have hz : ∀ i, raw2924step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2924step3 = (fun i j => raw2924step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2924step3 raw2924step2; decide +kernel
      have hl : raw2924step3Labels = (fun j => raw2924step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2924step2 raw2924step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw2925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2925step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2925step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2925step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2925step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2925 raw2925Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2925 raw2925Labels = mixedMoment B raw2925step0 raw2925step0Labels := by
      have hz : ∀ j, raw2925 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2925step0 = (fun i j => raw2925 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2925step0 raw2925; decide +kernel
      have hl : raw2925step0Labels = raw2925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2925 raw2925Labels permutation520 hz
    mixedMoment B raw2925step0 raw2925step0Labels = mixedMoment B raw2925step1 raw2925step1Labels := by
      have hz : ∀ j, raw2925step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2925step1 = (fun i j => raw2925step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2925step1 raw2925step0; decide +kernel
      have hl : raw2925step1Labels = raw2925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2925step0 raw2925step0Labels permutation80 hz
    mixedMoment B raw2925step1 raw2925step1Labels = mixedMoment B raw2925step2 raw2925step2Labels := by
      have hz : ∀ i, raw2925step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2925step2 = (fun i j => raw2925step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2925step2 raw2925step1; decide +kernel
      have hl : raw2925step2Labels = (fun j => raw2925step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2925step1 raw2925step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw2926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2926step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2926step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2926step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2926 raw2926Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2926 raw2926Labels = mixedMoment B raw2926step0 raw2926step0Labels := by
      have hz : ∀ j, raw2926 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2926step0 = (fun i j => raw2926 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2926step0 raw2926; decide +kernel
      have hl : raw2926step0Labels = raw2926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2926 raw2926Labels permutation520 hz
    mixedMoment B raw2926step0 raw2926step0Labels = mixedMoment B raw2926step1 raw2926step1Labels := by
      have hz : ∀ j, raw2926step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2926step1 = (fun i j => raw2926step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2926step1 raw2926step0; decide +kernel
      have hl : raw2926step1Labels = raw2926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2926step0 raw2926step0Labels permutation56 hz
    mixedMoment B raw2926step1 raw2926step1Labels = mixedMoment B raw2926step2 raw2926step2Labels := by
      have hz : ∀ i, raw2926step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2926step2 = (fun i j => raw2926step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2926step2 raw2926step1; decide +kernel
      have hl : raw2926step2Labels = (fun j => raw2926step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2926step1 raw2926step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2927step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw2927step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2927step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw2927step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2927step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2927step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2927 raw2927Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2927 raw2927Labels = mixedMoment B raw2927step0 raw2927step0Labels := by
      have hz : ∀ j, raw2927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2927step0 = (fun i j => raw2927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2927step0 raw2927; decide +kernel
      have hl : raw2927step0Labels = raw2927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2927 raw2927Labels permutation346 hz
    mixedMoment B raw2927step0 raw2927step0Labels = mixedMoment B raw2927step1 raw2927step1Labels := by
      have hz : ∀ j, raw2927step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2927step1 = (fun i j => raw2927step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2927step1 raw2927step0; decide +kernel
      have hl : raw2927step1Labels = raw2927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2927step0 raw2927step0Labels permutation56 hz
    mixedMoment B raw2927step1 raw2927step1Labels = mixedMoment B raw2927step2 raw2927step2Labels := by
      have hz : ∀ i, raw2927step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2927step2 = (fun i j => raw2927step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2927step2 raw2927step1; decide +kernel
      have hl : raw2927step2Labels = (fun j => raw2927step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2927step1 raw2927step1Labels permutation6 hz
    mixedMoment B raw2927step2 raw2927step2Labels = mixedMoment B raw2927step3 raw2927step3Labels := by
      have ha : raw2927step3 = (fun i j => raw2927step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2927step3 raw2927step2; decide +kernel
      have hl : raw2927step3Labels = raw2927step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2927step2 raw2927step2Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw2928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2928step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2928step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2928step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2928step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2928step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2928 raw2928Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2928 raw2928Labels = mixedMoment B raw2928step0 raw2928step0Labels := by
      have hz : ∀ j, raw2928 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2928step0 = (fun i j => raw2928 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2928step0 raw2928; decide +kernel
      have hl : raw2928step0Labels = raw2928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2928 raw2928Labels permutation520 hz
    mixedMoment B raw2928step0 raw2928step0Labels = mixedMoment B raw2928step1 raw2928step1Labels := by
      have hz : ∀ j, raw2928step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2928step1 = (fun i j => raw2928step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2928step1 raw2928step0; decide +kernel
      have hl : raw2928step1Labels = raw2928step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2928step0 raw2928step0Labels permutation80 hz
    mixedMoment B raw2928step1 raw2928step1Labels = mixedMoment B raw2928step2 raw2928step2Labels := by
      have hz : ∀ j, raw2928step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2928step2 = (fun i j => raw2928step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2928step2 raw2928step1; decide +kernel
      have hl : raw2928step2Labels = raw2928step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2928step1 raw2928step1Labels permutation14 hz
    mixedMoment B raw2928step2 raw2928step2Labels = mixedMoment B raw2928step3 raw2928step3Labels := by
      have hz : ∀ i, raw2928step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2928step3 = (fun i j => raw2928step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2928step3 raw2928step2; decide +kernel
      have hl : raw2928step3Labels = (fun j => raw2928step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2928step2 raw2928step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw2929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2929step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2929step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2929step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2929 raw2929Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2929 raw2929Labels = mixedMoment B raw2929step0 raw2929step0Labels := by
      have hz : ∀ j, raw2929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2929step0 = (fun i j => raw2929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2929step0 raw2929; decide +kernel
      have hl : raw2929step0Labels = raw2929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929 raw2929Labels permutation434 hz
    mixedMoment B raw2929step0 raw2929step0Labels = mixedMoment B raw2929step1 raw2929step1Labels := by
      have hz : ∀ j, raw2929step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2929step1 = (fun i j => raw2929step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2929step1 raw2929step0; decide +kernel
      have hl : raw2929step1Labels = raw2929step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step0 raw2929step0Labels permutation80 hz
    mixedMoment B raw2929step1 raw2929step1Labels = mixedMoment B raw2929step2 raw2929step2Labels := by
      have hz : ∀ j, raw2929step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2929step2 = (fun i j => raw2929step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2929step2 raw2929step1; decide +kernel
      have hl : raw2929step2Labels = raw2929step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2929step1 raw2929step1Labels permutation14 hz
    mixedMoment B raw2929step2 raw2929step2Labels = mixedMoment B raw2929step3 raw2929step3Labels := by
      have hz : ∀ i, raw2929step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2929step3 = (fun i j => raw2929step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2929step3 raw2929step2; decide +kernel
      have hl : raw2929step3Labels = (fun j => raw2929step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2929step2 raw2929step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw2930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2930step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2930step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2930step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2930 raw2930Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2930 raw2930Labels = mixedMoment B raw2930step0 raw2930step0Labels := by
      have hz : ∀ j, raw2930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2930step0 = (fun i j => raw2930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2930step0 raw2930; decide +kernel
      have hl : raw2930step0Labels = raw2930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930 raw2930Labels permutation434 hz
    mixedMoment B raw2930step0 raw2930step0Labels = mixedMoment B raw2930step1 raw2930step1Labels := by
      have hz : ∀ j, raw2930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2930step1 = (fun i j => raw2930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2930step1 raw2930step0; decide +kernel
      have hl : raw2930step1Labels = raw2930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2930step0 raw2930step0Labels permutation80 hz
    mixedMoment B raw2930step1 raw2930step1Labels = mixedMoment B raw2930step2 raw2930step2Labels := by
      have hz : ∀ i, raw2930step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2930step2 = (fun i j => raw2930step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2930step2 raw2930step1; decide +kernel
      have hl : raw2930step2Labels = (fun j => raw2930step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2930step1 raw2930step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2931step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2931step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2931step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2931 raw2931Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2931 raw2931Labels = mixedMoment B raw2931step0 raw2931step0Labels := by
      have hz : ∀ j, raw2931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2931step0 = (fun i j => raw2931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2931step0 raw2931; decide +kernel
      have hl : raw2931step0Labels = raw2931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2931 raw2931Labels permutation434 hz
    mixedMoment B raw2931step0 raw2931step0Labels = mixedMoment B raw2931step1 raw2931step1Labels := by
      have hz : ∀ j, raw2931step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2931step1 = (fun i j => raw2931step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2931step1 raw2931step0; decide +kernel
      have hl : raw2931step1Labels = raw2931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2931step0 raw2931step0Labels permutation56 hz
    mixedMoment B raw2931step1 raw2931step1Labels = mixedMoment B raw2931step2 raw2931step2Labels := by
      have hz : ∀ i, raw2931step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2931step2 = (fun i j => raw2931step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2931step2 raw2931step1; decide +kernel
      have hl : raw2931step2Labels = (fun j => raw2931step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2931step1 raw2931step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw2932step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2932step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw2932step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2932 raw2932Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw2932 raw2932Labels = mixedMoment B raw2932step0 raw2932step0Labels := by
      have hz : ∀ j, raw2932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2932step0 = (fun i j => raw2932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2932step0 raw2932; decide +kernel
      have hl : raw2932step0Labels = raw2932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2932 raw2932Labels permutation346 hz
    mixedMoment B raw2932step0 raw2932step0Labels = mixedMoment B raw2932step1 raw2932step1Labels := by
      have hz : ∀ j, raw2932step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2932step1 = (fun i j => raw2932step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2932step1 raw2932step0; decide +kernel
      have hl : raw2932step1Labels = raw2932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2932step0 raw2932step0Labels permutation56 hz
    mixedMoment B raw2932step1 raw2932step1Labels = mixedMoment B raw2932step2 raw2932step2Labels := by
      have hz : ∀ i, raw2932step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2932step2 = (fun i j => raw2932step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2932step2 raw2932step1; decide +kernel
      have hl : raw2932step2Labels = (fun j => raw2932step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2932step1 raw2932step1Labels permutation6 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw2933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2933step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2933step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw2933step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2933 raw2933Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw2933 raw2933Labels = mixedMoment B raw2933step0 raw2933step0Labels := by
      have hz : ∀ j, raw2933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2933step0 = (fun i j => raw2933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2933step0 raw2933; decide +kernel
      have hl : raw2933step0Labels = raw2933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933 raw2933Labels permutation434 hz
    mixedMoment B raw2933step0 raw2933step0Labels = mixedMoment B raw2933step1 raw2933step1Labels := by
      have hz : ∀ j, raw2933step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2933step1 = (fun i j => raw2933step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2933step1 raw2933step0; decide +kernel
      have hl : raw2933step1Labels = raw2933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933step0 raw2933step0Labels permutation80 hz
    mixedMoment B raw2933step1 raw2933step1Labels = mixedMoment B raw2933step2 raw2933step2Labels := by
      have hz : ∀ j, raw2933step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2933step2 = (fun i j => raw2933step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2933step2 raw2933step1; decide +kernel
      have hl : raw2933step2Labels = raw2933step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2933step1 raw2933step1Labels permutation14 hz
    mixedMoment B raw2933step2 raw2933step2Labels = mixedMoment B raw2933step3 raw2933step3Labels := by
      have hz : ∀ i, raw2933step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2933step3 = (fun i j => raw2933step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2933step3 raw2933step2; decide +kernel
      have hl : raw2933step3Labels = (fun j => raw2933step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2933step2 raw2933step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw2934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2934step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 3, 0], ![3, -3, 0]]
def raw2934step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2934step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw2934step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2934 raw2934Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw2934 raw2934Labels = mixedMoment B raw2934step0 raw2934step0Labels := by
      have hz : ∀ j, raw2934 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2934step0 = (fun i j => raw2934 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2934step0 raw2934; decide +kernel
      have hl : raw2934step0Labels = raw2934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934 raw2934Labels permutation520 hz
    mixedMoment B raw2934step0 raw2934step0Labels = mixedMoment B raw2934step1 raw2934step1Labels := by
      have hz : ∀ j, raw2934step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2934step1 = (fun i j => raw2934step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2934step1 raw2934step0; decide +kernel
      have hl : raw2934step1Labels = raw2934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step0 raw2934step0Labels permutation104 hz
    mixedMoment B raw2934step1 raw2934step1Labels = mixedMoment B raw2934step2 raw2934step2Labels := by
      have hz : ∀ j, raw2934step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2934step2 = (fun i j => raw2934step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2934step2 raw2934step1; decide +kernel
      have hl : raw2934step2Labels = raw2934step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step1 raw2934step1Labels permutation20 hz
    mixedMoment B raw2934step2 raw2934step2Labels = mixedMoment B raw2934step3 raw2934step3Labels := by
      have hz : ∀ j, raw2934step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw2934step3 = (fun i j => raw2934step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw2934step3 raw2934step2; decide +kernel
      have hl : raw2934step3Labels = raw2934step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2934step2 raw2934step2Labels permutation4 hz
    mixedMoment B raw2934step3 raw2934step3Labels = mixedMoment B raw2934step4 raw2934step4Labels := by
      have hz : ∀ i, raw2934step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2934step4 = (fun i j => raw2934step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2934step4 raw2934step3; decide +kernel
      have hl : raw2934step4Labels = (fun j => raw2934step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2934step3 raw2934step3Labels permutation6 hz
    _ = mixedMoment B node4085 node4085Labels := by rfl

def raw2935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2935step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2935step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2935step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2935step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2935step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2935step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2935step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2935step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2935 raw2935Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2935 raw2935Labels = mixedMoment B raw2935step0 raw2935step0Labels := by
      have hz : ∀ j, raw2935 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2935step0 = (fun i j => raw2935 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2935step0 raw2935; decide +kernel
      have hl : raw2935step0Labels = raw2935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935 raw2935Labels permutation520 hz
    mixedMoment B raw2935step0 raw2935step0Labels = mixedMoment B raw2935step1 raw2935step1Labels := by
      have hz : ∀ j, raw2935step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2935step1 = (fun i j => raw2935step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2935step1 raw2935step0; decide +kernel
      have hl : raw2935step1Labels = raw2935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935step0 raw2935step0Labels permutation104 hz
    mixedMoment B raw2935step1 raw2935step1Labels = mixedMoment B raw2935step2 raw2935step2Labels := by
      have hz : ∀ j, raw2935step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw2935step2 = (fun i j => raw2935step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw2935step2 raw2935step1; decide +kernel
      have hl : raw2935step2Labels = raw2935step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2935step1 raw2935step1Labels permutation20 hz
    mixedMoment B raw2935step2 raw2935step2Labels = mixedMoment B raw2935step3 raw2935step3Labels := by
      have hz : ∀ i, raw2935step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2935step3 = (fun i j => raw2935step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2935step3 raw2935step2; decide +kernel
      have hl : raw2935step3Labels = (fun j => raw2935step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2935step2 raw2935step2Labels permutation6 hz
    mixedMoment B raw2935step3 raw2935step3Labels = mixedMoment B raw2935step4 raw2935step4Labels := by
      have ha : raw2935step4 = (fun i j => raw2935step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2935step4 raw2935step3; decide +kernel
      have hl : raw2935step4Labels = raw2935step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2935step3 raw2935step3Labels permutation7 permutation0
    mixedMoment B raw2935step4 raw2935step4Labels = mixedMoment B raw2935step5 raw2935step5Labels := by
      have ha : raw2935step5 = -raw2935step4 := by apply Matrix.ext; change ∀ i j, raw2935step5 i j = -(raw2935step4 i j); unfold raw2935step5 raw2935step4; decide +kernel
      have hl : raw2935step5Labels = raw2935step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw2936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2936step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2936step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2936step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2936step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2936step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2936step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2936step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2936step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2936 raw2936Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2936 raw2936Labels = mixedMoment B raw2936step0 raw2936step0Labels := by
      have hz : ∀ j, raw2936 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2936step0 = (fun i j => raw2936 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2936step0 raw2936; decide +kernel
      have hl : raw2936step0Labels = raw2936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2936 raw2936Labels permutation520 hz
    mixedMoment B raw2936step0 raw2936step0Labels = mixedMoment B raw2936step1 raw2936step1Labels := by
      have hz : ∀ j, raw2936step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw2936step1 = (fun i j => raw2936step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw2936step1 raw2936step0; decide +kernel
      have hl : raw2936step1Labels = raw2936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2936step0 raw2936step0Labels permutation104 hz
    mixedMoment B raw2936step1 raw2936step1Labels = mixedMoment B raw2936step2 raw2936step2Labels := by
      have hz : ∀ j, raw2936step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2936step2 = (fun i j => raw2936step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2936step2 raw2936step1; decide +kernel
      have hl : raw2936step2Labels = raw2936step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2936step1 raw2936step1Labels permutation14 hz
    mixedMoment B raw2936step2 raw2936step2Labels = mixedMoment B raw2936step3 raw2936step3Labels := by
      have hz : ∀ i, raw2936step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2936step3 = (fun i j => raw2936step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2936step3 raw2936step2; decide +kernel
      have hl : raw2936step3Labels = (fun j => raw2936step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2936step2 raw2936step2Labels permutation6 hz
    mixedMoment B raw2936step3 raw2936step3Labels = mixedMoment B raw2936step4 raw2936step4Labels := by
      have ha : raw2936step4 = (fun i j => raw2936step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2936step4 raw2936step3; decide +kernel
      have hl : raw2936step4Labels = raw2936step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2936step3 raw2936step3Labels permutation7 permutation0
    mixedMoment B raw2936step4 raw2936step4Labels = mixedMoment B raw2936step5 raw2936step5Labels := by
      have ha : raw2936step5 = -raw2936step4 := by apply Matrix.ext; change ∀ i j, raw2936step5 i j = -(raw2936step4 i j); unfold raw2936step5 raw2936step4; decide +kernel
      have hl : raw2936step5Labels = raw2936step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw2937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw2937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2937step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2937step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2937step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2937step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2937step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2937step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2937step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2937step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2937 raw2937Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2937 raw2937Labels = mixedMoment B raw2937step0 raw2937step0Labels := by
      have hz : ∀ j, raw2937 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2937step0 = (fun i j => raw2937 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2937step0 raw2937; decide +kernel
      have hl : raw2937step0Labels = raw2937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2937 raw2937Labels permutation520 hz
    mixedMoment B raw2937step0 raw2937step0Labels = mixedMoment B raw2937step1 raw2937step1Labels := by
      have hz : ∀ j, raw2937step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2937step1 = (fun i j => raw2937step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2937step1 raw2937step0; decide +kernel
      have hl : raw2937step1Labels = raw2937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2937step0 raw2937step0Labels permutation80 hz
    mixedMoment B raw2937step1 raw2937step1Labels = mixedMoment B raw2937step2 raw2937step2Labels := by
      have hz : ∀ j, raw2937step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2937step2 = (fun i j => raw2937step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2937step2 raw2937step1; decide +kernel
      have hl : raw2937step2Labels = raw2937step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2937step1 raw2937step1Labels permutation14 hz
    mixedMoment B raw2937step2 raw2937step2Labels = mixedMoment B raw2937step3 raw2937step3Labels := by
      have hz : ∀ i, raw2937step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2937step3 = (fun i j => raw2937step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2937step3 raw2937step2; decide +kernel
      have hl : raw2937step3Labels = (fun j => raw2937step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2937step2 raw2937step2Labels permutation6 hz
    mixedMoment B raw2937step3 raw2937step3Labels = mixedMoment B raw2937step4 raw2937step4Labels := by
      have ha : raw2937step4 = (fun i j => raw2937step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2937step4 raw2937step3; decide +kernel
      have hl : raw2937step4Labels = raw2937step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2937step3 raw2937step3Labels permutation7 permutation0
    mixedMoment B raw2937step4 raw2937step4Labels = mixedMoment B raw2937step5 raw2937step5Labels := by
      have ha : raw2937step5 = -raw2937step4 := by apply Matrix.ext; change ∀ i j, raw2937step5 i j = -(raw2937step4 i j); unfold raw2937step5 raw2937step4; decide +kernel
      have hl : raw2937step5Labels = raw2937step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw2938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw2938step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2938step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw2938step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2938step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw2938step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw2938step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw2938step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical2938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2938 raw2938Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw2938 raw2938Labels = mixedMoment B raw2938step0 raw2938step0Labels := by
      have hz : ∀ j, raw2938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2938step0 = (fun i j => raw2938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2938step0 raw2938; decide +kernel
      have hl : raw2938step0Labels = raw2938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2938 raw2938Labels permutation434 hz
    mixedMoment B raw2938step0 raw2938step0Labels = mixedMoment B raw2938step1 raw2938step1Labels := by
      have hz : ∀ j, raw2938step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2938step1 = (fun i j => raw2938step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2938step1 raw2938step0; decide +kernel
      have hl : raw2938step1Labels = raw2938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2938step0 raw2938step0Labels permutation80 hz
    mixedMoment B raw2938step1 raw2938step1Labels = mixedMoment B raw2938step2 raw2938step2Labels := by
      have hz : ∀ j, raw2938step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2938step2 = (fun i j => raw2938step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2938step2 raw2938step1; decide +kernel
      have hl : raw2938step2Labels = raw2938step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2938step1 raw2938step1Labels permutation14 hz
    mixedMoment B raw2938step2 raw2938step2Labels = mixedMoment B raw2938step3 raw2938step3Labels := by
      have hz : ∀ i, raw2938step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw2938step3 = (fun i j => raw2938step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw2938step3 raw2938step2; decide +kernel
      have hl : raw2938step3Labels = (fun j => raw2938step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw2938step2 raw2938step2Labels permutation6 hz
    mixedMoment B raw2938step3 raw2938step3Labels = mixedMoment B raw2938step4 raw2938step4Labels := by
      have ha : raw2938step4 = (fun i j => raw2938step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw2938step4 raw2938step3; decide +kernel
      have hl : raw2938step4Labels = raw2938step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2938step3 raw2938step3Labels permutation7 permutation0
    mixedMoment B raw2938step4 raw2938step4Labels = mixedMoment B raw2938step5 raw2938step5Labels := by
      have ha : raw2938step5 = -raw2938step4 := by apply Matrix.ext; change ∀ i j, raw2938step5 i j = -(raw2938step4 i j); unfold raw2938step5 raw2938step4; decide +kernel
      have hl : raw2938step5Labels = raw2938step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw2939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2939step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2939step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2939step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2939 raw2939Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw2939 raw2939Labels = mixedMoment B raw2939step0 raw2939step0Labels := by
      have ha : raw2939step0 = (fun i j => raw2939 (permutation240 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2939step0 raw2939; decide +kernel
      have hl : raw2939step0Labels = raw2939Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2939 raw2939Labels permutation240 permutation6
    mixedMoment B raw2939step0 raw2939step0Labels = mixedMoment B raw2939step1 raw2939step1Labels := by
      have ha : raw2939step1 = -raw2939step0 := by apply Matrix.ext; change ∀ i j, raw2939step1 i j = -(raw2939step0 i j); unfold raw2939step1 raw2939step0; decide +kernel
      have hl : raw2939step1Labels = raw2939step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2939step1 raw2939step1Labels = mixedMoment B raw2939step2 raw2939step2Labels := by
      have ha : raw2939step2 = raw2939step1 := by apply Matrix.ext; unfold raw2939step2 raw2939step1; decide +kernel
      have hl : raw2939step1Labels = labelEmbedding9 ∘ raw2939step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2939step1 raw2939step1Labels raw2939step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw2940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2940step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2940step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2940step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2940step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2940 raw2940Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw2940 raw2940Labels = mixedMoment B raw2940step0 raw2940step0Labels := by
      have hz : ∀ j, raw2940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2940step0 = (fun i j => raw2940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2940step0 raw2940; decide +kernel
      have hl : raw2940step0Labels = raw2940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2940 raw2940Labels permutation265 hz
    mixedMoment B raw2940step0 raw2940step0Labels = mixedMoment B raw2940step1 raw2940step1Labels := by
      have ha : raw2940step1 = (fun i j => raw2940step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2940step1 raw2940step0; decide +kernel
      have hl : raw2940step1Labels = raw2940step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2940step0 raw2940step0Labels permutation65 permutation4
    mixedMoment B raw2940step1 raw2940step1Labels = mixedMoment B raw2940step2 raw2940step2Labels := by
      have ha : raw2940step2 = -raw2940step1 := by apply Matrix.ext; change ∀ i j, raw2940step2 i j = -(raw2940step1 i j); unfold raw2940step2 raw2940step1; decide +kernel
      have hl : raw2940step2Labels = raw2940step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2940step2 raw2940step2Labels = mixedMoment B raw2940step3 raw2940step3Labels := by
      have ha : raw2940step3 = raw2940step2 := by apply Matrix.ext; unfold raw2940step3 raw2940step2; decide +kernel
      have hl : raw2940step2Labels = labelEmbedding7 ∘ raw2940step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2940step2 raw2940step2Labels raw2940step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw2941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2941step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2941step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2941step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2941step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2941 raw2941Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw2941 raw2941Labels = mixedMoment B raw2941step0 raw2941step0Labels := by
      have hz : ∀ j, raw2941 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2941step0 = (fun i j => raw2941 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2941step0 raw2941; decide +kernel
      have hl : raw2941step0Labels = raw2941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2941 raw2941Labels permutation265 hz
    mixedMoment B raw2941step0 raw2941step0Labels = mixedMoment B raw2941step1 raw2941step1Labels := by
      have ha : raw2941step1 = (fun i j => raw2941step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2941step1 raw2941step0; decide +kernel
      have hl : raw2941step1Labels = raw2941step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2941step0 raw2941step0Labels permutation89 permutation4
    mixedMoment B raw2941step1 raw2941step1Labels = mixedMoment B raw2941step2 raw2941step2Labels := by
      have ha : raw2941step2 = -raw2941step1 := by apply Matrix.ext; change ∀ i j, raw2941step2 i j = -(raw2941step1 i j); unfold raw2941step2 raw2941step1; decide +kernel
      have hl : raw2941step2Labels = raw2941step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2941step2 raw2941step2Labels = mixedMoment B raw2941step3 raw2941step3Labels := by
      have ha : raw2941step3 = raw2941step2 := by apply Matrix.ext; unfold raw2941step3 raw2941step2; decide +kernel
      have hl : raw2941step2Labels = labelEmbedding7 ∘ raw2941step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2941step2 raw2941step2Labels raw2941step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw2942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw2942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2942step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2942step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2942step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2942step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2942 raw2942Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw2942 raw2942Labels = mixedMoment B raw2942step0 raw2942step0Labels := by
      have hz : ∀ j, raw2942 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2942step0 = (fun i j => raw2942 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2942step0 raw2942; decide +kernel
      have hl : raw2942step0Labels = raw2942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2942 raw2942Labels permutation520 hz
    mixedMoment B raw2942step0 raw2942step0Labels = mixedMoment B raw2942step1 raw2942step1Labels := by
      have hz : ∀ j, raw2942step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2942step1 = (fun i j => raw2942step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2942step1 raw2942step0; decide +kernel
      have hl : raw2942step1Labels = raw2942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2942step0 raw2942step0Labels permutation56 hz
    mixedMoment B raw2942step1 raw2942step1Labels = mixedMoment B raw2942step2 raw2942step2Labels := by
      have ha : raw2942step2 = (fun i j => raw2942step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2942step2 raw2942step1; decide +kernel
      have hl : raw2942step2Labels = raw2942step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2942step1 raw2942step1Labels permutation12 permutation6
    mixedMoment B raw2942step2 raw2942step2Labels = mixedMoment B raw2942step3 raw2942step3Labels := by
      have ha : raw2942step3 = -raw2942step2 := by apply Matrix.ext; change ∀ i j, raw2942step3 i j = -(raw2942step2 i j); unfold raw2942step3 raw2942step2; decide +kernel
      have hl : raw2942step3Labels = raw2942step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2942step3 raw2942step3Labels = mixedMoment B raw2942step4 raw2942step4Labels := by
      have ha : raw2942step4 = raw2942step3 := by apply Matrix.ext; unfold raw2942step4 raw2942step3; decide +kernel
      have hl : raw2942step3Labels = labelEmbedding9 ∘ raw2942step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2942step3 raw2942step3Labels raw2942step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw2943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw2943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2943step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2943step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2943step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2943step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2943step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2943 raw2943Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw2943 raw2943Labels = mixedMoment B raw2943step0 raw2943step0Labels := by
      have hz : ∀ j, raw2943 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw2943step0 = (fun i j => raw2943 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw2943step0 raw2943; decide +kernel
      have hl : raw2943step0Labels = raw2943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2943 raw2943Labels permutation590 hz
    mixedMoment B raw2943step0 raw2943step0Labels = mixedMoment B raw2943step1 raw2943step1Labels := by
      have hz : ∀ j, raw2943step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2943step1 = (fun i j => raw2943step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2943step1 raw2943step0; decide +kernel
      have hl : raw2943step1Labels = raw2943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2943step0 raw2943step0Labels permutation56 hz
    mixedMoment B raw2943step1 raw2943step1Labels = mixedMoment B raw2943step2 raw2943step2Labels := by
      have ha : raw2943step2 = (fun i j => raw2943step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2943step2 raw2943step1; decide +kernel
      have hl : raw2943step2Labels = raw2943step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2943step1 raw2943step1Labels permutation12 permutation6
    mixedMoment B raw2943step2 raw2943step2Labels = mixedMoment B raw2943step3 raw2943step3Labels := by
      have ha : raw2943step3 = -raw2943step2 := by apply Matrix.ext; change ∀ i j, raw2943step3 i j = -(raw2943step2 i j); unfold raw2943step3 raw2943step2; decide +kernel
      have hl : raw2943step3Labels = raw2943step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2943step3 raw2943step3Labels = mixedMoment B raw2943step4 raw2943step4Labels := by
      have ha : raw2943step4 = raw2943step3 := by apply Matrix.ext; unfold raw2943step4 raw2943step3; decide +kernel
      have hl : raw2943step3Labels = labelEmbedding9 ∘ raw2943step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2943step3 raw2943step3Labels raw2943step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
