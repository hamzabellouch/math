import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2688step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2688step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2688step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2688step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2688step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2688step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2688step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2688 raw2688Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw2688 raw2688Labels = mixedMoment B raw2688step0 raw2688step0Labels := by
      have hz : ∀ j, raw2688 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2688step0 = (fun i j => raw2688 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2688step0 raw2688; decide +kernel
      have hl : raw2688step0Labels = raw2688Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2688 raw2688Labels permutation265 hz
    mixedMoment B raw2688step0 raw2688step0Labels = mixedMoment B raw2688step1 raw2688step1Labels := by
      have ha : raw2688step1 = (fun i j => raw2688step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2688step1 raw2688step0; decide +kernel
      have hl : raw2688step1Labels = raw2688step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2688step0 raw2688step0Labels permutation145 permutation3
    mixedMoment B raw2688step1 raw2688step1Labels = mixedMoment B raw2688step2 raw2688step2Labels := by
      have ha : raw2688step2 = -raw2688step1 := by apply Matrix.ext; change ∀ i j, raw2688step2 i j = -(raw2688step1 i j); unfold raw2688step2 raw2688step1; decide +kernel
      have hl : raw2688step2Labels = raw2688step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2688step2 raw2688step2Labels = mixedMoment B raw2688step3 raw2688step3Labels := by
      have ha : raw2688step3 = raw2688step2 := by apply Matrix.ext; unfold raw2688step3 raw2688step2; decide +kernel
      have hl : raw2688step2Labels = labelEmbedding6 ∘ raw2688step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2688step2 raw2688step2Labels raw2688step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw2689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2689step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2689step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2689step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2689step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2689step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2689step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2689step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2689 raw2689Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw2689 raw2689Labels = mixedMoment B raw2689step0 raw2689step0Labels := by
      have hz : ∀ j, raw2689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2689step0 = (fun i j => raw2689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2689step0 raw2689; decide +kernel
      have hl : raw2689step0Labels = raw2689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2689 raw2689Labels permutation346 hz
    mixedMoment B raw2689step0 raw2689step0Labels = mixedMoment B raw2689step1 raw2689step1Labels := by
      have hz : ∀ j, raw2689step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2689step1 = (fun i j => raw2689step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2689step1 raw2689step0; decide +kernel
      have hl : raw2689step1Labels = raw2689step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2689step0 raw2689step0Labels permutation56 hz
    mixedMoment B raw2689step1 raw2689step1Labels = mixedMoment B raw2689step2 raw2689step2Labels := by
      have ha : raw2689step2 = (fun i j => raw2689step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2689step2 raw2689step1; decide +kernel
      have hl : raw2689step2Labels = raw2689step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2689step1 raw2689step1Labels permutation31 permutation3
    mixedMoment B raw2689step2 raw2689step2Labels = mixedMoment B raw2689step3 raw2689step3Labels := by
      have ha : raw2689step3 = -raw2689step2 := by apply Matrix.ext; change ∀ i j, raw2689step3 i j = -(raw2689step2 i j); unfold raw2689step3 raw2689step2; decide +kernel
      have hl : raw2689step3Labels = raw2689step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2689step3 raw2689step3Labels = mixedMoment B raw2689step4 raw2689step4Labels := by
      have ha : raw2689step4 = raw2689step3 := by apply Matrix.ext; unfold raw2689step4 raw2689step3; decide +kernel
      have hl : raw2689step3Labels = labelEmbedding6 ∘ raw2689step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2689step3 raw2689step3Labels raw2689step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw2690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2690step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2690step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2690step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2690step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2690step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2690step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2690step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2690 raw2690Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw2690 raw2690Labels = mixedMoment B raw2690step0 raw2690step0Labels := by
      have hz : ∀ j, raw2690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2690step0 = (fun i j => raw2690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2690step0 raw2690; decide +kernel
      have hl : raw2690step0Labels = raw2690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2690 raw2690Labels permutation346 hz
    mixedMoment B raw2690step0 raw2690step0Labels = mixedMoment B raw2690step1 raw2690step1Labels := by
      have hz : ∀ j, raw2690step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2690step1 = (fun i j => raw2690step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2690step1 raw2690step0; decide +kernel
      have hl : raw2690step1Labels = raw2690step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2690step0 raw2690step0Labels permutation56 hz
    mixedMoment B raw2690step1 raw2690step1Labels = mixedMoment B raw2690step2 raw2690step2Labels := by
      have ha : raw2690step2 = (fun i j => raw2690step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2690step2 raw2690step1; decide +kernel
      have hl : raw2690step2Labels = raw2690step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2690step1 raw2690step1Labels permutation29 permutation3
    mixedMoment B raw2690step2 raw2690step2Labels = mixedMoment B raw2690step3 raw2690step3Labels := by
      have ha : raw2690step3 = -raw2690step2 := by apply Matrix.ext; change ∀ i j, raw2690step3 i j = -(raw2690step2 i j); unfold raw2690step3 raw2690step2; decide +kernel
      have hl : raw2690step3Labels = raw2690step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2690step3 raw2690step3Labels = mixedMoment B raw2690step4 raw2690step4Labels := by
      have ha : raw2690step4 = raw2690step3 := by apply Matrix.ext; unfold raw2690step4 raw2690step3; decide +kernel
      have hl : raw2690step3Labels = labelEmbedding6 ∘ raw2690step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2690step3 raw2690step3Labels raw2690step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw2691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw2691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2691step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2691 raw2691Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw2691 raw2691Labels = mixedMoment B raw2691step0 raw2691step0Labels := by
      have hz : ∀ j, raw2691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2691step0 = (fun i j => raw2691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2691step0 raw2691; decide +kernel
      have hl : raw2691step0Labels = raw2691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2691 raw2691Labels permutation346 hz
    mixedMoment B raw2691step0 raw2691step0Labels = mixedMoment B raw2691step1 raw2691step1Labels := by
      have ha : raw2691step1 = (fun i j => raw2691step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2691step1 raw2691step0; decide +kernel
      have hl : raw2691step1Labels = raw2691step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2691step0 raw2691step0Labels permutation144 permutation3
    mixedMoment B raw2691step1 raw2691step1Labels = mixedMoment B raw2691step2 raw2691step2Labels := by
      have ha : raw2691step2 = -raw2691step1 := by apply Matrix.ext; change ∀ i j, raw2691step2 i j = -(raw2691step1 i j); unfold raw2691step2 raw2691step1; decide +kernel
      have hl : raw2691step2Labels = raw2691step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw2692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw2692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2692step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2692step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2692 raw2692Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw2692 raw2692Labels = mixedMoment B raw2692step0 raw2692step0Labels := by
      have hz : ∀ j, raw2692 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2692step0 = (fun i j => raw2692 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2692step0 raw2692; decide +kernel
      have hl : raw2692step0Labels = raw2692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2692 raw2692Labels permutation265 hz
    mixedMoment B raw2692step0 raw2692step0Labels = mixedMoment B raw2692step1 raw2692step1Labels := by
      have ha : raw2692step1 = (fun i j => raw2692step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2692step1 raw2692step0; decide +kernel
      have hl : raw2692step1Labels = raw2692step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2692step0 raw2692step0Labels permutation144 permutation3
    mixedMoment B raw2692step1 raw2692step1Labels = mixedMoment B raw2692step2 raw2692step2Labels := by
      have ha : raw2692step2 = -raw2692step1 := by apply Matrix.ext; change ∀ i j, raw2692step2 i j = -(raw2692step1 i j); unfold raw2692step2 raw2692step1; decide +kernel
      have hl : raw2692step2Labels = raw2692step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw2693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2693step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2693step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2693step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2693step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2693step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2693step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2693step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2693step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2693 raw2693Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw2693 raw2693Labels = mixedMoment B raw2693step0 raw2693step0Labels := by
      have hz : ∀ j, raw2693 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2693step0 = (fun i j => raw2693 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2693step0 raw2693; decide +kernel
      have hl : raw2693step0Labels = raw2693Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2693 raw2693Labels permutation346 hz
    mixedMoment B raw2693step0 raw2693step0Labels = mixedMoment B raw2693step1 raw2693step1Labels := by
      have hz : ∀ j, raw2693step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2693step1 = (fun i j => raw2693step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2693step1 raw2693step0; decide +kernel
      have hl : raw2693step1Labels = raw2693step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2693step0 raw2693step0Labels permutation56 hz
    mixedMoment B raw2693step1 raw2693step1Labels = mixedMoment B raw2693step2 raw2693step2Labels := by
      have ha : raw2693step2 = (fun i j => raw2693step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2693step2 raw2693step1; decide +kernel
      have hl : raw2693step2Labels = raw2693step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2693step1 raw2693step1Labels permutation30 permutation3
    mixedMoment B raw2693step2 raw2693step2Labels = mixedMoment B raw2693step3 raw2693step3Labels := by
      have ha : raw2693step3 = -raw2693step2 := by apply Matrix.ext; change ∀ i j, raw2693step3 i j = -(raw2693step2 i j); unfold raw2693step3 raw2693step2; decide +kernel
      have hl : raw2693step3Labels = raw2693step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw2694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2694step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2694step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2694step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2694step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2694step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2694step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2694step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2694 raw2694Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw2694 raw2694Labels = mixedMoment B raw2694step0 raw2694step0Labels := by
      have hz : ∀ j, raw2694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2694step0 = (fun i j => raw2694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2694step0 raw2694; decide +kernel
      have hl : raw2694step0Labels = raw2694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2694 raw2694Labels permutation346 hz
    mixedMoment B raw2694step0 raw2694step0Labels = mixedMoment B raw2694step1 raw2694step1Labels := by
      have hz : ∀ j, raw2694step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2694step1 = (fun i j => raw2694step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2694step1 raw2694step0; decide +kernel
      have hl : raw2694step1Labels = raw2694step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2694step0 raw2694step0Labels permutation56 hz
    mixedMoment B raw2694step1 raw2694step1Labels = mixedMoment B raw2694step2 raw2694step2Labels := by
      have ha : raw2694step2 = (fun i j => raw2694step1 (permutation28 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2694step2 raw2694step1; decide +kernel
      have hl : raw2694step2Labels = raw2694step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2694step1 raw2694step1Labels permutation28 permutation3
    mixedMoment B raw2694step2 raw2694step2Labels = mixedMoment B raw2694step3 raw2694step3Labels := by
      have ha : raw2694step3 = -raw2694step2 := by apply Matrix.ext; change ∀ i j, raw2694step3 i j = -(raw2694step2 i j); unfold raw2694step3 raw2694step2; decide +kernel
      have hl : raw2694step3Labels = raw2694step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw2695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2695step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2695step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2695step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2695step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2695step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2695step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2695step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2695 raw2695Labels = mixedMoment B node4016 node4016Labels := by
  calc
    mixedMoment B raw2695 raw2695Labels = mixedMoment B raw2695step0 raw2695step0Labels := by
      have hz : ∀ j, raw2695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2695step0 = (fun i j => raw2695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2695step0 raw2695; decide +kernel
      have hl : raw2695step0Labels = raw2695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2695 raw2695Labels permutation346 hz
    mixedMoment B raw2695step0 raw2695step0Labels = mixedMoment B raw2695step1 raw2695step1Labels := by
      have hz : ∀ j, raw2695step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2695step1 = (fun i j => raw2695step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2695step1 raw2695step0; decide +kernel
      have hl : raw2695step1Labels = raw2695step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2695step0 raw2695step0Labels permutation56 hz
    mixedMoment B raw2695step1 raw2695step1Labels = mixedMoment B raw2695step2 raw2695step2Labels := by
      have ha : raw2695step2 = (fun i j => raw2695step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2695step2 raw2695step1; decide +kernel
      have hl : raw2695step2Labels = raw2695step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2695step1 raw2695step1Labels permutation12 permutation6
    mixedMoment B raw2695step2 raw2695step2Labels = mixedMoment B raw2695step3 raw2695step3Labels := by
      have ha : raw2695step3 = -raw2695step2 := by apply Matrix.ext; change ∀ i j, raw2695step3 i j = -(raw2695step2 i j); unfold raw2695step3 raw2695step2; decide +kernel
      have hl : raw2695step3Labels = raw2695step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4016 node4016Labels := by rfl

def raw2696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2696step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2696 raw2696Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2696 raw2696Labels = mixedMoment B raw2696step0 raw2696step0Labels := by
      have hz : ∀ j, raw2696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2696step0 = (fun i j => raw2696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2696step0 raw2696; decide +kernel
      have hl : raw2696step0Labels = raw2696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2696 raw2696Labels permutation346 hz
    mixedMoment B raw2696step0 raw2696step0Labels = mixedMoment B raw2696step1 raw2696step1Labels := by
      have ha : raw2696step1 = (fun i j => raw2696step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2696step1 raw2696step0; decide +kernel
      have hl : raw2696step1Labels = raw2696step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2696step0 raw2696step0Labels permutation40 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw2697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2697step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2697 raw2697Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw2697 raw2697Labels = mixedMoment B raw2697step0 raw2697step0Labels := by
      have ha : raw2697step0 = (fun i j => raw2697 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2697step0 raw2697; decide +kernel
      have hl : raw2697step0Labels = raw2697Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2697 raw2697Labels permutation616 permutation3
    mixedMoment B raw2697step0 raw2697step0Labels = mixedMoment B raw2697step1 raw2697step1Labels := by
      have ha : raw2697step1 = -raw2697step0 := by apply Matrix.ext; change ∀ i j, raw2697step1 i j = -(raw2697step0 i j); unfold raw2697step1 raw2697step0; decide +kernel
      have hl : raw2697step1Labels = raw2697step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw2698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2698step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2698step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2698step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2698step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2698step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2698step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2698 raw2698Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2698 raw2698Labels = mixedMoment B raw2698step0 raw2698step0Labels := by
      have hz : ∀ j, raw2698 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2698step0 = (fun i j => raw2698 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2698step0 raw2698; decide +kernel
      have hl : raw2698step0Labels = raw2698Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2698 raw2698Labels permutation346 hz
    mixedMoment B raw2698step0 raw2698step0Labels = mixedMoment B raw2698step1 raw2698step1Labels := by
      have ha : raw2698step1 = (fun i j => raw2698step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2698step1 raw2698step0; decide +kernel
      have hl : raw2698step1Labels = raw2698step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2698step0 raw2698step0Labels permutation139 permutation3
    mixedMoment B raw2698step1 raw2698step1Labels = mixedMoment B raw2698step2 raw2698step2Labels := by
      have ha : raw2698step2 = -raw2698step1 := by apply Matrix.ext; change ∀ i j, raw2698step2 i j = -(raw2698step1 i j); unfold raw2698step2 raw2698step1; decide +kernel
      have hl : raw2698step2Labels = raw2698step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw2699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2699step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2699step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2699 raw2699Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2699 raw2699Labels = mixedMoment B raw2699step0 raw2699step0Labels := by
      have hz : ∀ j, raw2699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2699step0 = (fun i j => raw2699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2699step0 raw2699; decide +kernel
      have hl : raw2699step0Labels = raw2699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2699 raw2699Labels permutation346 hz
    mixedMoment B raw2699step0 raw2699step0Labels = mixedMoment B raw2699step1 raw2699step1Labels := by
      have ha : raw2699step1 = (fun i j => raw2699step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2699step1 raw2699step0; decide +kernel
      have hl : raw2699step1Labels = raw2699step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2699step0 raw2699step0Labels permutation137 permutation3
    mixedMoment B raw2699step1 raw2699step1Labels = mixedMoment B raw2699step2 raw2699step2Labels := by
      have ha : raw2699step2 = -raw2699step1 := by apply Matrix.ext; change ∀ i j, raw2699step2 i j = -(raw2699step1 i j); unfold raw2699step2 raw2699step1; decide +kernel
      have hl : raw2699step2Labels = raw2699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw2700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2700step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2700step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2700 raw2700Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw2700 raw2700Labels = mixedMoment B raw2700step0 raw2700step0Labels := by
      have hz : ∀ j, raw2700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2700step0 = (fun i j => raw2700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2700step0 raw2700; decide +kernel
      have hl : raw2700step0Labels = raw2700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2700 raw2700Labels permutation346 hz
    mixedMoment B raw2700step0 raw2700step0Labels = mixedMoment B raw2700step1 raw2700step1Labels := by
      have ha : raw2700step1 = (fun i j => raw2700step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2700step1 raw2700step0; decide +kernel
      have hl : raw2700step1Labels = raw2700step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2700step0 raw2700step0Labels permutation40 permutation3
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw2701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2701step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2701step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2701 raw2701Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw2701 raw2701Labels = mixedMoment B raw2701step0 raw2701step0Labels := by
      have hz : ∀ j, raw2701 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2701step0 = (fun i j => raw2701 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2701step0 raw2701; decide +kernel
      have hl : raw2701step0Labels = raw2701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2701 raw2701Labels permutation265 hz
    mixedMoment B raw2701step0 raw2701step0Labels = mixedMoment B raw2701step1 raw2701step1Labels := by
      have ha : raw2701step1 = (fun i j => raw2701step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2701step1 raw2701step0; decide +kernel
      have hl : raw2701step1Labels = raw2701step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2701step0 raw2701step0Labels permutation40 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw2702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2702step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2702 raw2702Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw2702 raw2702Labels = mixedMoment B raw2702step0 raw2702step0Labels := by
      have ha : raw2702step0 = (fun i j => raw2702 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2702step0 raw2702; decide +kernel
      have hl : raw2702step0Labels = raw2702Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2702 raw2702Labels permutation640 permutation3
    mixedMoment B raw2702step0 raw2702step0Labels = mixedMoment B raw2702step1 raw2702step1Labels := by
      have ha : raw2702step1 = -raw2702step0 := by apply Matrix.ext; change ∀ i j, raw2702step1 i j = -(raw2702step0 i j); unfold raw2702step1 raw2702step0; decide +kernel
      have hl : raw2702step1Labels = raw2702step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw2703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2703step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2703step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2703 raw2703Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2703 raw2703Labels = mixedMoment B raw2703step0 raw2703step0Labels := by
      have hz : ∀ j, raw2703 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2703step0 = (fun i j => raw2703 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2703step0 raw2703; decide +kernel
      have hl : raw2703step0Labels = raw2703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2703 raw2703Labels permutation265 hz
    mixedMoment B raw2703step0 raw2703step0Labels = mixedMoment B raw2703step1 raw2703step1Labels := by
      have ha : raw2703step1 = (fun i j => raw2703step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2703step1 raw2703step0; decide +kernel
      have hl : raw2703step1Labels = raw2703step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2703step0 raw2703step0Labels permutation139 permutation3
    mixedMoment B raw2703step1 raw2703step1Labels = mixedMoment B raw2703step2 raw2703step2Labels := by
      have ha : raw2703step2 = -raw2703step1 := by apply Matrix.ext; change ∀ i j, raw2703step2 i j = -(raw2703step1 i j); unfold raw2703step2 raw2703step1; decide +kernel
      have hl : raw2703step2Labels = raw2703step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw2704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2704step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2704 raw2704Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2704 raw2704Labels = mixedMoment B raw2704step0 raw2704step0Labels := by
      have hz : ∀ j, raw2704 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2704step0 = (fun i j => raw2704 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2704step0 raw2704; decide +kernel
      have hl : raw2704step0Labels = raw2704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2704 raw2704Labels permutation265 hz
    mixedMoment B raw2704step0 raw2704step0Labels = mixedMoment B raw2704step1 raw2704step1Labels := by
      have ha : raw2704step1 = (fun i j => raw2704step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2704step1 raw2704step0; decide +kernel
      have hl : raw2704step1Labels = raw2704step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2704step0 raw2704step0Labels permutation137 permutation3
    mixedMoment B raw2704step1 raw2704step1Labels = mixedMoment B raw2704step2 raw2704step2Labels := by
      have ha : raw2704step2 = -raw2704step1 := by apply Matrix.ext; change ∀ i j, raw2704step2 i j = -(raw2704step1 i j); unfold raw2704step2 raw2704step1; decide +kernel
      have hl : raw2704step2Labels = raw2704step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw2705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2705step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2705 raw2705Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw2705 raw2705Labels = mixedMoment B raw2705step0 raw2705step0Labels := by
      have hz : ∀ j, raw2705 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2705step0 = (fun i j => raw2705 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2705step0 raw2705; decide +kernel
      have hl : raw2705step0Labels = raw2705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2705 raw2705Labels permutation265 hz
    mixedMoment B raw2705step0 raw2705step0Labels = mixedMoment B raw2705step1 raw2705step1Labels := by
      have ha : raw2705step1 = (fun i j => raw2705step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2705step1 raw2705step0; decide +kernel
      have hl : raw2705step1Labels = raw2705step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2705step0 raw2705step0Labels permutation40 permutation3
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw2706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2706step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2706step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2706step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2706step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw2706step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2706 raw2706Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw2706 raw2706Labels = mixedMoment B raw2706step0 raw2706step0Labels := by
      have hz : ∀ j, raw2706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2706step0 = (fun i j => raw2706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2706step0 raw2706; decide +kernel
      have hl : raw2706step0Labels = raw2706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2706 raw2706Labels permutation346 hz
    mixedMoment B raw2706step0 raw2706step0Labels = mixedMoment B raw2706step1 raw2706step1Labels := by
      have hz : ∀ j, raw2706step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2706step1 = (fun i j => raw2706step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2706step1 raw2706step0; decide +kernel
      have hl : raw2706step1Labels = raw2706step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2706step0 raw2706step0Labels permutation56 hz
    mixedMoment B raw2706step1 raw2706step1Labels = mixedMoment B raw2706step2 raw2706step2Labels := by
      have ha : raw2706step2 = (fun i j => raw2706step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2706step2 raw2706step1; decide +kernel
      have hl : raw2706step2Labels = raw2706step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2706step1 raw2706step1Labels permutation10 permutation3
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw2707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2707 raw2707Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw2707 raw2707Labels = mixedMoment B raw2707step0 raw2707step0Labels := by
      have hz : ∀ j, raw2707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2707step0 = (fun i j => raw2707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2707step0 raw2707; decide +kernel
      have hl : raw2707step0Labels = raw2707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2707 raw2707Labels permutation346 hz
    mixedMoment B raw2707step0 raw2707step0Labels = mixedMoment B raw2707step1 raw2707step1Labels := by
      have ha : raw2707step1 = (fun i j => raw2707step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2707step1 raw2707step0; decide +kernel
      have hl : raw2707step1Labels = raw2707step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2707step0 raw2707step0Labels permutation145 permutation3
    mixedMoment B raw2707step1 raw2707step1Labels = mixedMoment B raw2707step2 raw2707step2Labels := by
      have ha : raw2707step2 = -raw2707step1 := by apply Matrix.ext; change ∀ i j, raw2707step2 i j = -(raw2707step1 i j); unfold raw2707step2 raw2707step1; decide +kernel
      have hl : raw2707step2Labels = raw2707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw2708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2708step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2708 raw2708Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw2708 raw2708Labels = mixedMoment B raw2708step0 raw2708step0Labels := by
      have hz : ∀ j, raw2708 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2708step0 = (fun i j => raw2708 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2708step0 raw2708; decide +kernel
      have hl : raw2708step0Labels = raw2708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2708 raw2708Labels permutation265 hz
    mixedMoment B raw2708step0 raw2708step0Labels = mixedMoment B raw2708step1 raw2708step1Labels := by
      have ha : raw2708step1 = (fun i j => raw2708step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2708step1 raw2708step0; decide +kernel
      have hl : raw2708step1Labels = raw2708step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2708step0 raw2708step0Labels permutation145 permutation3
    mixedMoment B raw2708step1 raw2708step1Labels = mixedMoment B raw2708step2 raw2708step2Labels := by
      have ha : raw2708step2 = -raw2708step1 := by apply Matrix.ext; change ∀ i j, raw2708step2 i j = -(raw2708step1 i j); unfold raw2708step2 raw2708step1; decide +kernel
      have hl : raw2708step2Labels = raw2708step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw2709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2709step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2709step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2709step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2709step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2709 raw2709Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw2709 raw2709Labels = mixedMoment B raw2709step0 raw2709step0Labels := by
      have hz : ∀ j, raw2709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2709step0 = (fun i j => raw2709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2709step0 raw2709; decide +kernel
      have hl : raw2709step0Labels = raw2709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2709 raw2709Labels permutation346 hz
    mixedMoment B raw2709step0 raw2709step0Labels = mixedMoment B raw2709step1 raw2709step1Labels := by
      have hz : ∀ j, raw2709step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2709step1 = (fun i j => raw2709step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2709step1 raw2709step0; decide +kernel
      have hl : raw2709step1Labels = raw2709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2709step0 raw2709step0Labels permutation56 hz
    mixedMoment B raw2709step1 raw2709step1Labels = mixedMoment B raw2709step2 raw2709step2Labels := by
      have ha : raw2709step2 = (fun i j => raw2709step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2709step2 raw2709step1; decide +kernel
      have hl : raw2709step2Labels = raw2709step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2709step1 raw2709step1Labels permutation29 permutation3
    mixedMoment B raw2709step2 raw2709step2Labels = mixedMoment B raw2709step3 raw2709step3Labels := by
      have ha : raw2709step3 = -raw2709step2 := by apply Matrix.ext; change ∀ i j, raw2709step3 i j = -(raw2709step2 i j); unfold raw2709step3 raw2709step2; decide +kernel
      have hl : raw2709step3Labels = raw2709step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw2710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2710step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2710step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2710step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2710step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2710 raw2710Labels = mixedMoment B node4040 node4040Labels := by
  calc
    mixedMoment B raw2710 raw2710Labels = mixedMoment B raw2710step0 raw2710step0Labels := by
      have hz : ∀ j, raw2710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2710step0 = (fun i j => raw2710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2710step0 raw2710; decide +kernel
      have hl : raw2710step0Labels = raw2710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2710 raw2710Labels permutation346 hz
    mixedMoment B raw2710step0 raw2710step0Labels = mixedMoment B raw2710step1 raw2710step1Labels := by
      have hz : ∀ j, raw2710step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2710step1 = (fun i j => raw2710step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2710step1 raw2710step0; decide +kernel
      have hl : raw2710step1Labels = raw2710step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2710step0 raw2710step0Labels permutation56 hz
    mixedMoment B raw2710step1 raw2710step1Labels = mixedMoment B raw2710step2 raw2710step2Labels := by
      have ha : raw2710step2 = (fun i j => raw2710step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2710step2 raw2710step1; decide +kernel
      have hl : raw2710step2Labels = raw2710step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2710step1 raw2710step1Labels permutation10 permutation3
    _ = mixedMoment B node4040 node4040Labels := by rfl

def raw2711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2711step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2711step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2711step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2711step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw2711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2711 raw2711Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw2711 raw2711Labels = mixedMoment B raw2711step0 raw2711step0Labels := by
      have hz : ∀ j, raw2711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2711step0 = (fun i j => raw2711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2711step0 raw2711; decide +kernel
      have hl : raw2711step0Labels = raw2711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2711 raw2711Labels permutation346 hz
    mixedMoment B raw2711step0 raw2711step0Labels = mixedMoment B raw2711step1 raw2711step1Labels := by
      have hz : ∀ j, raw2711step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2711step1 = (fun i j => raw2711step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2711step1 raw2711step0; decide +kernel
      have hl : raw2711step1Labels = raw2711step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2711step0 raw2711step0Labels permutation56 hz
    mixedMoment B raw2711step1 raw2711step1Labels = mixedMoment B raw2711step2 raw2711step2Labels := by
      have ha : raw2711step2 = (fun i j => raw2711step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2711step2 raw2711step1; decide +kernel
      have hl : raw2711step2Labels = raw2711step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2711step1 raw2711step1Labels permutation8 permutation3
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw2712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2712step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2712 raw2712Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw2712 raw2712Labels = mixedMoment B raw2712step0 raw2712step0Labels := by
      have hz : ∀ j, raw2712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2712step0 = (fun i j => raw2712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2712step0 raw2712; decide +kernel
      have hl : raw2712step0Labels = raw2712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2712 raw2712Labels permutation346 hz
    mixedMoment B raw2712step0 raw2712step0Labels = mixedMoment B raw2712step1 raw2712step1Labels := by
      have ha : raw2712step1 = (fun i j => raw2712step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2712step1 raw2712step0; decide +kernel
      have hl : raw2712step1Labels = raw2712step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2712step0 raw2712step0Labels permutation151 permutation3
    mixedMoment B raw2712step1 raw2712step1Labels = mixedMoment B raw2712step2 raw2712step2Labels := by
      have ha : raw2712step2 = -raw2712step1 := by apply Matrix.ext; change ∀ i j, raw2712step2 i j = -(raw2712step1 i j); unfold raw2712step2 raw2712step1; decide +kernel
      have hl : raw2712step2Labels = raw2712step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw2713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2713step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2713step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2713 raw2713Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw2713 raw2713Labels = mixedMoment B raw2713step0 raw2713step0Labels := by
      have hz : ∀ j, raw2713 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2713step0 = (fun i j => raw2713 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2713step0 raw2713; decide +kernel
      have hl : raw2713step0Labels = raw2713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2713 raw2713Labels permutation265 hz
    mixedMoment B raw2713step0 raw2713step0Labels = mixedMoment B raw2713step1 raw2713step1Labels := by
      have ha : raw2713step1 = (fun i j => raw2713step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2713step1 raw2713step0; decide +kernel
      have hl : raw2713step1Labels = raw2713step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2713step0 raw2713step0Labels permutation151 permutation3
    mixedMoment B raw2713step1 raw2713step1Labels = mixedMoment B raw2713step2 raw2713step2Labels := by
      have ha : raw2713step2 = -raw2713step1 := by apply Matrix.ext; change ∀ i j, raw2713step2 i j = -(raw2713step1 i j); unfold raw2713step2 raw2713step1; decide +kernel
      have hl : raw2713step2Labels = raw2713step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw2714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2714step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2714step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2714step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2714step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2714step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2714 raw2714Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw2714 raw2714Labels = mixedMoment B raw2714step0 raw2714step0Labels := by
      have hz : ∀ j, raw2714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2714step0 = (fun i j => raw2714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2714step0 raw2714; decide +kernel
      have hl : raw2714step0Labels = raw2714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2714 raw2714Labels permutation346 hz
    mixedMoment B raw2714step0 raw2714step0Labels = mixedMoment B raw2714step1 raw2714step1Labels := by
      have hz : ∀ j, raw2714step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2714step1 = (fun i j => raw2714step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2714step1 raw2714step0; decide +kernel
      have hl : raw2714step1Labels = raw2714step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2714step0 raw2714step0Labels permutation56 hz
    mixedMoment B raw2714step1 raw2714step1Labels = mixedMoment B raw2714step2 raw2714step2Labels := by
      have ha : raw2714step2 = (fun i j => raw2714step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2714step2 raw2714step1; decide +kernel
      have hl : raw2714step2Labels = raw2714step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2714step1 raw2714step1Labels permutation31 permutation3
    mixedMoment B raw2714step2 raw2714step2Labels = mixedMoment B raw2714step3 raw2714step3Labels := by
      have ha : raw2714step3 = -raw2714step2 := by apply Matrix.ext; change ∀ i j, raw2714step3 i j = -(raw2714step2 i j); unfold raw2714step3 raw2714step2; decide +kernel
      have hl : raw2714step3Labels = raw2714step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw2715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2715step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2715step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2715step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2715step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw2715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2715 raw2715Labels = mixedMoment B node4040 node4040Labels := by
  calc
    mixedMoment B raw2715 raw2715Labels = mixedMoment B raw2715step0 raw2715step0Labels := by
      have hz : ∀ j, raw2715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2715step0 = (fun i j => raw2715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2715step0 raw2715; decide +kernel
      have hl : raw2715step0Labels = raw2715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2715 raw2715Labels permutation346 hz
    mixedMoment B raw2715step0 raw2715step0Labels = mixedMoment B raw2715step1 raw2715step1Labels := by
      have hz : ∀ j, raw2715step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2715step1 = (fun i j => raw2715step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2715step1 raw2715step0; decide +kernel
      have hl : raw2715step1Labels = raw2715step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2715step0 raw2715step0Labels permutation56 hz
    mixedMoment B raw2715step1 raw2715step1Labels = mixedMoment B raw2715step2 raw2715step2Labels := by
      have ha : raw2715step2 = (fun i j => raw2715step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2715step2 raw2715step1; decide +kernel
      have hl : raw2715step2Labels = raw2715step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2715step1 raw2715step1Labels permutation8 permutation3
    _ = mixedMoment B node4040 node4040Labels := by rfl

def raw2716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2716step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2716step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2716step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2716step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw2716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2716step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw2716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2716 raw2716Labels = mixedMoment B node2247 node2247Labels := by
  calc
    mixedMoment B raw2716 raw2716Labels = mixedMoment B raw2716step0 raw2716step0Labels := by
      have hz : ∀ j, raw2716 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2716step0 = (fun i j => raw2716 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2716step0 raw2716; decide +kernel
      have hl : raw2716step0Labels = raw2716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2716 raw2716Labels permutation346 hz
    mixedMoment B raw2716step0 raw2716step0Labels = mixedMoment B raw2716step1 raw2716step1Labels := by
      have hz : ∀ j, raw2716step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2716step1 = (fun i j => raw2716step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2716step1 raw2716step0; decide +kernel
      have hl : raw2716step1Labels = raw2716step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2716step0 raw2716step0Labels permutation56 hz
    mixedMoment B raw2716step1 raw2716step1Labels = mixedMoment B raw2716step2 raw2716step2Labels := by
      have ha : raw2716step2 = (fun i j => raw2716step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2716step2 raw2716step1; decide +kernel
      have hl : raw2716step2Labels = raw2716step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2716step1 raw2716step1Labels permutation29 permutation3
    mixedMoment B raw2716step2 raw2716step2Labels = mixedMoment B raw2716step3 raw2716step3Labels := by
      have ha : raw2716step3 = -raw2716step2 := by apply Matrix.ext; change ∀ i j, raw2716step3 i j = -(raw2716step2 i j); unfold raw2716step3 raw2716step2; decide +kernel
      have hl : raw2716step3Labels = raw2716step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2247 node2247Labels := by rfl

def raw2717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2717step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2717 raw2717Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw2717 raw2717Labels = mixedMoment B raw2717step0 raw2717step0Labels := by
      have hz : ∀ j, raw2717 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2717step0 = (fun i j => raw2717 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2717step0 raw2717; decide +kernel
      have hl : raw2717step0Labels = raw2717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2717 raw2717Labels permutation346 hz
    mixedMoment B raw2717step0 raw2717step0Labels = mixedMoment B raw2717step1 raw2717step1Labels := by
      have ha : raw2717step1 = (fun i j => raw2717step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2717step1 raw2717step0; decide +kernel
      have hl : raw2717step1Labels = raw2717step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2717step0 raw2717step0Labels permutation145 permutation3
    mixedMoment B raw2717step1 raw2717step1Labels = mixedMoment B raw2717step2 raw2717step2Labels := by
      have ha : raw2717step2 = -raw2717step1 := by apply Matrix.ext; change ∀ i j, raw2717step2 i j = -(raw2717step1 i j); unfold raw2717step2 raw2717step1; decide +kernel
      have hl : raw2717step2Labels = raw2717step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw2718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2718step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2718step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2718 raw2718Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw2718 raw2718Labels = mixedMoment B raw2718step0 raw2718step0Labels := by
      have hz : ∀ j, raw2718 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2718step0 = (fun i j => raw2718 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2718step0 raw2718; decide +kernel
      have hl : raw2718step0Labels = raw2718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2718 raw2718Labels permutation265 hz
    mixedMoment B raw2718step0 raw2718step0Labels = mixedMoment B raw2718step1 raw2718step1Labels := by
      have ha : raw2718step1 = (fun i j => raw2718step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2718step1 raw2718step0; decide +kernel
      have hl : raw2718step1Labels = raw2718step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2718step0 raw2718step0Labels permutation145 permutation3
    mixedMoment B raw2718step1 raw2718step1Labels = mixedMoment B raw2718step2 raw2718step2Labels := by
      have ha : raw2718step2 = -raw2718step1 := by apply Matrix.ext; change ∀ i j, raw2718step2 i j = -(raw2718step1 i j); unfold raw2718step2 raw2718step1; decide +kernel
      have hl : raw2718step2Labels = raw2718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw2719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2719step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2719step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2719step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2719step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2719step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2719step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2719 raw2719Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw2719 raw2719Labels = mixedMoment B raw2719step0 raw2719step0Labels := by
      have hz : ∀ j, raw2719 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2719step0 = (fun i j => raw2719 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2719step0 raw2719; decide +kernel
      have hl : raw2719step0Labels = raw2719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2719 raw2719Labels permutation346 hz
    mixedMoment B raw2719step0 raw2719step0Labels = mixedMoment B raw2719step1 raw2719step1Labels := by
      have hz : ∀ j, raw2719step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2719step1 = (fun i j => raw2719step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2719step1 raw2719step0; decide +kernel
      have hl : raw2719step1Labels = raw2719step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2719step0 raw2719step0Labels permutation56 hz
    mixedMoment B raw2719step1 raw2719step1Labels = mixedMoment B raw2719step2 raw2719step2Labels := by
      have ha : raw2719step2 = (fun i j => raw2719step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2719step2 raw2719step1; decide +kernel
      have hl : raw2719step2Labels = raw2719step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2719step1 raw2719step1Labels permutation31 permutation3
    mixedMoment B raw2719step2 raw2719step2Labels = mixedMoment B raw2719step3 raw2719step3Labels := by
      have ha : raw2719step3 = -raw2719step2 := by apply Matrix.ext; change ∀ i j, raw2719step3 i j = -(raw2719step2 i j); unfold raw2719step3 raw2719step2; decide +kernel
      have hl : raw2719step3Labels = raw2719step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw2720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2720step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2720step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![3, -3, 0]]
def raw2720step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2720step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2720step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2720step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2720 raw2720Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw2720 raw2720Labels = mixedMoment B raw2720step0 raw2720step0Labels := by
      have hz : ∀ j, raw2720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2720step0 = (fun i j => raw2720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2720step0 raw2720; decide +kernel
      have hl : raw2720step0Labels = raw2720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2720 raw2720Labels permutation346 hz
    mixedMoment B raw2720step0 raw2720step0Labels = mixedMoment B raw2720step1 raw2720step1Labels := by
      have hz : ∀ j, raw2720step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2720step1 = (fun i j => raw2720step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2720step1 raw2720step0; decide +kernel
      have hl : raw2720step1Labels = raw2720step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2720step0 raw2720step0Labels permutation56 hz
    mixedMoment B raw2720step1 raw2720step1Labels = mixedMoment B raw2720step2 raw2720step2Labels := by
      have ha : raw2720step2 = (fun i j => raw2720step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2720step2 raw2720step1; decide +kernel
      have hl : raw2720step2Labels = raw2720step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2720step1 raw2720step1Labels permutation29 permutation3
    mixedMoment B raw2720step2 raw2720step2Labels = mixedMoment B raw2720step3 raw2720step3Labels := by
      have ha : raw2720step3 = -raw2720step2 := by apply Matrix.ext; change ∀ i j, raw2720step3 i j = -(raw2720step2 i j); unfold raw2720step3 raw2720step2; decide +kernel
      have hl : raw2720step3Labels = raw2720step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw2721 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2721step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2721 raw2721Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2721 raw2721Labels = mixedMoment B raw2721step0 raw2721step0Labels := by
      have hz : ∀ j, raw2721 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2721step0 = (fun i j => raw2721 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2721step0 raw2721; decide +kernel
      have hl : raw2721step0Labels = raw2721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2721 raw2721Labels permutation346 hz
    mixedMoment B raw2721step0 raw2721step0Labels = mixedMoment B raw2721step1 raw2721step1Labels := by
      have ha : raw2721step1 = (fun i j => raw2721step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2721step1 raw2721step0; decide +kernel
      have hl : raw2721step1Labels = raw2721step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2721step0 raw2721step0Labels permutation137 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2722 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2722 raw2722Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2722 raw2722Labels = mixedMoment B raw2722step0 raw2722step0Labels := by
      have hz : ∀ j, raw2722 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2722step0 = (fun i j => raw2722 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2722step0 raw2722; decide +kernel
      have hl : raw2722step0Labels = raw2722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2722 raw2722Labels permutation265 hz
    mixedMoment B raw2722step0 raw2722step0Labels = mixedMoment B raw2722step1 raw2722step1Labels := by
      have ha : raw2722step1 = (fun i j => raw2722step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2722step1 raw2722step0; decide +kernel
      have hl : raw2722step1Labels = raw2722step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2722step0 raw2722step0Labels permutation137 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2723 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2723step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 0, 2]]
def raw2723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2723step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2723step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2723step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2723step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2723step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2723step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2723 raw2723Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2723 raw2723Labels = mixedMoment B raw2723step0 raw2723step0Labels := by
      have hz : ∀ j, raw2723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2723step0 = (fun i j => raw2723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2723step0 raw2723; decide +kernel
      have hl : raw2723step0Labels = raw2723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2723 raw2723Labels permutation434 hz
    mixedMoment B raw2723step0 raw2723step0Labels = mixedMoment B raw2723step1 raw2723step1Labels := by
      have hz : ∀ j, raw2723step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2723step1 = (fun i j => raw2723step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2723step1 raw2723step0; decide +kernel
      have hl : raw2723step1Labels = raw2723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2723step0 raw2723step0Labels permutation80 hz
    mixedMoment B raw2723step1 raw2723step1Labels = mixedMoment B raw2723step2 raw2723step2Labels := by
      have hz : ∀ j, raw2723step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2723step2 = (fun i j => raw2723step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2723step2 raw2723step1; decide +kernel
      have hl : raw2723step2Labels = raw2723step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2723step1 raw2723step1Labels permutation14 hz
    mixedMoment B raw2723step2 raw2723step2Labels = mixedMoment B raw2723step3 raw2723step3Labels := by
      have ha : raw2723step3 = (fun i j => raw2723step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw2723step3 raw2723step2; decide +kernel
      have hl : raw2723step3Labels = raw2723step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2723step2 raw2723step2Labels permutation7 permutation7
    mixedMoment B raw2723step3 raw2723step3Labels = mixedMoment B raw2723step4 raw2723step4Labels := by
      have ha : raw2723step4 = -raw2723step3 := by apply Matrix.ext; change ∀ i j, raw2723step4 i j = -(raw2723step3 i j); unfold raw2723step4 raw2723step3; decide +kernel
      have hl : raw2723step4Labels = raw2723step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2723step4 raw2723step4Labels = mixedMoment B raw2723step5 raw2723step5Labels := by
      have ha : raw2723step5 = raw2723step4 := by apply Matrix.ext; unfold raw2723step5 raw2723step4; decide +kernel
      have hl : raw2723step4Labels = labelEmbedding10 ∘ raw2723step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2723step4 raw2723step4Labels raw2723step5Labels labelEmbedding10 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw2724 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2]]
def raw2724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2724step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2724step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 0, 2]]
def raw2724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2724step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2724step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2724step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2724step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2724step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2724step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2724 raw2724Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2724 raw2724Labels = mixedMoment B raw2724step0 raw2724step0Labels := by
      have hz : ∀ j, raw2724 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2724step0 = (fun i j => raw2724 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2724step0 raw2724; decide +kernel
      have hl : raw2724step0Labels = raw2724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2724 raw2724Labels permutation520 hz
    mixedMoment B raw2724step0 raw2724step0Labels = mixedMoment B raw2724step1 raw2724step1Labels := by
      have hz : ∀ j, raw2724step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2724step1 = (fun i j => raw2724step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2724step1 raw2724step0; decide +kernel
      have hl : raw2724step1Labels = raw2724step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2724step0 raw2724step0Labels permutation80 hz
    mixedMoment B raw2724step1 raw2724step1Labels = mixedMoment B raw2724step2 raw2724step2Labels := by
      have hz : ∀ j, raw2724step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2724step2 = (fun i j => raw2724step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2724step2 raw2724step1; decide +kernel
      have hl : raw2724step2Labels = raw2724step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2724step1 raw2724step1Labels permutation14 hz
    mixedMoment B raw2724step2 raw2724step2Labels = mixedMoment B raw2724step3 raw2724step3Labels := by
      have ha : raw2724step3 = (fun i j => raw2724step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw2724step3 raw2724step2; decide +kernel
      have hl : raw2724step3Labels = raw2724step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2724step2 raw2724step2Labels permutation7 permutation7
    mixedMoment B raw2724step3 raw2724step3Labels = mixedMoment B raw2724step4 raw2724step4Labels := by
      have ha : raw2724step4 = -raw2724step3 := by apply Matrix.ext; change ∀ i j, raw2724step4 i j = -(raw2724step3 i j); unfold raw2724step4 raw2724step3; decide +kernel
      have hl : raw2724step4Labels = raw2724step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2724step4 raw2724step4Labels = mixedMoment B raw2724step5 raw2724step5Labels := by
      have ha : raw2724step5 = raw2724step4 := by apply Matrix.ext; unfold raw2724step5 raw2724step4; decide +kernel
      have hl : raw2724step4Labels = labelEmbedding10 ∘ raw2724step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2724step4 raw2724step4Labels raw2724step5Labels labelEmbedding10 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw2725 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2725step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2725 raw2725Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw2725 raw2725Labels = mixedMoment B raw2725step0 raw2725step0Labels := by
      have hz : ∀ j, raw2725 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2725step0 = (fun i j => raw2725 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2725step0 raw2725; decide +kernel
      have hl : raw2725step0Labels = raw2725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2725 raw2725Labels permutation346 hz
    mixedMoment B raw2725step0 raw2725step0Labels = mixedMoment B raw2725step1 raw2725step1Labels := by
      have hz : ∀ j, raw2725step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2725step1 = (fun i j => raw2725step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2725step1 raw2725step0; decide +kernel
      have hl : raw2725step1Labels = raw2725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2725step0 raw2725step0Labels permutation56 hz
    mixedMoment B raw2725step1 raw2725step1Labels = mixedMoment B raw2725step2 raw2725step2Labels := by
      have ha : raw2725step2 = (fun i j => raw2725step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2725step2 raw2725step1; decide +kernel
      have hl : raw2725step2Labels = raw2725step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2725step1 raw2725step1Labels permutation29 permutation2
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw2726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2726step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw2726step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2726step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2726step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2726step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2726step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2726 raw2726Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2726 raw2726Labels = mixedMoment B raw2726step0 raw2726step0Labels := by
      have hz : ∀ j, raw2726 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2726step0 = (fun i j => raw2726 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2726step0 raw2726; decide +kernel
      have hl : raw2726step0Labels = raw2726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2726 raw2726Labels permutation346 hz
    mixedMoment B raw2726step0 raw2726step0Labels = mixedMoment B raw2726step1 raw2726step1Labels := by
      have ha : raw2726step1 = (fun i j => raw2726step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2726step1 raw2726step0; decide +kernel
      have hl : raw2726step1Labels = raw2726step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2726step0 raw2726step0Labels permutation50 permutation4
    mixedMoment B raw2726step1 raw2726step1Labels = mixedMoment B raw2726step2 raw2726step2Labels := by
      have ha : raw2726step2 = -raw2726step1 := by apply Matrix.ext; change ∀ i j, raw2726step2 i j = -(raw2726step1 i j); unfold raw2726step2 raw2726step1; decide +kernel
      have hl : raw2726step2Labels = raw2726step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2726step2 raw2726step2Labels = mixedMoment B raw2726step3 raw2726step3Labels := by
      have ha : raw2726step3 = raw2726step2 := by apply Matrix.ext; unfold raw2726step3 raw2726step2; decide +kernel
      have hl : raw2726step2Labels = labelEmbedding7 ∘ raw2726step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2726step2 raw2726step2Labels raw2726step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw2727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2727 raw2727Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw2727 raw2727Labels = mixedMoment B raw2727step0 raw2727step0Labels := by
      have ha : raw2727step0 = (fun i j => raw2727 (permutation623 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2727step0 raw2727; decide +kernel
      have hl : raw2727step0Labels = raw2727Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2727 raw2727Labels permutation623 permutation2
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw2728 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2728step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2728step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2728step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2728 raw2728Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2728 raw2728Labels = mixedMoment B raw2728step0 raw2728step0Labels := by
      have hz : ∀ j, raw2728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2728step0 = (fun i j => raw2728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2728step0 raw2728; decide +kernel
      have hl : raw2728step0Labels = raw2728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2728 raw2728Labels permutation434 hz
    mixedMoment B raw2728step0 raw2728step0Labels = mixedMoment B raw2728step1 raw2728step1Labels := by
      have hz : ∀ j, raw2728step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2728step1 = (fun i j => raw2728step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2728step1 raw2728step0; decide +kernel
      have hl : raw2728step1Labels = raw2728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2728step0 raw2728step0Labels permutation80 hz
    mixedMoment B raw2728step1 raw2728step1Labels = mixedMoment B raw2728step2 raw2728step2Labels := by
      have ha : raw2728step2 = (fun i j => raw2728step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2728step2 raw2728step1; decide +kernel
      have hl : raw2728step2Labels = raw2728step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2728step1 raw2728step1Labels permutation8 permutation6
    mixedMoment B raw2728step2 raw2728step2Labels = mixedMoment B raw2728step3 raw2728step3Labels := by
      have ha : raw2728step3 = raw2728step2 := by apply Matrix.ext; unfold raw2728step3 raw2728step2; decide +kernel
      have hl : raw2728step2Labels = labelEmbedding9 ∘ raw2728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2728step2 raw2728step2Labels raw2728step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2]]
def raw2729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2729step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2729step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2729step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2729step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2729step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2729 raw2729Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2729 raw2729Labels = mixedMoment B raw2729step0 raw2729step0Labels := by
      have hz : ∀ j, raw2729 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2729step0 = (fun i j => raw2729 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2729step0 raw2729; decide +kernel
      have hl : raw2729step0Labels = raw2729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2729 raw2729Labels permutation520 hz
    mixedMoment B raw2729step0 raw2729step0Labels = mixedMoment B raw2729step1 raw2729step1Labels := by
      have hz : ∀ j, raw2729step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2729step1 = (fun i j => raw2729step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2729step1 raw2729step0; decide +kernel
      have hl : raw2729step1Labels = raw2729step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2729step0 raw2729step0Labels permutation80 hz
    mixedMoment B raw2729step1 raw2729step1Labels = mixedMoment B raw2729step2 raw2729step2Labels := by
      have ha : raw2729step2 = (fun i j => raw2729step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2729step2 raw2729step1; decide +kernel
      have hl : raw2729step2Labels = raw2729step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2729step1 raw2729step1Labels permutation8 permutation6
    mixedMoment B raw2729step2 raw2729step2Labels = mixedMoment B raw2729step3 raw2729step3Labels := by
      have ha : raw2729step3 = raw2729step2 := by apply Matrix.ext; unfold raw2729step3 raw2729step2; decide +kernel
      have hl : raw2729step2Labels = labelEmbedding9 ∘ raw2729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2729step2 raw2729step2Labels raw2729step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2730Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2730step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2730step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2730 raw2730Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2730 raw2730Labels = mixedMoment B raw2730step0 raw2730step0Labels := by
      have hz : ∀ j, raw2730 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2730step0 = (fun i j => raw2730 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2730step0 raw2730; decide +kernel
      have hl : raw2730step0Labels = raw2730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2730 raw2730Labels permutation346 hz
    mixedMoment B raw2730step0 raw2730step0Labels = mixedMoment B raw2730step1 raw2730step1Labels := by
      have ha : raw2730step1 = (fun i j => raw2730step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2730step1 raw2730step0; decide +kernel
      have hl : raw2730step1Labels = raw2730step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2730step0 raw2730step0Labels permutation128 permutation2
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw2731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2731Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2731step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw2731step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2731step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2731step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2731step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2731 raw2731Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2731 raw2731Labels = mixedMoment B raw2731step0 raw2731step0Labels := by
      have hz : ∀ j, raw2731 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2731step0 = (fun i j => raw2731 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2731step0 raw2731; decide +kernel
      have hl : raw2731step0Labels = raw2731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2731 raw2731Labels permutation265 hz
    mixedMoment B raw2731step0 raw2731step0Labels = mixedMoment B raw2731step1 raw2731step1Labels := by
      have ha : raw2731step1 = (fun i j => raw2731step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2731step1 raw2731step0; decide +kernel
      have hl : raw2731step1Labels = raw2731step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2731step0 raw2731step0Labels permutation50 permutation4
    mixedMoment B raw2731step1 raw2731step1Labels = mixedMoment B raw2731step2 raw2731step2Labels := by
      have ha : raw2731step2 = -raw2731step1 := by apply Matrix.ext; change ∀ i j, raw2731step2 i j = -(raw2731step1 i j); unfold raw2731step2 raw2731step1; decide +kernel
      have hl : raw2731step2Labels = raw2731step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2731step2 raw2731step2Labels = mixedMoment B raw2731step3 raw2731step3Labels := by
      have ha : raw2731step3 = raw2731step2 := by apply Matrix.ext; unfold raw2731step3 raw2731step2; decide +kernel
      have hl : raw2731step2Labels = labelEmbedding7 ∘ raw2731step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2731step2 raw2731step2Labels raw2731step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw2732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2732Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2732step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2732 raw2732Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw2732 raw2732Labels = mixedMoment B raw2732step0 raw2732step0Labels := by
      have ha : raw2732step0 = (fun i j => raw2732 (permutation602 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2732step0 raw2732; decide +kernel
      have hl : raw2732step0Labels = raw2732Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2732 raw2732Labels permutation602 permutation2
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw2733 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2733Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2733step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2733step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2733step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2733step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2733step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2733 raw2733Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2733 raw2733Labels = mixedMoment B raw2733step0 raw2733step0Labels := by
      have hz : ∀ j, raw2733 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2733step0 = (fun i j => raw2733 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2733step0 raw2733; decide +kernel
      have hl : raw2733step0Labels = raw2733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2733 raw2733Labels permutation434 hz
    mixedMoment B raw2733step0 raw2733step0Labels = mixedMoment B raw2733step1 raw2733step1Labels := by
      have hz : ∀ j, raw2733step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2733step1 = (fun i j => raw2733step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2733step1 raw2733step0; decide +kernel
      have hl : raw2733step1Labels = raw2733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2733step0 raw2733step0Labels permutation56 hz
    mixedMoment B raw2733step1 raw2733step1Labels = mixedMoment B raw2733step2 raw2733step2Labels := by
      have ha : raw2733step2 = (fun i j => raw2733step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2733step2 raw2733step1; decide +kernel
      have hl : raw2733step2Labels = raw2733step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2733step1 raw2733step1Labels permutation8 permutation6
    mixedMoment B raw2733step2 raw2733step2Labels = mixedMoment B raw2733step3 raw2733step3Labels := by
      have ha : raw2733step3 = raw2733step2 := by apply Matrix.ext; unfold raw2733step3 raw2733step2; decide +kernel
      have hl : raw2733step2Labels = labelEmbedding9 ∘ raw2733step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2733step2 raw2733step2Labels raw2733step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2]]
def raw2734Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2734step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2734step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2734step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2734step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2734step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2734step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2734step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2734 raw2734Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2734 raw2734Labels = mixedMoment B raw2734step0 raw2734step0Labels := by
      have hz : ∀ j, raw2734 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2734step0 = (fun i j => raw2734 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2734step0 raw2734; decide +kernel
      have hl : raw2734step0Labels = raw2734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2734 raw2734Labels permutation520 hz
    mixedMoment B raw2734step0 raw2734step0Labels = mixedMoment B raw2734step1 raw2734step1Labels := by
      have hz : ∀ j, raw2734step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2734step1 = (fun i j => raw2734step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2734step1 raw2734step0; decide +kernel
      have hl : raw2734step1Labels = raw2734step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2734step0 raw2734step0Labels permutation56 hz
    mixedMoment B raw2734step1 raw2734step1Labels = mixedMoment B raw2734step2 raw2734step2Labels := by
      have ha : raw2734step2 = (fun i j => raw2734step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2734step2 raw2734step1; decide +kernel
      have hl : raw2734step2Labels = raw2734step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2734step1 raw2734step1Labels permutation8 permutation6
    mixedMoment B raw2734step2 raw2734step2Labels = mixedMoment B raw2734step3 raw2734step3Labels := by
      have ha : raw2734step3 = raw2734step2 := by apply Matrix.ext; unfold raw2734step3 raw2734step2; decide +kernel
      have hl : raw2734step2Labels = labelEmbedding9 ∘ raw2734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2734step2 raw2734step2Labels raw2734step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2735Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2735step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2735step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2735 raw2735Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw2735 raw2735Labels = mixedMoment B raw2735step0 raw2735step0Labels := by
      have hz : ∀ j, raw2735 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2735step0 = (fun i j => raw2735 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2735step0 raw2735; decide +kernel
      have hl : raw2735step0Labels = raw2735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2735 raw2735Labels permutation265 hz
    mixedMoment B raw2735step0 raw2735step0Labels = mixedMoment B raw2735step1 raw2735step1Labels := by
      have ha : raw2735step1 = (fun i j => raw2735step0 (permutation128 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2735step1 raw2735step0; decide +kernel
      have hl : raw2735step1Labels = raw2735step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2735step0 raw2735step0Labels permutation128 permutation2
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw2736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2736Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2736step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2736step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2736step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2736step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw2736step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2736step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2736step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2736step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2736step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2736 raw2736Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2736 raw2736Labels = mixedMoment B raw2736step0 raw2736step0Labels := by
      have hz : ∀ j, raw2736 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2736step0 = (fun i j => raw2736 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2736step0 raw2736; decide +kernel
      have hl : raw2736step0Labels = raw2736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2736 raw2736Labels permutation346 hz
    mixedMoment B raw2736step0 raw2736step0Labels = mixedMoment B raw2736step1 raw2736step1Labels := by
      have hz : ∀ j, raw2736step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2736step1 = (fun i j => raw2736step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2736step1 raw2736step0; decide +kernel
      have hl : raw2736step1Labels = raw2736step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2736step0 raw2736step0Labels permutation56 hz
    mixedMoment B raw2736step1 raw2736step1Labels = mixedMoment B raw2736step2 raw2736step2Labels := by
      have ha : raw2736step2 = (fun i j => raw2736step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2736step2 raw2736step1; decide +kernel
      have hl : raw2736step2Labels = raw2736step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2736step1 raw2736step1Labels permutation13 permutation4
    mixedMoment B raw2736step2 raw2736step2Labels = mixedMoment B raw2736step3 raw2736step3Labels := by
      have ha : raw2736step3 = -raw2736step2 := by apply Matrix.ext; change ∀ i j, raw2736step3 i j = -(raw2736step2 i j); unfold raw2736step3 raw2736step2; decide +kernel
      have hl : raw2736step3Labels = raw2736step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2736step3 raw2736step3Labels = mixedMoment B raw2736step4 raw2736step4Labels := by
      have ha : raw2736step4 = raw2736step3 := by apply Matrix.ext; unfold raw2736step4 raw2736step3; decide +kernel
      have hl : raw2736step3Labels = labelEmbedding7 ∘ raw2736step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2736step3 raw2736step3Labels raw2736step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw2737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2737Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2737step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2737step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2737step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2737step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2737 raw2737Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2737 raw2737Labels = mixedMoment B raw2737step0 raw2737step0Labels := by
      have hz : ∀ j, raw2737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2737step0 = (fun i j => raw2737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2737step0 raw2737; decide +kernel
      have hl : raw2737step0Labels = raw2737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2737 raw2737Labels permutation346 hz
    mixedMoment B raw2737step0 raw2737step0Labels = mixedMoment B raw2737step1 raw2737step1Labels := by
      have ha : raw2737step1 = (fun i j => raw2737step0 (permutation92 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2737step1 raw2737step0; decide +kernel
      have hl : raw2737step1Labels = raw2737step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2737step0 raw2737step0Labels permutation92 permutation3
    mixedMoment B raw2737step1 raw2737step1Labels = mixedMoment B raw2737step2 raw2737step2Labels := by
      have ha : raw2737step2 = -raw2737step1 := by apply Matrix.ext; change ∀ i j, raw2737step2 i j = -(raw2737step1 i j); unfold raw2737step2 raw2737step1; decide +kernel
      have hl : raw2737step2Labels = raw2737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2737step2 raw2737step2Labels = mixedMoment B raw2737step3 raw2737step3Labels := by
      have ha : raw2737step3 = raw2737step2 := by apply Matrix.ext; unfold raw2737step3 raw2737step2; decide +kernel
      have hl : raw2737step2Labels = labelEmbedding6 ∘ raw2737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2737step2 raw2737step2Labels raw2737step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw2738 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2738Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2]]
def raw2738step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2738step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2738step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2738step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2738 raw2738Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2738 raw2738Labels = mixedMoment B raw2738step0 raw2738step0Labels := by
      have hz : ∀ j, raw2738 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2738step0 = (fun i j => raw2738 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2738step0 raw2738; decide +kernel
      have hl : raw2738step0Labels = raw2738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2738 raw2738Labels permutation265 hz
    mixedMoment B raw2738step0 raw2738step0Labels = mixedMoment B raw2738step1 raw2738step1Labels := by
      have ha : raw2738step1 = (fun i j => raw2738step0 (permutation92 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2738step1 raw2738step0; decide +kernel
      have hl : raw2738step1Labels = raw2738step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2738step0 raw2738step0Labels permutation92 permutation3
    mixedMoment B raw2738step1 raw2738step1Labels = mixedMoment B raw2738step2 raw2738step2Labels := by
      have ha : raw2738step2 = -raw2738step1 := by apply Matrix.ext; change ∀ i j, raw2738step2 i j = -(raw2738step1 i j); unfold raw2738step2 raw2738step1; decide +kernel
      have hl : raw2738step2Labels = raw2738step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2738step2 raw2738step2Labels = mixedMoment B raw2738step3 raw2738step3Labels := by
      have ha : raw2738step3 = raw2738step2 := by apply Matrix.ext; unfold raw2738step3 raw2738step2; decide +kernel
      have hl : raw2738step2Labels = labelEmbedding6 ∘ raw2738step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2738step2 raw2738step2Labels raw2738step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw2739 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![-2, 0, 2]]
def raw2739Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2739step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2739step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2739step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![-2, 0, 2]]
def raw2739step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2739step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2739step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2739 raw2739Labels = mixedMoment B node5456 node5456Labels := by
  calc
    mixedMoment B raw2739 raw2739Labels = mixedMoment B raw2739step0 raw2739step0Labels := by
      have hz : ∀ j, raw2739 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2739step0 = (fun i j => raw2739 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2739step0 raw2739; decide +kernel
      have hl : raw2739step0Labels = raw2739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2739 raw2739Labels permutation520 hz
    mixedMoment B raw2739step0 raw2739step0Labels = mixedMoment B raw2739step1 raw2739step1Labels := by
      have hz : ∀ j, raw2739step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2739step1 = (fun i j => raw2739step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2739step1 raw2739step0; decide +kernel
      have hl : raw2739step1Labels = raw2739step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2739step0 raw2739step0Labels permutation80 hz
    mixedMoment B raw2739step1 raw2739step1Labels = mixedMoment B raw2739step2 raw2739step2Labels := by
      have hz : ∀ j, raw2739step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2739step2 = (fun i j => raw2739step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2739step2 raw2739step1; decide +kernel
      have hl : raw2739step2Labels = raw2739step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2739step1 raw2739step1Labels permutation14 hz
    mixedMoment B raw2739step2 raw2739step2Labels = mixedMoment B raw2739step3 raw2739step3Labels := by
      have ha : raw2739step3 = (fun i j => raw2739step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2739step3 raw2739step2; decide +kernel
      have hl : raw2739step3Labels = raw2739step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2739step2 raw2739step2Labels permutation6 permutation2
    _ = mixedMoment B node5456 node5456Labels := by rfl

def raw2740 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2740Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2740step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2740step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![-3, 1, 2]]
def raw2740step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2740step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2740step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2740 raw2740Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2740 raw2740Labels = mixedMoment B raw2740step0 raw2740step0Labels := by
      have hz : ∀ j, raw2740 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2740step0 = (fun i j => raw2740 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2740step0 raw2740; decide +kernel
      have hl : raw2740step0Labels = raw2740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2740 raw2740Labels permutation346 hz
    mixedMoment B raw2740step0 raw2740step0Labels = mixedMoment B raw2740step1 raw2740step1Labels := by
      have hz : ∀ j, raw2740step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2740step1 = (fun i j => raw2740step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2740step1 raw2740step0; decide +kernel
      have hl : raw2740step1Labels = raw2740step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2740step0 raw2740step0Labels permutation56 hz
    mixedMoment B raw2740step1 raw2740step1Labels = mixedMoment B raw2740step2 raw2740step2Labels := by
      have ha : raw2740step2 = (fun i j => raw2740step1 (permutation27 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2740step2 raw2740step1; decide +kernel
      have hl : raw2740step2Labels = raw2740step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2740step1 raw2740step1Labels permutation27 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw2741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2741Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2741step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2741step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2741step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2741step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2741step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw2741step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2741step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2741step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2741step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2741step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2741 raw2741Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2741 raw2741Labels = mixedMoment B raw2741step0 raw2741step0Labels := by
      have hz : ∀ j, raw2741 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2741step0 = (fun i j => raw2741 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2741step0 raw2741; decide +kernel
      have hl : raw2741step0Labels = raw2741Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2741 raw2741Labels permutation346 hz
    mixedMoment B raw2741step0 raw2741step0Labels = mixedMoment B raw2741step1 raw2741step1Labels := by
      have hz : ∀ j, raw2741step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2741step1 = (fun i j => raw2741step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2741step1 raw2741step0; decide +kernel
      have hl : raw2741step1Labels = raw2741step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2741step0 raw2741step0Labels permutation56 hz
    mixedMoment B raw2741step1 raw2741step1Labels = mixedMoment B raw2741step2 raw2741step2Labels := by
      have ha : raw2741step2 = (fun i j => raw2741step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2741step2 raw2741step1; decide +kernel
      have hl : raw2741step2Labels = raw2741step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2741step1 raw2741step1Labels permutation12 permutation4
    mixedMoment B raw2741step2 raw2741step2Labels = mixedMoment B raw2741step3 raw2741step3Labels := by
      have ha : raw2741step3 = -raw2741step2 := by apply Matrix.ext; change ∀ i j, raw2741step3 i j = -(raw2741step2 i j); unfold raw2741step3 raw2741step2; decide +kernel
      have hl : raw2741step3Labels = raw2741step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2741step3 raw2741step3Labels = mixedMoment B raw2741step4 raw2741step4Labels := by
      have ha : raw2741step4 = raw2741step3 := by apply Matrix.ext; unfold raw2741step4 raw2741step3; decide +kernel
      have hl : raw2741step3Labels = labelEmbedding7 ∘ raw2741step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2741step3 raw2741step3Labels raw2741step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw2742 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2742Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2742step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2742step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2742step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2742step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2742 raw2742Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2742 raw2742Labels = mixedMoment B raw2742step0 raw2742step0Labels := by
      have hz : ∀ j, raw2742 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2742step0 = (fun i j => raw2742 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2742step0 raw2742; decide +kernel
      have hl : raw2742step0Labels = raw2742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2742 raw2742Labels permutation346 hz
    mixedMoment B raw2742step0 raw2742step0Labels = mixedMoment B raw2742step1 raw2742step1Labels := by
      have ha : raw2742step1 = (fun i j => raw2742step0 (permutation116 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2742step1 raw2742step0; decide +kernel
      have hl : raw2742step1Labels = raw2742step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2742step0 raw2742step0Labels permutation116 permutation3
    mixedMoment B raw2742step1 raw2742step1Labels = mixedMoment B raw2742step2 raw2742step2Labels := by
      have ha : raw2742step2 = -raw2742step1 := by apply Matrix.ext; change ∀ i j, raw2742step2 i j = -(raw2742step1 i j); unfold raw2742step2 raw2742step1; decide +kernel
      have hl : raw2742step2Labels = raw2742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2742step2 raw2742step2Labels = mixedMoment B raw2742step3 raw2742step3Labels := by
      have ha : raw2742step3 = raw2742step2 := by apply Matrix.ext; unfold raw2742step3 raw2742step2; decide +kernel
      have hl : raw2742step2Labels = labelEmbedding6 ∘ raw2742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2742step2 raw2742step2Labels raw2742step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw2743 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2743Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2743step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2743step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2743step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2743step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2743 raw2743Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2743 raw2743Labels = mixedMoment B raw2743step0 raw2743step0Labels := by
      have hz : ∀ j, raw2743 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2743step0 = (fun i j => raw2743 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2743step0 raw2743; decide +kernel
      have hl : raw2743step0Labels = raw2743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2743 raw2743Labels permutation265 hz
    mixedMoment B raw2743step0 raw2743step0Labels = mixedMoment B raw2743step1 raw2743step1Labels := by
      have ha : raw2743step1 = (fun i j => raw2743step0 (permutation116 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2743step1 raw2743step0; decide +kernel
      have hl : raw2743step1Labels = raw2743step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2743step0 raw2743step0Labels permutation116 permutation3
    mixedMoment B raw2743step1 raw2743step1Labels = mixedMoment B raw2743step2 raw2743step2Labels := by
      have ha : raw2743step2 = -raw2743step1 := by apply Matrix.ext; change ∀ i j, raw2743step2 i j = -(raw2743step1 i j); unfold raw2743step2 raw2743step1; decide +kernel
      have hl : raw2743step2Labels = raw2743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2743step2 raw2743step2Labels = mixedMoment B raw2743step3 raw2743step3Labels := by
      have ha : raw2743step3 = raw2743step2 := by apply Matrix.ext; unfold raw2743step3 raw2743step2; decide +kernel
      have hl : raw2743step2Labels = labelEmbedding6 ∘ raw2743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2743step2 raw2743step2Labels raw2743step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw2744 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2744Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2744step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2744step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2]]
def raw2744step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2744step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![2, -2, 0], ![-2, 0, 2]]
def raw2744step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2744step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2744step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2744 raw2744Labels = mixedMoment B node5456 node5456Labels := by
  calc
    mixedMoment B raw2744 raw2744Labels = mixedMoment B raw2744step0 raw2744step0Labels := by
      have hz : ∀ j, raw2744 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2744step0 = (fun i j => raw2744 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2744step0 raw2744; decide +kernel
      have hl : raw2744step0Labels = raw2744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2744 raw2744Labels permutation434 hz
    mixedMoment B raw2744step0 raw2744step0Labels = mixedMoment B raw2744step1 raw2744step1Labels := by
      have hz : ∀ j, raw2744step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2744step1 = (fun i j => raw2744step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2744step1 raw2744step0; decide +kernel
      have hl : raw2744step1Labels = raw2744step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2744step0 raw2744step0Labels permutation80 hz
    mixedMoment B raw2744step1 raw2744step1Labels = mixedMoment B raw2744step2 raw2744step2Labels := by
      have hz : ∀ j, raw2744step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2744step2 = (fun i j => raw2744step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2744step2 raw2744step1; decide +kernel
      have hl : raw2744step2Labels = raw2744step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2744step1 raw2744step1Labels permutation14 hz
    mixedMoment B raw2744step2 raw2744step2Labels = mixedMoment B raw2744step3 raw2744step3Labels := by
      have ha : raw2744step3 = (fun i j => raw2744step2 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2744step3 raw2744step2; decide +kernel
      have hl : raw2744step3Labels = raw2744step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2744step2 raw2744step2Labels permutation6 permutation2
    _ = mixedMoment B node5456 node5456Labels := by rfl

def raw2745 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 1, 2]]
def raw2745Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-3, 1, 2]]
def raw2745step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2745step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![-3, 1, 2]]
def raw2745step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2745step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2745step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2745 raw2745Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2745 raw2745Labels = mixedMoment B raw2745step0 raw2745step0Labels := by
      have hz : ∀ j, raw2745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2745step0 = (fun i j => raw2745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2745step0 raw2745; decide +kernel
      have hl : raw2745step0Labels = raw2745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2745 raw2745Labels permutation346 hz
    mixedMoment B raw2745step0 raw2745step0Labels = mixedMoment B raw2745step1 raw2745step1Labels := by
      have hz : ∀ j, raw2745step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2745step1 = (fun i j => raw2745step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2745step1 raw2745step0; decide +kernel
      have hl : raw2745step1Labels = raw2745step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2745step0 raw2745step0Labels permutation56 hz
    mixedMoment B raw2745step1 raw2745step1Labels = mixedMoment B raw2745step2 raw2745step2Labels := by
      have ha : raw2745step2 = (fun i j => raw2745step1 (permutation26 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2745step2 raw2745step1; decide +kernel
      have hl : raw2745step2Labels = raw2745step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2745step1 raw2745step1Labels permutation26 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw2746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2746Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2746step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2746step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2746step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2746step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2746step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2746step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2746step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2746step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2746step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2746 raw2746Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw2746 raw2746Labels = mixedMoment B raw2746step0 raw2746step0Labels := by
      have hz : ∀ j, raw2746 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2746step0 = (fun i j => raw2746 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2746step0 raw2746; decide +kernel
      have hl : raw2746step0Labels = raw2746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2746 raw2746Labels permutation346 hz
    mixedMoment B raw2746step0 raw2746step0Labels = mixedMoment B raw2746step1 raw2746step1Labels := by
      have hz : ∀ j, raw2746step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2746step1 = (fun i j => raw2746step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2746step1 raw2746step0; decide +kernel
      have hl : raw2746step1Labels = raw2746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2746step0 raw2746step0Labels permutation56 hz
    mixedMoment B raw2746step1 raw2746step1Labels = mixedMoment B raw2746step2 raw2746step2Labels := by
      have ha : raw2746step2 = (fun i j => raw2746step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2746step2 raw2746step1; decide +kernel
      have hl : raw2746step2Labels = raw2746step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2746step1 raw2746step1Labels permutation8 permutation4
    mixedMoment B raw2746step2 raw2746step2Labels = mixedMoment B raw2746step3 raw2746step3Labels := by
      have ha : raw2746step3 = -raw2746step2 := by apply Matrix.ext; change ∀ i j, raw2746step3 i j = -(raw2746step2 i j); unfold raw2746step3 raw2746step2; decide +kernel
      have hl : raw2746step3Labels = raw2746step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2746step3 raw2746step3Labels = mixedMoment B raw2746step4 raw2746step4Labels := by
      have ha : raw2746step4 = raw2746step3 := by apply Matrix.ext; unfold raw2746step4 raw2746step3; decide +kernel
      have hl : raw2746step3Labels = labelEmbedding7 ∘ raw2746step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2746step3 raw2746step3Labels raw2746step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw2747 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2747Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2747step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2747step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2747step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2747step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2747 raw2747Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2747 raw2747Labels = mixedMoment B raw2747step0 raw2747step0Labels := by
      have hz : ∀ j, raw2747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2747step0 = (fun i j => raw2747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2747step0 raw2747; decide +kernel
      have hl : raw2747step0Labels = raw2747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2747 raw2747Labels permutation346 hz
    mixedMoment B raw2747step0 raw2747step0Labels = mixedMoment B raw2747step1 raw2747step1Labels := by
      have ha : raw2747step1 = (fun i j => raw2747step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2747step1 raw2747step0; decide +kernel
      have hl : raw2747step1Labels = raw2747step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2747step0 raw2747step0Labels permutation32 permutation4
    mixedMoment B raw2747step1 raw2747step1Labels = mixedMoment B raw2747step2 raw2747step2Labels := by
      have ha : raw2747step2 = -raw2747step1 := by apply Matrix.ext; change ∀ i j, raw2747step2 i j = -(raw2747step1 i j); unfold raw2747step2 raw2747step1; decide +kernel
      have hl : raw2747step2Labels = raw2747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2747step2 raw2747step2Labels = mixedMoment B raw2747step3 raw2747step3Labels := by
      have ha : raw2747step3 = raw2747step2 := by apply Matrix.ext; unfold raw2747step3 raw2747step2; decide +kernel
      have hl : raw2747step2Labels = labelEmbedding7 ∘ raw2747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2747step2 raw2747step2Labels raw2747step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2748 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2748Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2748step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2748step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2748step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2748step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2748 raw2748Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2748 raw2748Labels = mixedMoment B raw2748step0 raw2748step0Labels := by
      have hz : ∀ j, raw2748 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2748step0 = (fun i j => raw2748 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2748step0 raw2748; decide +kernel
      have hl : raw2748step0Labels = raw2748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2748 raw2748Labels permutation265 hz
    mixedMoment B raw2748step0 raw2748step0Labels = mixedMoment B raw2748step1 raw2748step1Labels := by
      have ha : raw2748step1 = (fun i j => raw2748step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2748step1 raw2748step0; decide +kernel
      have hl : raw2748step1Labels = raw2748step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2748step0 raw2748step0Labels permutation32 permutation4
    mixedMoment B raw2748step1 raw2748step1Labels = mixedMoment B raw2748step2 raw2748step2Labels := by
      have ha : raw2748step2 = -raw2748step1 := by apply Matrix.ext; change ∀ i j, raw2748step2 i j = -(raw2748step1 i j); unfold raw2748step2 raw2748step1; decide +kernel
      have hl : raw2748step2Labels = raw2748step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2748step2 raw2748step2Labels = mixedMoment B raw2748step3 raw2748step3Labels := by
      have ha : raw2748step3 = raw2748step2 := by apply Matrix.ext; unfold raw2748step3 raw2748step2; decide +kernel
      have hl : raw2748step2Labels = labelEmbedding7 ∘ raw2748step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2748step2 raw2748step2Labels raw2748step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2749 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2749Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2749step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2749step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2749step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, -1, 2]]
def raw2749step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2749step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2749step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2749step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2749step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2749 raw2749Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2749 raw2749Labels = mixedMoment B raw2749step0 raw2749step0Labels := by
      have hz : ∀ j, raw2749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2749step0 = (fun i j => raw2749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2749step0 raw2749; decide +kernel
      have hl : raw2749step0Labels = raw2749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2749 raw2749Labels permutation434 hz
    mixedMoment B raw2749step0 raw2749step0Labels = mixedMoment B raw2749step1 raw2749step1Labels := by
      have hz : ∀ j, raw2749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2749step1 = (fun i j => raw2749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2749step1 raw2749step0; decide +kernel
      have hl : raw2749step1Labels = raw2749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2749step0 raw2749step0Labels permutation80 hz
    mixedMoment B raw2749step1 raw2749step1Labels = mixedMoment B raw2749step2 raw2749step2Labels := by
      have hz : ∀ j, raw2749step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2749step2 = (fun i j => raw2749step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2749step2 raw2749step1; decide +kernel
      have hl : raw2749step2Labels = raw2749step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2749step1 raw2749step1Labels permutation14 hz
    mixedMoment B raw2749step2 raw2749step2Labels = mixedMoment B raw2749step3 raw2749step3Labels := by
      have ha : raw2749step3 = (fun i j => raw2749step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2749step3 raw2749step2; decide +kernel
      have hl : raw2749step3Labels = raw2749step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2749step2 raw2749step2Labels permutation2 permutation6
    mixedMoment B raw2749step3 raw2749step3Labels = mixedMoment B raw2749step4 raw2749step4Labels := by
      have ha : raw2749step4 = raw2749step3 := by apply Matrix.ext; unfold raw2749step4 raw2749step3; decide +kernel
      have hl : raw2749step3Labels = labelEmbedding9 ∘ raw2749step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2749step3 raw2749step3Labels raw2749step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw2750 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2]]
def raw2750Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2750step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2]]
def raw2750step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2750step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, -1, 2]]
def raw2750step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2750step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2750step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2750step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2750step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2750 raw2750Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2750 raw2750Labels = mixedMoment B raw2750step0 raw2750step0Labels := by
      have hz : ∀ j, raw2750 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw2750step0 = (fun i j => raw2750 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw2750step0 raw2750; decide +kernel
      have hl : raw2750step0Labels = raw2750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2750 raw2750Labels permutation520 hz
    mixedMoment B raw2750step0 raw2750step0Labels = mixedMoment B raw2750step1 raw2750step1Labels := by
      have hz : ∀ j, raw2750step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2750step1 = (fun i j => raw2750step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2750step1 raw2750step0; decide +kernel
      have hl : raw2750step1Labels = raw2750step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2750step0 raw2750step0Labels permutation80 hz
    mixedMoment B raw2750step1 raw2750step1Labels = mixedMoment B raw2750step2 raw2750step2Labels := by
      have hz : ∀ j, raw2750step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2750step2 = (fun i j => raw2750step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2750step2 raw2750step1; decide +kernel
      have hl : raw2750step2Labels = raw2750step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2750step1 raw2750step1Labels permutation14 hz
    mixedMoment B raw2750step2 raw2750step2Labels = mixedMoment B raw2750step3 raw2750step3Labels := by
      have ha : raw2750step3 = (fun i j => raw2750step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2750step3 raw2750step2; decide +kernel
      have hl : raw2750step3Labels = raw2750step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2750step2 raw2750step2Labels permutation2 permutation6
    mixedMoment B raw2750step3 raw2750step3Labels = mixedMoment B raw2750step4 raw2750step4Labels := by
      have ha : raw2750step4 = raw2750step3 := by apply Matrix.ext; unfold raw2750step4 raw2750step3; decide +kernel
      have hl : raw2750step3Labels = labelEmbedding9 ∘ raw2750step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2750step3 raw2750step3Labels raw2750step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw2751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2751Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2751step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2751step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2751step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2751step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2751step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2751step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2751step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2751 raw2751Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw2751 raw2751Labels = mixedMoment B raw2751step0 raw2751step0Labels := by
      have hz : ∀ j, raw2751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2751step0 = (fun i j => raw2751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2751step0 raw2751; decide +kernel
      have hl : raw2751step0Labels = raw2751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2751 raw2751Labels permutation434 hz
    mixedMoment B raw2751step0 raw2751step0Labels = mixedMoment B raw2751step1 raw2751step1Labels := by
      have hz : ∀ j, raw2751step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2751step1 = (fun i j => raw2751step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2751step1 raw2751step0; decide +kernel
      have hl : raw2751step1Labels = raw2751step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2751step0 raw2751step0Labels permutation80 hz
    mixedMoment B raw2751step1 raw2751step1Labels = mixedMoment B raw2751step2 raw2751step2Labels := by
      have ha : raw2751step2 = (fun i j => raw2751step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2751step2 raw2751step1; decide +kernel
      have hl : raw2751step2Labels = raw2751step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2751step1 raw2751step1Labels permutation30 permutation2
    mixedMoment B raw2751step2 raw2751step2Labels = mixedMoment B raw2751step3 raw2751step3Labels := by
      have ha : raw2751step3 = -raw2751step2 := by apply Matrix.ext; change ∀ i j, raw2751step3 i j = -(raw2751step2 i j); unfold raw2751step3 raw2751step2; decide +kernel
      have hl : raw2751step3Labels = raw2751step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw2752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2752step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2752step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2752step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2752 raw2752Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw2752 raw2752Labels = mixedMoment B raw2752step0 raw2752step0Labels := by
      have hz : ∀ j, raw2752 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2752step0 = (fun i j => raw2752 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2752step0 raw2752; decide +kernel
      have hl : raw2752step0Labels = raw2752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2752 raw2752Labels permutation434 hz
    mixedMoment B raw2752step0 raw2752step0Labels = mixedMoment B raw2752step1 raw2752step1Labels := by
      have ha : raw2752step1 = (fun i j => raw2752step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2752step1 raw2752step0; decide +kernel
      have hl : raw2752step1Labels = raw2752step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2752step0 raw2752step0Labels permutation149 permutation2
    mixedMoment B raw2752step1 raw2752step1Labels = mixedMoment B raw2752step2 raw2752step2Labels := by
      have ha : raw2752step2 = -raw2752step1 := by apply Matrix.ext; change ∀ i j, raw2752step2 i j = -(raw2752step1 i j); unfold raw2752step2 raw2752step1; decide +kernel
      have hl : raw2752step2Labels = raw2752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw2753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2753step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2753step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2753step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2753step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2753 raw2753Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw2753 raw2753Labels = mixedMoment B raw2753step0 raw2753step0Labels := by
      have hz : ∀ j, raw2753 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2753step0 = (fun i j => raw2753 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2753step0 raw2753; decide +kernel
      have hl : raw2753step0Labels = raw2753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2753 raw2753Labels permutation346 hz
    mixedMoment B raw2753step0 raw2753step0Labels = mixedMoment B raw2753step1 raw2753step1Labels := by
      have ha : raw2753step1 = (fun i j => raw2753step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2753step1 raw2753step0; decide +kernel
      have hl : raw2753step1Labels = raw2753step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2753step0 raw2753step0Labels permutation149 permutation2
    mixedMoment B raw2753step1 raw2753step1Labels = mixedMoment B raw2753step2 raw2753step2Labels := by
      have ha : raw2753step2 = -raw2753step1 := by apply Matrix.ext; change ∀ i j, raw2753step2 i j = -(raw2753step1 i j); unfold raw2753step2 raw2753step1; decide +kernel
      have hl : raw2753step2Labels = raw2753step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw2754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1]]
def raw2754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw2754step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2754step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2754step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2754step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2754step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2754 raw2754Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw2754 raw2754Labels = mixedMoment B raw2754step0 raw2754step0Labels := by
      have hz : ∀ j, raw2754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2754step0 = (fun i j => raw2754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2754step0 raw2754; decide +kernel
      have hl : raw2754step0Labels = raw2754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2754 raw2754Labels permutation434 hz
    mixedMoment B raw2754step0 raw2754step0Labels = mixedMoment B raw2754step1 raw2754step1Labels := by
      have hz : ∀ j, raw2754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2754step1 = (fun i j => raw2754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2754step1 raw2754step0; decide +kernel
      have hl : raw2754step1Labels = raw2754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2754step0 raw2754step0Labels permutation80 hz
    mixedMoment B raw2754step1 raw2754step1Labels = mixedMoment B raw2754step2 raw2754step2Labels := by
      have ha : raw2754step2 = (fun i j => raw2754step1 (permutation28 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2754step2 raw2754step1; decide +kernel
      have hl : raw2754step2Labels = raw2754step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2754step1 raw2754step1Labels permutation28 permutation3
    mixedMoment B raw2754step2 raw2754step2Labels = mixedMoment B raw2754step3 raw2754step3Labels := by
      have ha : raw2754step3 = -raw2754step2 := by apply Matrix.ext; change ∀ i j, raw2754step3 i j = -(raw2754step2 i j); unfold raw2754step3 raw2754step2; decide +kernel
      have hl : raw2754step3Labels = raw2754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2754step3 raw2754step3Labels = mixedMoment B raw2754step4 raw2754step4Labels := by
      have ha : raw2754step4 = raw2754step3 := by apply Matrix.ext; unfold raw2754step4 raw2754step3; decide +kernel
      have hl : raw2754step3Labels = labelEmbedding6 ∘ raw2754step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2754step3 raw2754step3Labels raw2754step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw2755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw2755step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2755step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2755step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2755step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2755step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2755 raw2755Labels = mixedMoment B node5501 node5501Labels := by
  calc
    mixedMoment B raw2755 raw2755Labels = mixedMoment B raw2755step0 raw2755step0Labels := by
      have hz : ∀ j, raw2755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2755step0 = (fun i j => raw2755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2755step0 raw2755; decide +kernel
      have hl : raw2755step0Labels = raw2755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2755 raw2755Labels permutation434 hz
    mixedMoment B raw2755step0 raw2755step0Labels = mixedMoment B raw2755step1 raw2755step1Labels := by
      have hz : ∀ j, raw2755step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2755step1 = (fun i j => raw2755step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2755step1 raw2755step0; decide +kernel
      have hl : raw2755step1Labels = raw2755step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2755step0 raw2755step0Labels permutation80 hz
    mixedMoment B raw2755step1 raw2755step1Labels = mixedMoment B raw2755step2 raw2755step2Labels := by
      have ha : raw2755step2 = (fun i j => raw2755step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2755step2 raw2755step1; decide +kernel
      have hl : raw2755step2Labels = raw2755step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2755step1 raw2755step1Labels permutation24 permutation6
    mixedMoment B raw2755step2 raw2755step2Labels = mixedMoment B raw2755step3 raw2755step3Labels := by
      have ha : raw2755step3 = raw2755step2 := by apply Matrix.ext; unfold raw2755step3 raw2755step2; decide +kernel
      have hl : raw2755step2Labels = labelEmbedding9 ∘ raw2755step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2755step2 raw2755step2Labels raw2755step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5501 node5501Labels := by rfl

def raw2756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2756step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2756step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2756step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2756step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2756step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2756 raw2756Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw2756 raw2756Labels = mixedMoment B raw2756step0 raw2756step0Labels := by
      have hz : ∀ j, raw2756 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2756step0 = (fun i j => raw2756 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2756step0 raw2756; decide +kernel
      have hl : raw2756step0Labels = raw2756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2756 raw2756Labels permutation434 hz
    mixedMoment B raw2756step0 raw2756step0Labels = mixedMoment B raw2756step1 raw2756step1Labels := by
      have hz : ∀ j, raw2756step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2756step1 = (fun i j => raw2756step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2756step1 raw2756step0; decide +kernel
      have hl : raw2756step1Labels = raw2756step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2756step0 raw2756step0Labels permutation80 hz
    mixedMoment B raw2756step1 raw2756step1Labels = mixedMoment B raw2756step2 raw2756step2Labels := by
      have ha : raw2756step2 = (fun i j => raw2756step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2756step2 raw2756step1; decide +kernel
      have hl : raw2756step2Labels = raw2756step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2756step1 raw2756step1Labels permutation10 permutation3
    mixedMoment B raw2756step2 raw2756step2Labels = mixedMoment B raw2756step3 raw2756step3Labels := by
      have ha : raw2756step3 = raw2756step2 := by apply Matrix.ext; unfold raw2756step3 raw2756step2; decide +kernel
      have hl : raw2756step2Labels = labelEmbedding6 ∘ raw2756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2756step2 raw2756step2Labels raw2756step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw2757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2757step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2757step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2757step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2757step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2757step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2757 raw2757Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw2757 raw2757Labels = mixedMoment B raw2757step0 raw2757step0Labels := by
      have hz : ∀ j, raw2757 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2757step0 = (fun i j => raw2757 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2757step0 raw2757; decide +kernel
      have hl : raw2757step0Labels = raw2757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2757 raw2757Labels permutation434 hz
    mixedMoment B raw2757step0 raw2757step0Labels = mixedMoment B raw2757step1 raw2757step1Labels := by
      have ha : raw2757step1 = (fun i j => raw2757step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2757step1 raw2757step0; decide +kernel
      have hl : raw2757step1Labels = raw2757step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2757step0 raw2757step0Labels permutation139 permutation3
    mixedMoment B raw2757step1 raw2757step1Labels = mixedMoment B raw2757step2 raw2757step2Labels := by
      have ha : raw2757step2 = -raw2757step1 := by apply Matrix.ext; change ∀ i j, raw2757step2 i j = -(raw2757step1 i j); unfold raw2757step2 raw2757step1; decide +kernel
      have hl : raw2757step2Labels = raw2757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2757step2 raw2757step2Labels = mixedMoment B raw2757step3 raw2757step3Labels := by
      have ha : raw2757step3 = raw2757step2 := by apply Matrix.ext; unfold raw2757step3 raw2757step2; decide +kernel
      have hl : raw2757step2Labels = labelEmbedding6 ∘ raw2757step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2757step2 raw2757step2Labels raw2757step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw2758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2758step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2758step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2758step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2758step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2758step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2758 raw2758Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw2758 raw2758Labels = mixedMoment B raw2758step0 raw2758step0Labels := by
      have hz : ∀ j, raw2758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2758step0 = (fun i j => raw2758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2758step0 raw2758; decide +kernel
      have hl : raw2758step0Labels = raw2758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2758 raw2758Labels permutation346 hz
    mixedMoment B raw2758step0 raw2758step0Labels = mixedMoment B raw2758step1 raw2758step1Labels := by
      have ha : raw2758step1 = (fun i j => raw2758step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2758step1 raw2758step0; decide +kernel
      have hl : raw2758step1Labels = raw2758step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2758step0 raw2758step0Labels permutation139 permutation3
    mixedMoment B raw2758step1 raw2758step1Labels = mixedMoment B raw2758step2 raw2758step2Labels := by
      have ha : raw2758step2 = -raw2758step1 := by apply Matrix.ext; change ∀ i j, raw2758step2 i j = -(raw2758step1 i j); unfold raw2758step2 raw2758step1; decide +kernel
      have hl : raw2758step2Labels = raw2758step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2758step2 raw2758step2Labels = mixedMoment B raw2758step3 raw2758step3Labels := by
      have ha : raw2758step3 = raw2758step2 := by apply Matrix.ext; unfold raw2758step3 raw2758step2; decide +kernel
      have hl : raw2758step2Labels = labelEmbedding6 ∘ raw2758step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2758step2 raw2758step2Labels raw2758step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw2759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2759step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 2, -1], ![2, -1, -1]]
def raw2759step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2759step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2759step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2759step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2759step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2759 raw2759Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw2759 raw2759Labels = mixedMoment B raw2759step0 raw2759step0Labels := by
      have hz : ∀ j, raw2759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2759step0 = (fun i j => raw2759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2759step0 raw2759; decide +kernel
      have hl : raw2759step0Labels = raw2759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2759 raw2759Labels permutation434 hz
    mixedMoment B raw2759step0 raw2759step0Labels = mixedMoment B raw2759step1 raw2759step1Labels := by
      have hz : ∀ j, raw2759step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2759step1 = (fun i j => raw2759step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2759step1 raw2759step0; decide +kernel
      have hl : raw2759step1Labels = raw2759step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2759step0 raw2759step0Labels permutation80 hz
    mixedMoment B raw2759step1 raw2759step1Labels = mixedMoment B raw2759step2 raw2759step2Labels := by
      have ha : raw2759step2 = (fun i j => raw2759step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2759step2 raw2759step1; decide +kernel
      have hl : raw2759step2Labels = raw2759step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2759step1 raw2759step1Labels permutation10 permutation3
    mixedMoment B raw2759step2 raw2759step2Labels = mixedMoment B raw2759step3 raw2759step3Labels := by
      have ha : raw2759step3 = raw2759step2 := by apply Matrix.ext; unfold raw2759step3 raw2759step2; decide +kernel
      have hl : raw2759step2Labels = labelEmbedding6 ∘ raw2759step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2759step2 raw2759step2Labels raw2759step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

def raw2760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2760step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2760step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2760step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw2760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2760step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2760step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2760step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2760step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2760 raw2760Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw2760 raw2760Labels = mixedMoment B raw2760step0 raw2760step0Labels := by
      have hz : ∀ j, raw2760 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2760step0 = (fun i j => raw2760 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2760step0 raw2760; decide +kernel
      have hl : raw2760step0Labels = raw2760Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2760 raw2760Labels permutation434 hz
    mixedMoment B raw2760step0 raw2760step0Labels = mixedMoment B raw2760step1 raw2760step1Labels := by
      have hz : ∀ j, raw2760step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2760step1 = (fun i j => raw2760step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2760step1 raw2760step0; decide +kernel
      have hl : raw2760step1Labels = raw2760step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2760step0 raw2760step0Labels permutation80 hz
    mixedMoment B raw2760step1 raw2760step1Labels = mixedMoment B raw2760step2 raw2760step2Labels := by
      have ha : raw2760step2 = (fun i j => raw2760step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2760step2 raw2760step1; decide +kernel
      have hl : raw2760step2Labels = raw2760step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2760step1 raw2760step1Labels permutation11 permutation3
    mixedMoment B raw2760step2 raw2760step2Labels = mixedMoment B raw2760step3 raw2760step3Labels := by
      have ha : raw2760step3 = raw2760step2 := by apply Matrix.ext; unfold raw2760step3 raw2760step2; decide +kernel
      have hl : raw2760step2Labels = labelEmbedding6 ∘ raw2760step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2760step2 raw2760step2Labels raw2760step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw2761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2761step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2761step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2761step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2761step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2761 raw2761Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2761 raw2761Labels = mixedMoment B raw2761step0 raw2761step0Labels := by
      have hz : ∀ j, raw2761 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2761step0 = (fun i j => raw2761 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2761step0 raw2761; decide +kernel
      have hl : raw2761step0Labels = raw2761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2761 raw2761Labels permutation434 hz
    mixedMoment B raw2761step0 raw2761step0Labels = mixedMoment B raw2761step1 raw2761step1Labels := by
      have ha : raw2761step1 = (fun i j => raw2761step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2761step1 raw2761step0; decide +kernel
      have hl : raw2761step1Labels = raw2761step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2761step0 raw2761step0Labels permutation44 permutation3
    mixedMoment B raw2761step1 raw2761step1Labels = mixedMoment B raw2761step2 raw2761step2Labels := by
      have ha : raw2761step2 = raw2761step1 := by apply Matrix.ext; unfold raw2761step2 raw2761step1; decide +kernel
      have hl : raw2761step1Labels = labelEmbedding6 ∘ raw2761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2761step1 raw2761step1Labels raw2761step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw2762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2762step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2762 raw2762Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw2762 raw2762Labels = mixedMoment B raw2762step0 raw2762step0Labels := by
      have hz : ∀ j, raw2762 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2762step0 = (fun i j => raw2762 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2762step0 raw2762; decide +kernel
      have hl : raw2762step0Labels = raw2762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2762 raw2762Labels permutation434 hz
    mixedMoment B raw2762step0 raw2762step0Labels = mixedMoment B raw2762step1 raw2762step1Labels := by
      have ha : raw2762step1 = (fun i j => raw2762step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2762step1 raw2762step0; decide +kernel
      have hl : raw2762step1Labels = raw2762step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2762step0 raw2762step0Labels permutation34 permutation2
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw2763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2763step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2763 raw2763Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw2763 raw2763Labels = mixedMoment B raw2763step0 raw2763step0Labels := by
      have ha : raw2763step0 = (fun i j => raw2763 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2763step0 raw2763; decide +kernel
      have hl : raw2763step0Labels = raw2763Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2763 raw2763Labels permutation212 permutation3
    mixedMoment B raw2763step0 raw2763step0Labels = mixedMoment B raw2763step1 raw2763step1Labels := by
      have ha : raw2763step1 = raw2763step0 := by apply Matrix.ext; unfold raw2763step1 raw2763step0; decide +kernel
      have hl : raw2763step0Labels = labelEmbedding6 ∘ raw2763step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2763step0 raw2763step0Labels raw2763step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw2764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2764step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2764step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2764step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2764step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2764 raw2764Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw2764 raw2764Labels = mixedMoment B raw2764step0 raw2764step0Labels := by
      have hz : ∀ j, raw2764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2764step0 = (fun i j => raw2764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2764step0 raw2764; decide +kernel
      have hl : raw2764step0Labels = raw2764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2764 raw2764Labels permutation434 hz
    mixedMoment B raw2764step0 raw2764step0Labels = mixedMoment B raw2764step1 raw2764step1Labels := by
      have ha : raw2764step1 = (fun i j => raw2764step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2764step1 raw2764step0; decide +kernel
      have hl : raw2764step1Labels = raw2764step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2764step0 raw2764step0Labels permutation44 permutation3
    mixedMoment B raw2764step1 raw2764step1Labels = mixedMoment B raw2764step2 raw2764step2Labels := by
      have ha : raw2764step2 = raw2764step1 := by apply Matrix.ext; unfold raw2764step2 raw2764step1; decide +kernel
      have hl : raw2764step1Labels = labelEmbedding6 ∘ raw2764step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2764step1 raw2764step1Labels raw2764step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw2765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2765 raw2765Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw2765 raw2765Labels = mixedMoment B raw2765step0 raw2765step0Labels := by
      have hz : ∀ j, raw2765 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2765step0 = (fun i j => raw2765 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2765step0 raw2765; decide +kernel
      have hl : raw2765step0Labels = raw2765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2765 raw2765Labels permutation434 hz
    mixedMoment B raw2765step0 raw2765step0Labels = mixedMoment B raw2765step1 raw2765step1Labels := by
      have ha : raw2765step1 = (fun i j => raw2765step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2765step1 raw2765step0; decide +kernel
      have hl : raw2765step1Labels = raw2765step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2765step0 raw2765step0Labels permutation34 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw2766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2766step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2766step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2766 raw2766Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2766 raw2766Labels = mixedMoment B raw2766step0 raw2766step0Labels := by
      have hz : ∀ j, raw2766 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2766step0 = (fun i j => raw2766 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2766step0 raw2766; decide +kernel
      have hl : raw2766step0Labels = raw2766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2766 raw2766Labels permutation346 hz
    mixedMoment B raw2766step0 raw2766step0Labels = mixedMoment B raw2766step1 raw2766step1Labels := by
      have ha : raw2766step1 = (fun i j => raw2766step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2766step1 raw2766step0; decide +kernel
      have hl : raw2766step1Labels = raw2766step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2766step0 raw2766step0Labels permutation44 permutation3
    mixedMoment B raw2766step1 raw2766step1Labels = mixedMoment B raw2766step2 raw2766step2Labels := by
      have ha : raw2766step2 = raw2766step1 := by apply Matrix.ext; unfold raw2766step2 raw2766step1; decide +kernel
      have hl : raw2766step1Labels = labelEmbedding6 ∘ raw2766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2766step1 raw2766step1Labels raw2766step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw2767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2767step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2767 raw2767Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw2767 raw2767Labels = mixedMoment B raw2767step0 raw2767step0Labels := by
      have hz : ∀ j, raw2767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2767step0 = (fun i j => raw2767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2767step0 raw2767; decide +kernel
      have hl : raw2767step0Labels = raw2767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2767 raw2767Labels permutation346 hz
    mixedMoment B raw2767step0 raw2767step0Labels = mixedMoment B raw2767step1 raw2767step1Labels := by
      have ha : raw2767step1 = (fun i j => raw2767step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2767step1 raw2767step0; decide +kernel
      have hl : raw2767step1Labels = raw2767step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2767step0 raw2767step0Labels permutation34 permutation2
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw2768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2768step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2768 raw2768Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw2768 raw2768Labels = mixedMoment B raw2768step0 raw2768step0Labels := by
      have ha : raw2768step0 = (fun i j => raw2768 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2768step0 raw2768; decide +kernel
      have hl : raw2768step0Labels = raw2768Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2768 raw2768Labels permutation188 permutation3
    mixedMoment B raw2768step0 raw2768step0Labels = mixedMoment B raw2768step1 raw2768step1Labels := by
      have ha : raw2768step1 = raw2768step0 := by apply Matrix.ext; unfold raw2768step1 raw2768step0; decide +kernel
      have hl : raw2768step0Labels = labelEmbedding6 ∘ raw2768step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2768step0 raw2768step0Labels raw2768step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw2769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2769step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2769 raw2769Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw2769 raw2769Labels = mixedMoment B raw2769step0 raw2769step0Labels := by
      have hz : ∀ j, raw2769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2769step0 = (fun i j => raw2769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2769step0 raw2769; decide +kernel
      have hl : raw2769step0Labels = raw2769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2769 raw2769Labels permutation346 hz
    mixedMoment B raw2769step0 raw2769step0Labels = mixedMoment B raw2769step1 raw2769step1Labels := by
      have ha : raw2769step1 = (fun i j => raw2769step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2769step1 raw2769step0; decide +kernel
      have hl : raw2769step1Labels = raw2769step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2769step0 raw2769step0Labels permutation44 permutation3
    mixedMoment B raw2769step1 raw2769step1Labels = mixedMoment B raw2769step2 raw2769step2Labels := by
      have ha : raw2769step2 = raw2769step1 := by apply Matrix.ext; unfold raw2769step2 raw2769step1; decide +kernel
      have hl : raw2769step1Labels = labelEmbedding6 ∘ raw2769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2769step1 raw2769step1Labels raw2769step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw2770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2770 raw2770Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw2770 raw2770Labels = mixedMoment B raw2770step0 raw2770step0Labels := by
      have hz : ∀ j, raw2770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2770step0 = (fun i j => raw2770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2770step0 raw2770; decide +kernel
      have hl : raw2770step0Labels = raw2770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2770 raw2770Labels permutation346 hz
    mixedMoment B raw2770step0 raw2770step0Labels = mixedMoment B raw2770step1 raw2770step1Labels := by
      have ha : raw2770step1 = (fun i j => raw2770step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2770step1 raw2770step0; decide +kernel
      have hl : raw2770step1Labels = raw2770step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2770step0 raw2770step0Labels permutation34 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw2771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2771step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2771step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2771step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2771 raw2771Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2771 raw2771Labels = mixedMoment B raw2771step0 raw2771step0Labels := by
      have hz : ∀ j, raw2771 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2771step0 = (fun i j => raw2771 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2771step0 raw2771; decide +kernel
      have hl : raw2771step0Labels = raw2771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2771 raw2771Labels permutation434 hz
    mixedMoment B raw2771step0 raw2771step0Labels = mixedMoment B raw2771step1 raw2771step1Labels := by
      have hz : ∀ j, raw2771step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2771step1 = (fun i j => raw2771step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2771step1 raw2771step0; decide +kernel
      have hl : raw2771step1Labels = raw2771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2771step0 raw2771step0Labels permutation80 hz
    mixedMoment B raw2771step1 raw2771step1Labels = mixedMoment B raw2771step2 raw2771step2Labels := by
      have ha : raw2771step2 = (fun i j => raw2771step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2771step2 raw2771step1; decide +kernel
      have hl : raw2771step2Labels = raw2771step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2771step1 raw2771step1Labels permutation8 permutation3
    mixedMoment B raw2771step2 raw2771step2Labels = mixedMoment B raw2771step3 raw2771step3Labels := by
      have ha : raw2771step3 = raw2771step2 := by apply Matrix.ext; unfold raw2771step3 raw2771step2; decide +kernel
      have hl : raw2771step2Labels = labelEmbedding6 ∘ raw2771step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2771step2 raw2771step2Labels raw2771step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw2772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2772step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2772 raw2772Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw2772 raw2772Labels = mixedMoment B raw2772step0 raw2772step0Labels := by
      have hz : ∀ j, raw2772 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2772step0 = (fun i j => raw2772 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2772step0 raw2772; decide +kernel
      have hl : raw2772step0Labels = raw2772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2772 raw2772Labels permutation434 hz
    mixedMoment B raw2772step0 raw2772step0Labels = mixedMoment B raw2772step1 raw2772step1Labels := by
      have hz : ∀ j, raw2772step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2772step1 = (fun i j => raw2772step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2772step1 raw2772step0; decide +kernel
      have hl : raw2772step1Labels = raw2772step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2772step0 raw2772step0Labels permutation80 hz
    _ = mixedMoment B node5487 node5487Labels := by rfl

def raw2773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2773step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2773step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2773 raw2773Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw2773 raw2773Labels = mixedMoment B raw2773step0 raw2773step0Labels := by
      have hz : ∀ j, raw2773 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2773step0 = (fun i j => raw2773 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2773step0 raw2773; decide +kernel
      have hl : raw2773step0Labels = raw2773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2773 raw2773Labels permutation434 hz
    mixedMoment B raw2773step0 raw2773step0Labels = mixedMoment B raw2773step1 raw2773step1Labels := by
      have ha : raw2773step1 = (fun i j => raw2773step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2773step1 raw2773step0; decide +kernel
      have hl : raw2773step1Labels = raw2773step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2773step0 raw2773step0Labels permutation149 permutation2
    mixedMoment B raw2773step1 raw2773step1Labels = mixedMoment B raw2773step2 raw2773step2Labels := by
      have ha : raw2773step2 = -raw2773step1 := by apply Matrix.ext; change ∀ i j, raw2773step2 i j = -(raw2773step1 i j); unfold raw2773step2 raw2773step1; decide +kernel
      have hl : raw2773step2Labels = raw2773step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw2774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2774 raw2774Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw2774 raw2774Labels = mixedMoment B raw2774step0 raw2774step0Labels := by
      have hz : ∀ j, raw2774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2774step0 = (fun i j => raw2774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2774step0 raw2774; decide +kernel
      have hl : raw2774step0Labels = raw2774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2774 raw2774Labels permutation346 hz
    mixedMoment B raw2774step0 raw2774step0Labels = mixedMoment B raw2774step1 raw2774step1Labels := by
      have ha : raw2774step1 = (fun i j => raw2774step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2774step1 raw2774step0; decide +kernel
      have hl : raw2774step1Labels = raw2774step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2774step0 raw2774step0Labels permutation149 permutation2
    mixedMoment B raw2774step1 raw2774step1Labels = mixedMoment B raw2774step2 raw2774step2Labels := by
      have ha : raw2774step2 = -raw2774step1 := by apply Matrix.ext; change ∀ i j, raw2774step2 i j = -(raw2774step1 i j); unfold raw2774step2 raw2774step1; decide +kernel
      have hl : raw2774step2Labels = raw2774step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw2775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2775 raw2775Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw2775 raw2775Labels = mixedMoment B raw2775step0 raw2775step0Labels := by
      have hz : ∀ j, raw2775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2775step0 = (fun i j => raw2775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2775step0 raw2775; decide +kernel
      have hl : raw2775step0Labels = raw2775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2775 raw2775Labels permutation434 hz
    mixedMoment B raw2775step0 raw2775step0Labels = mixedMoment B raw2775step1 raw2775step1Labels := by
      have hz : ∀ j, raw2775step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2775step1 = (fun i j => raw2775step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2775step1 raw2775step0; decide +kernel
      have hl : raw2775step1Labels = raw2775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2775step0 raw2775step0Labels permutation80 hz
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw2776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2776step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw2776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2776step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2776step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2776step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2776step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2776 raw2776Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw2776 raw2776Labels = mixedMoment B raw2776step0 raw2776step0Labels := by
      have hz : ∀ j, raw2776 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2776step0 = (fun i j => raw2776 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2776step0 raw2776; decide +kernel
      have hl : raw2776step0Labels = raw2776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2776 raw2776Labels permutation434 hz
    mixedMoment B raw2776step0 raw2776step0Labels = mixedMoment B raw2776step1 raw2776step1Labels := by
      have hz : ∀ j, raw2776step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2776step1 = (fun i j => raw2776step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2776step1 raw2776step0; decide +kernel
      have hl : raw2776step1Labels = raw2776step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2776step0 raw2776step0Labels permutation80 hz
    mixedMoment B raw2776step1 raw2776step1Labels = mixedMoment B raw2776step2 raw2776step2Labels := by
      have ha : raw2776step2 = (fun i j => raw2776step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2776step2 raw2776step1; decide +kernel
      have hl : raw2776step2Labels = raw2776step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2776step1 raw2776step1Labels permutation10 permutation3
    mixedMoment B raw2776step2 raw2776step2Labels = mixedMoment B raw2776step3 raw2776step3Labels := by
      have ha : raw2776step3 = raw2776step2 := by apply Matrix.ext; unfold raw2776step3 raw2776step2; decide +kernel
      have hl : raw2776step2Labels = labelEmbedding6 ∘ raw2776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2776step2 raw2776step2Labels raw2776step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw2777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2777step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1]]
def raw2777step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2777step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2777step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2777step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2777step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2777step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2777step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2777 raw2777Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw2777 raw2777Labels = mixedMoment B raw2777step0 raw2777step0Labels := by
      have hz : ∀ j, raw2777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2777step0 = (fun i j => raw2777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2777step0 raw2777; decide +kernel
      have hl : raw2777step0Labels = raw2777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2777 raw2777Labels permutation434 hz
    mixedMoment B raw2777step0 raw2777step0Labels = mixedMoment B raw2777step1 raw2777step1Labels := by
      have hz : ∀ j, raw2777step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2777step1 = (fun i j => raw2777step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2777step1 raw2777step0; decide +kernel
      have hl : raw2777step1Labels = raw2777step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2777step0 raw2777step0Labels permutation80 hz
    mixedMoment B raw2777step1 raw2777step1Labels = mixedMoment B raw2777step2 raw2777step2Labels := by
      have ha : raw2777step2 = (fun i j => raw2777step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2777step2 raw2777step1; decide +kernel
      have hl : raw2777step2Labels = raw2777step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2777step1 raw2777step1Labels permutation31 permutation3
    mixedMoment B raw2777step2 raw2777step2Labels = mixedMoment B raw2777step3 raw2777step3Labels := by
      have ha : raw2777step3 = -raw2777step2 := by apply Matrix.ext; change ∀ i j, raw2777step3 i j = -(raw2777step2 i j); unfold raw2777step3 raw2777step2; decide +kernel
      have hl : raw2777step3Labels = raw2777step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2777step3 raw2777step3Labels = mixedMoment B raw2777step4 raw2777step4Labels := by
      have ha : raw2777step4 = raw2777step3 := by apply Matrix.ext; unfold raw2777step4 raw2777step3; decide +kernel
      have hl : raw2777step3Labels = labelEmbedding6 ∘ raw2777step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2777step3 raw2777step3Labels raw2777step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw2778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2778step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2778step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2778step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2778step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2778 raw2778Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2778 raw2778Labels = mixedMoment B raw2778step0 raw2778step0Labels := by
      have hz : ∀ j, raw2778 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2778step0 = (fun i j => raw2778 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2778step0 raw2778; decide +kernel
      have hl : raw2778step0Labels = raw2778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2778 raw2778Labels permutation434 hz
    mixedMoment B raw2778step0 raw2778step0Labels = mixedMoment B raw2778step1 raw2778step1Labels := by
      have ha : raw2778step1 = (fun i j => raw2778step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2778step1 raw2778step0; decide +kernel
      have hl : raw2778step1Labels = raw2778step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2778step0 raw2778step0Labels permutation139 permutation3
    mixedMoment B raw2778step1 raw2778step1Labels = mixedMoment B raw2778step2 raw2778step2Labels := by
      have ha : raw2778step2 = -raw2778step1 := by apply Matrix.ext; change ∀ i j, raw2778step2 i j = -(raw2778step1 i j); unfold raw2778step2 raw2778step1; decide +kernel
      have hl : raw2778step2Labels = raw2778step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2778step2 raw2778step2Labels = mixedMoment B raw2778step3 raw2778step3Labels := by
      have ha : raw2778step3 = raw2778step2 := by apply Matrix.ext; unfold raw2778step3 raw2778step2; decide +kernel
      have hl : raw2778step2Labels = labelEmbedding6 ∘ raw2778step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2778step2 raw2778step2Labels raw2778step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw2779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2779step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2779step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2779 raw2779Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw2779 raw2779Labels = mixedMoment B raw2779step0 raw2779step0Labels := by
      have hz : ∀ j, raw2779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2779step0 = (fun i j => raw2779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2779step0 raw2779; decide +kernel
      have hl : raw2779step0Labels = raw2779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2779 raw2779Labels permutation346 hz
    mixedMoment B raw2779step0 raw2779step0Labels = mixedMoment B raw2779step1 raw2779step1Labels := by
      have ha : raw2779step1 = (fun i j => raw2779step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2779step1 raw2779step0; decide +kernel
      have hl : raw2779step1Labels = raw2779step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2779step0 raw2779step0Labels permutation139 permutation3
    mixedMoment B raw2779step1 raw2779step1Labels = mixedMoment B raw2779step2 raw2779step2Labels := by
      have ha : raw2779step2 = -raw2779step1 := by apply Matrix.ext; change ∀ i j, raw2779step2 i j = -(raw2779step1 i j); unfold raw2779step2 raw2779step1; decide +kernel
      have hl : raw2779step2Labels = raw2779step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2779step2 raw2779step2Labels = mixedMoment B raw2779step3 raw2779step3Labels := by
      have ha : raw2779step3 = raw2779step2 := by apply Matrix.ext; unfold raw2779step3 raw2779step2; decide +kernel
      have hl : raw2779step2Labels = labelEmbedding6 ∘ raw2779step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2779step2 raw2779step2Labels raw2779step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw2780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw2780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw2780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![3, -2, -1]]
def raw2780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2780step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2780step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2780step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2780step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2780 raw2780Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw2780 raw2780Labels = mixedMoment B raw2780step0 raw2780step0Labels := by
      have hz : ∀ j, raw2780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2780step0 = (fun i j => raw2780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2780step0 raw2780; decide +kernel
      have hl : raw2780step0Labels = raw2780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2780 raw2780Labels permutation434 hz
    mixedMoment B raw2780step0 raw2780step0Labels = mixedMoment B raw2780step1 raw2780step1Labels := by
      have hz : ∀ j, raw2780step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2780step1 = (fun i j => raw2780step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2780step1 raw2780step0; decide +kernel
      have hl : raw2780step1Labels = raw2780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2780step0 raw2780step0Labels permutation80 hz
    mixedMoment B raw2780step1 raw2780step1Labels = mixedMoment B raw2780step2 raw2780step2Labels := by
      have ha : raw2780step2 = (fun i j => raw2780step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2780step2 raw2780step1; decide +kernel
      have hl : raw2780step2Labels = raw2780step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2780step1 raw2780step1Labels permutation29 permutation3
    mixedMoment B raw2780step2 raw2780step2Labels = mixedMoment B raw2780step3 raw2780step3Labels := by
      have ha : raw2780step3 = -raw2780step2 := by apply Matrix.ext; change ∀ i j, raw2780step3 i j = -(raw2780step2 i j); unfold raw2780step3 raw2780step2; decide +kernel
      have hl : raw2780step3Labels = raw2780step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2780step3 raw2780step3Labels = mixedMoment B raw2780step4 raw2780step4Labels := by
      have ha : raw2780step4 = raw2780step3 := by apply Matrix.ext; unfold raw2780step4 raw2780step3; decide +kernel
      have hl : raw2780step3Labels = labelEmbedding6 ∘ raw2780step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2780step3 raw2780step3Labels raw2780step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw2781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2781Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2781step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2781step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2781step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2781step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw2781step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2781step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2781step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2781 raw2781Labels = mixedMoment B node4018 node4018Labels := by
  calc
    mixedMoment B raw2781 raw2781Labels = mixedMoment B raw2781step0 raw2781step0Labels := by
      have hz : ∀ j, raw2781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2781step0 = (fun i j => raw2781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2781step0 raw2781; decide +kernel
      have hl : raw2781step0Labels = raw2781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2781 raw2781Labels permutation434 hz
    mixedMoment B raw2781step0 raw2781step0Labels = mixedMoment B raw2781step1 raw2781step1Labels := by
      have hz : ∀ j, raw2781step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2781step1 = (fun i j => raw2781step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2781step1 raw2781step0; decide +kernel
      have hl : raw2781step1Labels = raw2781step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2781step0 raw2781step0Labels permutation80 hz
    mixedMoment B raw2781step1 raw2781step1Labels = mixedMoment B raw2781step2 raw2781step2Labels := by
      have ha : raw2781step2 = (fun i j => raw2781step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2781step2 raw2781step1; decide +kernel
      have hl : raw2781step2Labels = raw2781step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2781step1 raw2781step1Labels permutation30 permutation3
    mixedMoment B raw2781step2 raw2781step2Labels = mixedMoment B raw2781step3 raw2781step3Labels := by
      have ha : raw2781step3 = -raw2781step2 := by apply Matrix.ext; change ∀ i j, raw2781step3 i j = -(raw2781step2 i j); unfold raw2781step3 raw2781step2; decide +kernel
      have hl : raw2781step3Labels = raw2781step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4018 node4018Labels := by rfl

def raw2782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2782step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2782step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2782 raw2782Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw2782 raw2782Labels = mixedMoment B raw2782step0 raw2782step0Labels := by
      have hz : ∀ j, raw2782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2782step0 = (fun i j => raw2782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2782step0 raw2782; decide +kernel
      have hl : raw2782step0Labels = raw2782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2782 raw2782Labels permutation434 hz
    mixedMoment B raw2782step0 raw2782step0Labels = mixedMoment B raw2782step1 raw2782step1Labels := by
      have ha : raw2782step1 = (fun i j => raw2782step0 (permutation138 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2782step1 raw2782step0; decide +kernel
      have hl : raw2782step1Labels = raw2782step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2782step0 raw2782step0Labels permutation138 permutation3
    mixedMoment B raw2782step1 raw2782step1Labels = mixedMoment B raw2782step2 raw2782step2Labels := by
      have ha : raw2782step2 = -raw2782step1 := by apply Matrix.ext; change ∀ i j, raw2782step2 i j = -(raw2782step1 i j); unfold raw2782step2 raw2782step1; decide +kernel
      have hl : raw2782step2Labels = raw2782step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw2783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2783 raw2783Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw2783 raw2783Labels = mixedMoment B raw2783step0 raw2783step0Labels := by
      have hz : ∀ j, raw2783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2783step0 = (fun i j => raw2783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2783step0 raw2783; decide +kernel
      have hl : raw2783step0Labels = raw2783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2783 raw2783Labels permutation346 hz
    mixedMoment B raw2783step0 raw2783step0Labels = mixedMoment B raw2783step1 raw2783step1Labels := by
      have ha : raw2783step1 = (fun i j => raw2783step0 (permutation138 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2783step1 raw2783step0; decide +kernel
      have hl : raw2783step1Labels = raw2783step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2783step0 raw2783step0Labels permutation138 permutation3
    mixedMoment B raw2783step1 raw2783step1Labels = mixedMoment B raw2783step2 raw2783step2Labels := by
      have ha : raw2783step2 = -raw2783step1 := by apply Matrix.ext; change ∀ i j, raw2783step2 i j = -(raw2783step1 i j); unfold raw2783step2 raw2783step1; decide +kernel
      have hl : raw2783step2Labels = raw2783step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw2784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1]]
def raw2784step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw2784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2784step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2784step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2784 raw2784Labels = mixedMoment B node4015 node4015Labels := by
  calc
    mixedMoment B raw2784 raw2784Labels = mixedMoment B raw2784step0 raw2784step0Labels := by
      have hz : ∀ j, raw2784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2784step0 = (fun i j => raw2784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2784step0 raw2784; decide +kernel
      have hl : raw2784step0Labels = raw2784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2784 raw2784Labels permutation434 hz
    mixedMoment B raw2784step0 raw2784step0Labels = mixedMoment B raw2784step1 raw2784step1Labels := by
      have hz : ∀ j, raw2784step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2784step1 = (fun i j => raw2784step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2784step1 raw2784step0; decide +kernel
      have hl : raw2784step1Labels = raw2784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2784step0 raw2784step0Labels permutation80 hz
    mixedMoment B raw2784step1 raw2784step1Labels = mixedMoment B raw2784step2 raw2784step2Labels := by
      have ha : raw2784step2 = (fun i j => raw2784step1 (permutation28 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2784step2 raw2784step1; decide +kernel
      have hl : raw2784step2Labels = raw2784step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2784step1 raw2784step1Labels permutation28 permutation3
    mixedMoment B raw2784step2 raw2784step2Labels = mixedMoment B raw2784step3 raw2784step3Labels := by
      have ha : raw2784step3 = -raw2784step2 := by apply Matrix.ext; change ∀ i j, raw2784step3 i j = -(raw2784step2 i j); unfold raw2784step3 raw2784step2; decide +kernel
      have hl : raw2784step3Labels = raw2784step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw2785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2785step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw2785step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2785step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2785 raw2785Labels = mixedMoment B node4055 node4055Labels := by
  calc
    mixedMoment B raw2785 raw2785Labels = mixedMoment B raw2785step0 raw2785step0Labels := by
      have hz : ∀ j, raw2785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2785step0 = (fun i j => raw2785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2785step0 raw2785; decide +kernel
      have hl : raw2785step0Labels = raw2785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2785 raw2785Labels permutation434 hz
    mixedMoment B raw2785step0 raw2785step0Labels = mixedMoment B raw2785step1 raw2785step1Labels := by
      have hz : ∀ j, raw2785step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2785step1 = (fun i j => raw2785step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2785step1 raw2785step0; decide +kernel
      have hl : raw2785step1Labels = raw2785step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2785step0 raw2785step0Labels permutation80 hz
    mixedMoment B raw2785step1 raw2785step1Labels = mixedMoment B raw2785step2 raw2785step2Labels := by
      have ha : raw2785step2 = (fun i j => raw2785step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2785step2 raw2785step1; decide +kernel
      have hl : raw2785step2Labels = raw2785step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2785step1 raw2785step1Labels permutation24 permutation6
    _ = mixedMoment B node4055 node4055Labels := by rfl

def raw2786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2786step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2786step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2786step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2786 raw2786Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw2786 raw2786Labels = mixedMoment B raw2786step0 raw2786step0Labels := by
      have hz : ∀ j, raw2786 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2786step0 = (fun i j => raw2786 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2786step0 raw2786; decide +kernel
      have hl : raw2786step0Labels = raw2786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2786 raw2786Labels permutation434 hz
    mixedMoment B raw2786step0 raw2786step0Labels = mixedMoment B raw2786step1 raw2786step1Labels := by
      have hz : ∀ j, raw2786step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2786step1 = (fun i j => raw2786step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2786step1 raw2786step0; decide +kernel
      have hl : raw2786step1Labels = raw2786step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2786step0 raw2786step0Labels permutation80 hz
    mixedMoment B raw2786step1 raw2786step1Labels = mixedMoment B raw2786step2 raw2786step2Labels := by
      have ha : raw2786step2 = (fun i j => raw2786step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2786step2 raw2786step1; decide +kernel
      have hl : raw2786step2Labels = raw2786step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2786step1 raw2786step1Labels permutation10 permutation3
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw2787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2787step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2787 raw2787Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw2787 raw2787Labels = mixedMoment B raw2787step0 raw2787step0Labels := by
      have hz : ∀ j, raw2787 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2787step0 = (fun i j => raw2787 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2787step0 raw2787; decide +kernel
      have hl : raw2787step0Labels = raw2787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2787 raw2787Labels permutation434 hz
    mixedMoment B raw2787step0 raw2787step0Labels = mixedMoment B raw2787step1 raw2787step1Labels := by
      have ha : raw2787step1 = (fun i j => raw2787step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2787step1 raw2787step0; decide +kernel
      have hl : raw2787step1Labels = raw2787step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2787step0 raw2787step0Labels permutation139 permutation3
    mixedMoment B raw2787step1 raw2787step1Labels = mixedMoment B raw2787step2 raw2787step2Labels := by
      have ha : raw2787step2 = -raw2787step1 := by apply Matrix.ext; change ∀ i j, raw2787step2 i j = -(raw2787step1 i j); unfold raw2787step2 raw2787step1; decide +kernel
      have hl : raw2787step2Labels = raw2787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw2788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2788step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2788 raw2788Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw2788 raw2788Labels = mixedMoment B raw2788step0 raw2788step0Labels := by
      have hz : ∀ j, raw2788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2788step0 = (fun i j => raw2788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2788step0 raw2788; decide +kernel
      have hl : raw2788step0Labels = raw2788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2788 raw2788Labels permutation346 hz
    mixedMoment B raw2788step0 raw2788step0Labels = mixedMoment B raw2788step1 raw2788step1Labels := by
      have ha : raw2788step1 = (fun i j => raw2788step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2788step1 raw2788step0; decide +kernel
      have hl : raw2788step1Labels = raw2788step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2788step0 raw2788step0Labels permutation139 permutation3
    mixedMoment B raw2788step1 raw2788step1Labels = mixedMoment B raw2788step2 raw2788step2Labels := by
      have ha : raw2788step2 = -raw2788step1 := by apply Matrix.ext; change ∀ i j, raw2788step2 i j = -(raw2788step1 i j); unfold raw2788step2 raw2788step1; decide +kernel
      have hl : raw2788step2Labels = raw2788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw2789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2789step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![-1, 2, -1], ![2, -1, -1]]
def raw2789step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2789step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2789 raw2789Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw2789 raw2789Labels = mixedMoment B raw2789step0 raw2789step0Labels := by
      have hz : ∀ j, raw2789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2789step0 = (fun i j => raw2789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2789step0 raw2789; decide +kernel
      have hl : raw2789step0Labels = raw2789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2789 raw2789Labels permutation434 hz
    mixedMoment B raw2789step0 raw2789step0Labels = mixedMoment B raw2789step1 raw2789step1Labels := by
      have hz : ∀ j, raw2789step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2789step1 = (fun i j => raw2789step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2789step1 raw2789step0; decide +kernel
      have hl : raw2789step1Labels = raw2789step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2789step0 raw2789step0Labels permutation80 hz
    mixedMoment B raw2789step1 raw2789step1Labels = mixedMoment B raw2789step2 raw2789step2Labels := by
      have ha : raw2789step2 = (fun i j => raw2789step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2789step2 raw2789step1; decide +kernel
      have hl : raw2789step2Labels = raw2789step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2789step1 raw2789step1Labels permutation10 permutation3
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw2790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2790step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw2790step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2790 raw2790Labels = mixedMoment B node4015 node4015Labels := by
  calc
    mixedMoment B raw2790 raw2790Labels = mixedMoment B raw2790step0 raw2790step0Labels := by
      have hz : ∀ j, raw2790 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2790step0 = (fun i j => raw2790 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2790step0 raw2790; decide +kernel
      have hl : raw2790step0Labels = raw2790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2790 raw2790Labels permutation434 hz
    mixedMoment B raw2790step0 raw2790step0Labels = mixedMoment B raw2790step1 raw2790step1Labels := by
      have hz : ∀ j, raw2790step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2790step1 = (fun i j => raw2790step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2790step1 raw2790step0; decide +kernel
      have hl : raw2790step1Labels = raw2790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2790step0 raw2790step0Labels permutation80 hz
    mixedMoment B raw2790step1 raw2790step1Labels = mixedMoment B raw2790step2 raw2790step2Labels := by
      have ha : raw2790step2 = (fun i j => raw2790step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2790step2 raw2790step1; decide +kernel
      have hl : raw2790step2Labels = raw2790step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2790step1 raw2790step1Labels permutation11 permutation3
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw2791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2791step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2791 raw2791Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2791 raw2791Labels = mixedMoment B raw2791step0 raw2791step0Labels := by
      have hz : ∀ j, raw2791 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2791step0 = (fun i j => raw2791 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2791step0 raw2791; decide +kernel
      have hl : raw2791step0Labels = raw2791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2791 raw2791Labels permutation434 hz
    mixedMoment B raw2791step0 raw2791step0Labels = mixedMoment B raw2791step1 raw2791step1Labels := by
      have ha : raw2791step1 = (fun i j => raw2791step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2791step1 raw2791step0; decide +kernel
      have hl : raw2791step1Labels = raw2791step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2791step0 raw2791step0Labels permutation44 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw2792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2792 raw2792Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw2792 raw2792Labels = mixedMoment B raw2792step0 raw2792step0Labels := by
      have hz : ∀ j, raw2792 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2792step0 = (fun i j => raw2792 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2792step0 raw2792; decide +kernel
      have hl : raw2792step0Labels = raw2792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2792 raw2792Labels permutation434 hz
    mixedMoment B raw2792step0 raw2792step0Labels = mixedMoment B raw2792step1 raw2792step1Labels := by
      have ha : raw2792step1 = (fun i j => raw2792step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2792step1 raw2792step0; decide +kernel
      have hl : raw2792step1Labels = raw2792step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2792step0 raw2792step0Labels permutation145 permutation3
    mixedMoment B raw2792step1 raw2792step1Labels = mixedMoment B raw2792step2 raw2792step2Labels := by
      have ha : raw2792step2 = -raw2792step1 := by apply Matrix.ext; change ∀ i j, raw2792step2 i j = -(raw2792step1 i j); unfold raw2792step2 raw2792step1; decide +kernel
      have hl : raw2792step2Labels = raw2792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw2793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2793 raw2793Labels = mixedMoment B node3971 node3971Labels := by
  calc
    mixedMoment B raw2793 raw2793Labels = mixedMoment B raw2793step0 raw2793step0Labels := by
      have ha : raw2793step0 = (fun i j => raw2793 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2793step0 raw2793; decide +kernel
      have hl : raw2793step0Labels = raw2793Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2793 raw2793Labels permutation212 permutation3
    _ = mixedMoment B node3971 node3971Labels := by rfl

def raw2794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2794step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2794 raw2794Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw2794 raw2794Labels = mixedMoment B raw2794step0 raw2794step0Labels := by
      have hz : ∀ j, raw2794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2794step0 = (fun i j => raw2794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2794step0 raw2794; decide +kernel
      have hl : raw2794step0Labels = raw2794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2794 raw2794Labels permutation434 hz
    mixedMoment B raw2794step0 raw2794step0Labels = mixedMoment B raw2794step1 raw2794step1Labels := by
      have ha : raw2794step1 = (fun i j => raw2794step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2794step1 raw2794step0; decide +kernel
      have hl : raw2794step1Labels = raw2794step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2794step0 raw2794step0Labels permutation44 permutation3
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw2795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2795 raw2795Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw2795 raw2795Labels = mixedMoment B raw2795step0 raw2795step0Labels := by
      have hz : ∀ j, raw2795 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2795step0 = (fun i j => raw2795 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2795step0 raw2795; decide +kernel
      have hl : raw2795step0Labels = raw2795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2795 raw2795Labels permutation434 hz
    mixedMoment B raw2795step0 raw2795step0Labels = mixedMoment B raw2795step1 raw2795step1Labels := by
      have ha : raw2795step1 = (fun i j => raw2795step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2795step1 raw2795step0; decide +kernel
      have hl : raw2795step1Labels = raw2795step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2795step0 raw2795step0Labels permutation45 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw2796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2796 raw2796Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2796 raw2796Labels = mixedMoment B raw2796step0 raw2796step0Labels := by
      have hz : ∀ j, raw2796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2796step0 = (fun i j => raw2796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2796step0 raw2796; decide +kernel
      have hl : raw2796step0Labels = raw2796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2796 raw2796Labels permutation346 hz
    mixedMoment B raw2796step0 raw2796step0Labels = mixedMoment B raw2796step1 raw2796step1Labels := by
      have ha : raw2796step1 = (fun i j => raw2796step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2796step1 raw2796step0; decide +kernel
      have hl : raw2796step1Labels = raw2796step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2796step0 raw2796step0Labels permutation44 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw2797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2797step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2797 raw2797Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw2797 raw2797Labels = mixedMoment B raw2797step0 raw2797step0Labels := by
      have hz : ∀ j, raw2797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2797step0 = (fun i j => raw2797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2797step0 raw2797; decide +kernel
      have hl : raw2797step0Labels = raw2797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2797 raw2797Labels permutation346 hz
    mixedMoment B raw2797step0 raw2797step0Labels = mixedMoment B raw2797step1 raw2797step1Labels := by
      have ha : raw2797step1 = (fun i j => raw2797step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2797step1 raw2797step0; decide +kernel
      have hl : raw2797step1Labels = raw2797step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2797step0 raw2797step0Labels permutation145 permutation3
    mixedMoment B raw2797step1 raw2797step1Labels = mixedMoment B raw2797step2 raw2797step2Labels := by
      have ha : raw2797step2 = -raw2797step1 := by apply Matrix.ext; change ∀ i j, raw2797step2 i j = -(raw2797step1 i j); unfold raw2797step2 raw2797step1; decide +kernel
      have hl : raw2797step2Labels = raw2797step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw2798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2798 raw2798Labels = mixedMoment B node3971 node3971Labels := by
  calc
    mixedMoment B raw2798 raw2798Labels = mixedMoment B raw2798step0 raw2798step0Labels := by
      have ha : raw2798step0 = (fun i j => raw2798 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2798step0 raw2798; decide +kernel
      have hl : raw2798step0Labels = raw2798Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2798 raw2798Labels permutation188 permutation3
    _ = mixedMoment B node3971 node3971Labels := by rfl

def raw2799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2799 raw2799Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw2799 raw2799Labels = mixedMoment B raw2799step0 raw2799step0Labels := by
      have hz : ∀ j, raw2799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2799step0 = (fun i j => raw2799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2799step0 raw2799; decide +kernel
      have hl : raw2799step0Labels = raw2799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2799 raw2799Labels permutation346 hz
    mixedMoment B raw2799step0 raw2799step0Labels = mixedMoment B raw2799step1 raw2799step1Labels := by
      have ha : raw2799step1 = (fun i j => raw2799step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2799step1 raw2799step0; decide +kernel
      have hl : raw2799step1Labels = raw2799step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2799step0 raw2799step0Labels permutation44 permutation3
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw2800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw2800step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2800 raw2800Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw2800 raw2800Labels = mixedMoment B raw2800step0 raw2800step0Labels := by
      have hz : ∀ j, raw2800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2800step0 = (fun i j => raw2800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2800step0 raw2800; decide +kernel
      have hl : raw2800step0Labels = raw2800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2800 raw2800Labels permutation346 hz
    mixedMoment B raw2800step0 raw2800step0Labels = mixedMoment B raw2800step1 raw2800step1Labels := by
      have ha : raw2800step1 = (fun i j => raw2800step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2800step1 raw2800step0; decide +kernel
      have hl : raw2800step1Labels = raw2800step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2800step0 raw2800step0Labels permutation45 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw2801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2801step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2801step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2801step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2801 raw2801Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw2801 raw2801Labels = mixedMoment B raw2801step0 raw2801step0Labels := by
      have hz : ∀ j, raw2801 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2801step0 = (fun i j => raw2801 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2801step0 raw2801; decide +kernel
      have hl : raw2801step0Labels = raw2801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2801 raw2801Labels permutation434 hz
    mixedMoment B raw2801step0 raw2801step0Labels = mixedMoment B raw2801step1 raw2801step1Labels := by
      have hz : ∀ j, raw2801step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2801step1 = (fun i j => raw2801step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2801step1 raw2801step0; decide +kernel
      have hl : raw2801step1Labels = raw2801step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2801step0 raw2801step0Labels permutation80 hz
    mixedMoment B raw2801step1 raw2801step1Labels = mixedMoment B raw2801step2 raw2801step2Labels := by
      have ha : raw2801step2 = (fun i j => raw2801step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2801step2 raw2801step1; decide +kernel
      have hl : raw2801step2Labels = raw2801step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2801step1 raw2801step1Labels permutation8 permutation3
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw2802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2802step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2802step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2802step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2802 raw2802Labels = mixedMoment B node4000 node4000Labels := by
  calc
    mixedMoment B raw2802 raw2802Labels = mixedMoment B raw2802step0 raw2802step0Labels := by
      have hz : ∀ j, raw2802 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2802step0 = (fun i j => raw2802 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2802step0 raw2802; decide +kernel
      have hl : raw2802step0Labels = raw2802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2802 raw2802Labels permutation434 hz
    mixedMoment B raw2802step0 raw2802step0Labels = mixedMoment B raw2802step1 raw2802step1Labels := by
      have hz : ∀ j, raw2802step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2802step1 = (fun i j => raw2802step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2802step1 raw2802step0; decide +kernel
      have hl : raw2802step1Labels = raw2802step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2802step0 raw2802step0Labels permutation80 hz
    mixedMoment B raw2802step1 raw2802step1Labels = mixedMoment B raw2802step2 raw2802step2Labels := by
      have ha : raw2802step2 = (fun i j => raw2802step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2802step2 raw2802step1; decide +kernel
      have hl : raw2802step2Labels = raw2802step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2802step1 raw2802step1Labels permutation8 permutation3
    _ = mixedMoment B node4000 node4000Labels := by rfl

def raw2803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2803step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2803 raw2803Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw2803 raw2803Labels = mixedMoment B raw2803step0 raw2803step0Labels := by
      have hz : ∀ j, raw2803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2803step0 = (fun i j => raw2803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2803step0 raw2803; decide +kernel
      have hl : raw2803step0Labels = raw2803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2803 raw2803Labels permutation434 hz
    mixedMoment B raw2803step0 raw2803step0Labels = mixedMoment B raw2803step1 raw2803step1Labels := by
      have ha : raw2803step1 = (fun i j => raw2803step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2803step1 raw2803step0; decide +kernel
      have hl : raw2803step1Labels = raw2803step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2803step0 raw2803step0Labels permutation38 permutation3
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw2804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2804 raw2804Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw2804 raw2804Labels = mixedMoment B raw2804step0 raw2804step0Labels := by
      have hz : ∀ j, raw2804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2804step0 = (fun i j => raw2804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2804step0 raw2804; decide +kernel
      have hl : raw2804step0Labels = raw2804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2804 raw2804Labels permutation346 hz
    mixedMoment B raw2804step0 raw2804step0Labels = mixedMoment B raw2804step1 raw2804step1Labels := by
      have ha : raw2804step1 = (fun i j => raw2804step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2804step1 raw2804step0; decide +kernel
      have hl : raw2804step1Labels = raw2804step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2804step0 raw2804step0Labels permutation38 permutation3
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw2805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2805step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2805 raw2805Labels = mixedMoment B node4018 node4018Labels := by
  calc
    mixedMoment B raw2805 raw2805Labels = mixedMoment B raw2805step0 raw2805step0Labels := by
      have hz : ∀ j, raw2805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2805step0 = (fun i j => raw2805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2805step0 raw2805; decide +kernel
      have hl : raw2805step0Labels = raw2805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2805 raw2805Labels permutation434 hz
    mixedMoment B raw2805step0 raw2805step0Labels = mixedMoment B raw2805step1 raw2805step1Labels := by
      have hz : ∀ j, raw2805step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2805step1 = (fun i j => raw2805step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2805step1 raw2805step0; decide +kernel
      have hl : raw2805step1Labels = raw2805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2805step0 raw2805step0Labels permutation80 hz
    mixedMoment B raw2805step1 raw2805step1Labels = mixedMoment B raw2805step2 raw2805step2Labels := by
      have ha : raw2805step2 = (fun i j => raw2805step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2805step2 raw2805step1; decide +kernel
      have hl : raw2805step2Labels = raw2805step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2805step1 raw2805step1Labels permutation8 permutation3
    _ = mixedMoment B node4018 node4018Labels := by rfl

def raw2806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2806step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw2806step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2806step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw2806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2806 raw2806Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw2806 raw2806Labels = mixedMoment B raw2806step0 raw2806step0Labels := by
      have hz : ∀ j, raw2806 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2806step0 = (fun i j => raw2806 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2806step0 raw2806; decide +kernel
      have hl : raw2806step0Labels = raw2806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2806 raw2806Labels permutation434 hz
    mixedMoment B raw2806step0 raw2806step0Labels = mixedMoment B raw2806step1 raw2806step1Labels := by
      have hz : ∀ j, raw2806step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2806step1 = (fun i j => raw2806step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2806step1 raw2806step0; decide +kernel
      have hl : raw2806step1Labels = raw2806step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2806step0 raw2806step0Labels permutation80 hz
    mixedMoment B raw2806step1 raw2806step1Labels = mixedMoment B raw2806step2 raw2806step2Labels := by
      have ha : raw2806step2 = (fun i j => raw2806step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2806step2 raw2806step1; decide +kernel
      have hl : raw2806step2Labels = raw2806step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2806step1 raw2806step1Labels permutation10 permutation3
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw2807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2807step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1]]
def raw2807step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2807step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw2807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2807step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2807step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2807 raw2807Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw2807 raw2807Labels = mixedMoment B raw2807step0 raw2807step0Labels := by
      have hz : ∀ j, raw2807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2807step0 = (fun i j => raw2807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2807step0 raw2807; decide +kernel
      have hl : raw2807step0Labels = raw2807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2807 raw2807Labels permutation434 hz
    mixedMoment B raw2807step0 raw2807step0Labels = mixedMoment B raw2807step1 raw2807step1Labels := by
      have hz : ∀ j, raw2807step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2807step1 = (fun i j => raw2807step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2807step1 raw2807step0; decide +kernel
      have hl : raw2807step1Labels = raw2807step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2807step0 raw2807step0Labels permutation80 hz
    mixedMoment B raw2807step1 raw2807step1Labels = mixedMoment B raw2807step2 raw2807step2Labels := by
      have ha : raw2807step2 = (fun i j => raw2807step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2807step2 raw2807step1; decide +kernel
      have hl : raw2807step2Labels = raw2807step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2807step1 raw2807step1Labels permutation31 permutation3
    mixedMoment B raw2807step2 raw2807step2Labels = mixedMoment B raw2807step3 raw2807step3Labels := by
      have ha : raw2807step3 = -raw2807step2 := by apply Matrix.ext; change ∀ i j, raw2807step3 i j = -(raw2807step2 i j); unfold raw2807step3 raw2807step2; decide +kernel
      have hl : raw2807step3Labels = raw2807step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw2808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2808step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2808 raw2808Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2808 raw2808Labels = mixedMoment B raw2808step0 raw2808step0Labels := by
      have hz : ∀ j, raw2808 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2808step0 = (fun i j => raw2808 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2808step0 raw2808; decide +kernel
      have hl : raw2808step0Labels = raw2808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2808 raw2808Labels permutation434 hz
    mixedMoment B raw2808step0 raw2808step0Labels = mixedMoment B raw2808step1 raw2808step1Labels := by
      have ha : raw2808step1 = (fun i j => raw2808step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2808step1 raw2808step0; decide +kernel
      have hl : raw2808step1Labels = raw2808step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2808step0 raw2808step0Labels permutation139 permutation3
    mixedMoment B raw2808step1 raw2808step1Labels = mixedMoment B raw2808step2 raw2808step2Labels := by
      have ha : raw2808step2 = -raw2808step1 := by apply Matrix.ext; change ∀ i j, raw2808step2 i j = -(raw2808step1 i j); unfold raw2808step2 raw2808step1; decide +kernel
      have hl : raw2808step2Labels = raw2808step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw2809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw2809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2809 raw2809Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw2809 raw2809Labels = mixedMoment B raw2809step0 raw2809step0Labels := by
      have hz : ∀ j, raw2809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2809step0 = (fun i j => raw2809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2809step0 raw2809; decide +kernel
      have hl : raw2809step0Labels = raw2809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2809 raw2809Labels permutation346 hz
    mixedMoment B raw2809step0 raw2809step0Labels = mixedMoment B raw2809step1 raw2809step1Labels := by
      have ha : raw2809step1 = (fun i j => raw2809step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2809step1 raw2809step0; decide +kernel
      have hl : raw2809step1Labels = raw2809step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2809step0 raw2809step0Labels permutation139 permutation3
    mixedMoment B raw2809step1 raw2809step1Labels = mixedMoment B raw2809step2 raw2809step2Labels := by
      have ha : raw2809step2 = -raw2809step1 := by apply Matrix.ext; change ∀ i j, raw2809step2 i j = -(raw2809step1 i j); unfold raw2809step2 raw2809step1; decide +kernel
      have hl : raw2809step2Labels = raw2809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw2810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw2810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -2, -1]]
def raw2810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![3, -2, -1]]
def raw2810step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw2810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2810step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2810step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2810 raw2810Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw2810 raw2810Labels = mixedMoment B raw2810step0 raw2810step0Labels := by
      have hz : ∀ j, raw2810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2810step0 = (fun i j => raw2810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2810step0 raw2810; decide +kernel
      have hl : raw2810step0Labels = raw2810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2810 raw2810Labels permutation434 hz
    mixedMoment B raw2810step0 raw2810step0Labels = mixedMoment B raw2810step1 raw2810step1Labels := by
      have hz : ∀ j, raw2810step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2810step1 = (fun i j => raw2810step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2810step1 raw2810step0; decide +kernel
      have hl : raw2810step1Labels = raw2810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2810step0 raw2810step0Labels permutation80 hz
    mixedMoment B raw2810step1 raw2810step1Labels = mixedMoment B raw2810step2 raw2810step2Labels := by
      have ha : raw2810step2 = (fun i j => raw2810step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2810step2 raw2810step1; decide +kernel
      have hl : raw2810step2Labels = raw2810step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2810step1 raw2810step1Labels permutation29 permutation3
    mixedMoment B raw2810step2 raw2810step2Labels = mixedMoment B raw2810step3 raw2810step3Labels := by
      have ha : raw2810step3 = -raw2810step2 := by apply Matrix.ext; change ∀ i j, raw2810step3 i j = -(raw2810step2 i j); unfold raw2810step3 raw2810step2; decide +kernel
      have hl : raw2810step3Labels = raw2810step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw2811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2811Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2811step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2811step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2811 raw2811Labels = mixedMoment B node378 node378Labels := by
  calc
    mixedMoment B raw2811 raw2811Labels = mixedMoment B raw2811step0 raw2811step0Labels := by
      have hz : ∀ j, raw2811 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2811step0 = (fun i j => raw2811 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2811step0 raw2811; decide +kernel
      have hl : raw2811step0Labels = raw2811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2811 raw2811Labels permutation434 hz
    mixedMoment B raw2811step0 raw2811step0Labels = mixedMoment B raw2811step1 raw2811step1Labels := by
      have ha : raw2811step1 = (fun i j => raw2811step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2811step1 raw2811step0; decide +kernel
      have hl : raw2811step1Labels = raw2811step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2811step0 raw2811step0Labels permutation44 permutation3
    _ = mixedMoment B node378 node378Labels := by rfl

def raw2812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2812Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2812step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2812step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2812 raw2812Labels = mixedMoment B node521 node521Labels := by
  calc
    mixedMoment B raw2812 raw2812Labels = mixedMoment B raw2812step0 raw2812step0Labels := by
      have hz : ∀ j, raw2812 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2812step0 = (fun i j => raw2812 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2812step0 raw2812; decide +kernel
      have hl : raw2812step0Labels = raw2812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2812 raw2812Labels permutation434 hz
    mixedMoment B raw2812step0 raw2812step0Labels = mixedMoment B raw2812step1 raw2812step1Labels := by
      have ha : raw2812step1 = (fun i j => raw2812step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2812step1 raw2812step0; decide +kernel
      have hl : raw2812step1Labels = raw2812step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2812step0 raw2812step0Labels permutation34 permutation2
    _ = mixedMoment B node521 node521Labels := by rfl

def raw2813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2813Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2813step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2813step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2813 raw2813Labels = mixedMoment B node527 node527Labels := by
  calc
    mixedMoment B raw2813 raw2813Labels = mixedMoment B raw2813step0 raw2813step0Labels := by
      have hz : ∀ j, raw2813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2813step0 = (fun i j => raw2813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2813step0 raw2813; decide +kernel
      have hl : raw2813step0Labels = raw2813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2813 raw2813Labels permutation434 hz
    mixedMoment B raw2813step0 raw2813step0Labels = mixedMoment B raw2813step1 raw2813step1Labels := by
      have hz : ∀ j, raw2813step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2813step1 = (fun i j => raw2813step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2813step1 raw2813step0; decide +kernel
      have hl : raw2813step1Labels = raw2813step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2813step0 raw2813step0Labels permutation80 hz
    _ = mixedMoment B node527 node527Labels := by rfl

def raw2814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw2814Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2814step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2814 raw2814Labels = mixedMoment B node518 node518Labels := by
  calc
    mixedMoment B raw2814 raw2814Labels = mixedMoment B raw2814step0 raw2814step0Labels := by
      have ha : raw2814step0 = (fun i j => raw2814 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2814step0 raw2814; decide +kernel
      have hl : raw2814step0Labels = raw2814Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2814 raw2814Labels permutation212 permutation3
    _ = mixedMoment B node518 node518Labels := by rfl

def raw2815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2815Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -1, -1]]
def raw2815step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw2815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2815step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical2815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2815 raw2815Labels = mixedMoment B node514 node514Labels := by
  calc
    mixedMoment B raw2815 raw2815Labels = mixedMoment B raw2815step0 raw2815step0Labels := by
      have hz : ∀ j, raw2815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2815step0 = (fun i j => raw2815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2815step0 raw2815; decide +kernel
      have hl : raw2815step0Labels = raw2815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2815 raw2815Labels permutation434 hz
    mixedMoment B raw2815step0 raw2815step0Labels = mixedMoment B raw2815step1 raw2815step1Labels := by
      have ha : raw2815step1 = (fun i j => raw2815step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2815step1 raw2815step0; decide +kernel
      have hl : raw2815step1Labels = raw2815step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2815step0 raw2815step0Labels permutation44 permutation3
    _ = mixedMoment B node514 node514Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
