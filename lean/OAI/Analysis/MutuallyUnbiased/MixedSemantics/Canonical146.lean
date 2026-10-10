import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18688step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18688 raw18688Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw18688 raw18688Labels = mixedMoment B raw18688step0 raw18688step0Labels := by
      have ha : raw18688step0 = (fun i j => raw18688 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18688step0 raw18688; decide +kernel
      have hl : raw18688step0Labels = raw18688Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18688 raw18688Labels permutation181 permutation3
    mixedMoment B raw18688step0 raw18688step0Labels = mixedMoment B raw18688step1 raw18688step1Labels := by
      have ha : raw18688step1 = raw18688step0 := by apply Matrix.ext; unfold raw18688step1 raw18688step0; decide +kernel
      have hl : raw18688step0Labels = labelEmbedding6 ∘ raw18688step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18688step0 raw18688step0Labels raw18688step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw18689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18689step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18689step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18689step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18689 raw18689Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw18689 raw18689Labels = mixedMoment B raw18689step0 raw18689step0Labels := by
      have ha : raw18689step0 = (fun i j => raw18689 (permutation417 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18689step0 raw18689; decide +kernel
      have hl : raw18689step0Labels = raw18689Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18689 raw18689Labels permutation417 permutation4
    mixedMoment B raw18689step0 raw18689step0Labels = mixedMoment B raw18689step1 raw18689step1Labels := by
      have ha : raw18689step1 = -raw18689step0 := by apply Matrix.ext; change ∀ i j, raw18689step1 i j = -(raw18689step0 i j); unfold raw18689step1 raw18689step0; decide +kernel
      have hl : raw18689step1Labels = raw18689step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18689step1 raw18689step1Labels = mixedMoment B raw18689step2 raw18689step2Labels := by
      have ha : raw18689step2 = raw18689step1 := by apply Matrix.ext; unfold raw18689step2 raw18689step1; decide +kernel
      have hl : raw18689step1Labels = labelEmbedding7 ∘ raw18689step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18689step1 raw18689step1Labels raw18689step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw18690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18690step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18690step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18690step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18690 raw18690Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18690 raw18690Labels = mixedMoment B raw18690step0 raw18690step0Labels := by
      have hz : ∀ j, raw18690 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18690step0 = (fun i j => raw18690 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18690step0 raw18690; decide +kernel
      have hl : raw18690step0Labels = raw18690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18690 raw18690Labels permutation520 hz
    mixedMoment B raw18690step0 raw18690step0Labels = mixedMoment B raw18690step1 raw18690step1Labels := by
      have ha : raw18690step1 = (fun i j => raw18690step0 (permutation110 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18690step1 raw18690step0; decide +kernel
      have hl : raw18690step1Labels = raw18690step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18690step0 raw18690step0Labels permutation110 permutation4
    mixedMoment B raw18690step1 raw18690step1Labels = mixedMoment B raw18690step2 raw18690step2Labels := by
      have ha : raw18690step2 = raw18690step1 := by apply Matrix.ext; unfold raw18690step2 raw18690step1; decide +kernel
      have hl : raw18690step1Labels = labelEmbedding7 ∘ raw18690step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18690step1 raw18690step1Labels raw18690step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw18691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18691step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18691step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18691step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18691 raw18691Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18691 raw18691Labels = mixedMoment B raw18691step0 raw18691step0Labels := by
      have ha : raw18691step0 = (fun i j => raw18691 (permutation627 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18691step0 raw18691; decide +kernel
      have hl : raw18691step0Labels = raw18691Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18691 raw18691Labels permutation627 permutation4
    mixedMoment B raw18691step0 raw18691step0Labels = mixedMoment B raw18691step1 raw18691step1Labels := by
      have ha : raw18691step1 = -raw18691step0 := by apply Matrix.ext; change ∀ i j, raw18691step1 i j = -(raw18691step0 i j); unfold raw18691step1 raw18691step0; decide +kernel
      have hl : raw18691step1Labels = raw18691step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18691step1 raw18691step1Labels = mixedMoment B raw18691step2 raw18691step2Labels := by
      have ha : raw18691step2 = raw18691step1 := by apply Matrix.ext; unfold raw18691step2 raw18691step1; decide +kernel
      have hl : raw18691step1Labels = labelEmbedding7 ∘ raw18691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18691step1 raw18691step1Labels raw18691step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw18692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18692step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18692step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18692 raw18692Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw18692 raw18692Labels = mixedMoment B raw18692step0 raw18692step0Labels := by
      have ha : raw18692step0 = (fun i j => raw18692 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18692step0 raw18692; decide +kernel
      have hl : raw18692step0Labels = raw18692Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18692 raw18692Labels permutation171 permutation3
    mixedMoment B raw18692step0 raw18692step0Labels = mixedMoment B raw18692step1 raw18692step1Labels := by
      have ha : raw18692step1 = raw18692step0 := by apply Matrix.ext; unfold raw18692step1 raw18692step0; decide +kernel
      have hl : raw18692step0Labels = labelEmbedding6 ∘ raw18692step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18692step0 raw18692step0Labels raw18692step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw18693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18693step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18693 raw18693Labels = mixedMoment B node5461 node5461Labels := by
  calc
    mixedMoment B raw18693 raw18693Labels = mixedMoment B raw18693step0 raw18693step0Labels := by
      have ha : raw18693step0 = (fun i j => raw18693 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18693step0 raw18693; decide +kernel
      have hl : raw18693step0Labels = raw18693Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18693 raw18693Labels permutation160 permutation2
    _ = mixedMoment B node5461 node5461Labels := by rfl

def raw18694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18694step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18694 raw18694Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18694 raw18694Labels = mixedMoment B raw18694step0 raw18694step0Labels := by
      have hz : ∀ j, raw18694 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18694step0 = (fun i j => raw18694 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18694step0 raw18694; decide +kernel
      have hl : raw18694step0Labels = raw18694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18694 raw18694Labels permutation520 hz
    mixedMoment B raw18694step0 raw18694step0Labels = mixedMoment B raw18694step1 raw18694step1Labels := by
      have ha : raw18694step1 = (fun i j => raw18694step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18694step1 raw18694step0; decide +kernel
      have hl : raw18694step1Labels = raw18694step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18694step0 raw18694step0Labels permutation34 permutation2
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw18695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18695step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18695step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18695step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18695 raw18695Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18695 raw18695Labels = mixedMoment B raw18695step0 raw18695step0Labels := by
      have ha : raw18695step0 = (fun i j => raw18695 (permutation641 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18695step0 raw18695; decide +kernel
      have hl : raw18695step0Labels = raw18695Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18695 raw18695Labels permutation641 permutation6
    mixedMoment B raw18695step0 raw18695step0Labels = mixedMoment B raw18695step1 raw18695step1Labels := by
      have ha : raw18695step1 = raw18695step0 := by apply Matrix.ext; unfold raw18695step1 raw18695step0; decide +kernel
      have hl : raw18695step0Labels = labelEmbedding9 ∘ raw18695step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18695step0 raw18695step0Labels raw18695step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18696step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18696step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18696 raw18696Labels = mixedMoment B node5069 node5069Labels := by
  calc
    mixedMoment B raw18696 raw18696Labels = mixedMoment B raw18696step0 raw18696step0Labels := by
      have ha : raw18696step0 = (fun i j => raw18696 (permutation494 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18696step0 raw18696; decide +kernel
      have hl : raw18696step0Labels = raw18696Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18696 raw18696Labels permutation494 permutation5
    mixedMoment B raw18696step0 raw18696step0Labels = mixedMoment B raw18696step1 raw18696step1Labels := by
      have ha : raw18696step1 = raw18696step0 := by apply Matrix.ext; unfold raw18696step1 raw18696step0; decide +kernel
      have hl : raw18696step0Labels = labelEmbedding8 ∘ raw18696step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18696step0 raw18696step0Labels raw18696step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5069 node5069Labels := by rfl

def raw18697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18697step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18697step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18697 raw18697Labels = mixedMoment B node5092 node5092Labels := by
  calc
    mixedMoment B raw18697 raw18697Labels = mixedMoment B raw18697step0 raw18697step0Labels := by
      have ha : raw18697step0 = (fun i j => raw18697 (permutation503 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18697step0 raw18697; decide +kernel
      have hl : raw18697step0Labels = raw18697Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18697 raw18697Labels permutation503 permutation5
    mixedMoment B raw18697step0 raw18697step0Labels = mixedMoment B raw18697step1 raw18697step1Labels := by
      have ha : raw18697step1 = raw18697step0 := by apply Matrix.ext; unfold raw18697step1 raw18697step0; decide +kernel
      have hl : raw18697step0Labels = labelEmbedding8 ∘ raw18697step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18697step0 raw18697step0Labels raw18697step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5092 node5092Labels := by rfl

def raw18698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18698step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18698 raw18698Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw18698 raw18698Labels = mixedMoment B raw18698step0 raw18698step0Labels := by
      have ha : raw18698step0 = (fun i j => raw18698 (permutation493 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18698step0 raw18698; decide +kernel
      have hl : raw18698step0Labels = raw18698Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18698 raw18698Labels permutation493 permutation5
    mixedMoment B raw18698step0 raw18698step0Labels = mixedMoment B raw18698step1 raw18698step1Labels := by
      have ha : raw18698step1 = raw18698step0 := by apply Matrix.ext; unfold raw18698step1 raw18698step0; decide +kernel
      have hl : raw18698step0Labels = labelEmbedding8 ∘ raw18698step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18698step0 raw18698step0Labels raw18698step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

def raw18699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18699step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18699 raw18699Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw18699 raw18699Labels = mixedMoment B raw18699step0 raw18699step0Labels := by
      have hz : ∀ j, raw18699 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18699step0 = (fun i j => raw18699 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18699step0 raw18699; decide +kernel
      have hl : raw18699step0Labels = raw18699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18699 raw18699Labels permutation520 hz
    mixedMoment B raw18699step0 raw18699step0Labels = mixedMoment B raw18699step1 raw18699step1Labels := by
      have ha : raw18699step1 = (fun i j => raw18699step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18699step1 raw18699step0; decide +kernel
      have hl : raw18699step1Labels = raw18699step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18699step0 raw18699step0Labels permutation115 permutation5
    mixedMoment B raw18699step1 raw18699step1Labels = mixedMoment B raw18699step2 raw18699step2Labels := by
      have ha : raw18699step2 = raw18699step1 := by apply Matrix.ext; unfold raw18699step2 raw18699step1; decide +kernel
      have hl : raw18699step1Labels = labelEmbedding8 ∘ raw18699step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18699step1 raw18699step1Labels raw18699step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw18700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18700step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18700step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18700 raw18700Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw18700 raw18700Labels = mixedMoment B raw18700step0 raw18700step0Labels := by
      have ha : raw18700step0 = (fun i j => raw18700 (permutation491 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18700step0 raw18700; decide +kernel
      have hl : raw18700step0Labels = raw18700Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18700 raw18700Labels permutation491 permutation5
    mixedMoment B raw18700step0 raw18700step0Labels = mixedMoment B raw18700step1 raw18700step1Labels := by
      have ha : raw18700step1 = raw18700step0 := by apply Matrix.ext; unfold raw18700step1 raw18700step0; decide +kernel
      have hl : raw18700step0Labels = labelEmbedding8 ∘ raw18700step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18700step0 raw18700step0Labels raw18700step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw18701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18701step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18701step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18701 raw18701Labels = mixedMoment B node5132 node5132Labels := by
  calc
    mixedMoment B raw18701 raw18701Labels = mixedMoment B raw18701step0 raw18701step0Labels := by
      have ha : raw18701step0 = (fun i j => raw18701 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18701step0 raw18701; decide +kernel
      have hl : raw18701step0Labels = raw18701Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18701 raw18701Labels permutation156 permutation3
    mixedMoment B raw18701step0 raw18701step0Labels = mixedMoment B raw18701step1 raw18701step1Labels := by
      have ha : raw18701step1 = raw18701step0 := by apply Matrix.ext; unfold raw18701step1 raw18701step0; decide +kernel
      have hl : raw18701step0Labels = labelEmbedding6 ∘ raw18701step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18701step0 raw18701step0Labels raw18701step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5132 node5132Labels := by rfl

def raw18702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18702step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18702step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18702 raw18702Labels = mixedMoment B node5362 node5362Labels := by
  calc
    mixedMoment B raw18702 raw18702Labels = mixedMoment B raw18702step0 raw18702step0Labels := by
      have ha : raw18702step0 = (fun i j => raw18702 (permutation567 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18702step0 raw18702; decide +kernel
      have hl : raw18702step0Labels = raw18702Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18702 raw18702Labels permutation567 permutation5
    mixedMoment B raw18702step0 raw18702step0Labels = mixedMoment B raw18702step1 raw18702step1Labels := by
      have ha : raw18702step1 = raw18702step0 := by apply Matrix.ext; unfold raw18702step1 raw18702step0; decide +kernel
      have hl : raw18702step0Labels = labelEmbedding8 ∘ raw18702step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18702step0 raw18702step0Labels raw18702step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5362 node5362Labels := by rfl

def raw18703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18703step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18703step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18703 raw18703Labels = mixedMoment B node5350 node5350Labels := by
  calc
    mixedMoment B raw18703 raw18703Labels = mixedMoment B raw18703step0 raw18703step0Labels := by
      have ha : raw18703step0 = (fun i j => raw18703 (permutation558 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18703step0 raw18703; decide +kernel
      have hl : raw18703step0Labels = raw18703Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18703 raw18703Labels permutation558 permutation5
    mixedMoment B raw18703step0 raw18703step0Labels = mixedMoment B raw18703step1 raw18703step1Labels := by
      have ha : raw18703step1 = raw18703step0 := by apply Matrix.ext; unfold raw18703step1 raw18703step0; decide +kernel
      have hl : raw18703step0Labels = labelEmbedding8 ∘ raw18703step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18703step0 raw18703step0Labels raw18703step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5350 node5350Labels := by rfl

def raw18704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw18704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18704step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18704step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18704 raw18704Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw18704 raw18704Labels = mixedMoment B raw18704step0 raw18704step0Labels := by
      have ha : raw18704step0 = (fun i j => raw18704 (permutation556 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18704step0 raw18704; decide +kernel
      have hl : raw18704step0Labels = raw18704Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18704 raw18704Labels permutation556 permutation5
    mixedMoment B raw18704step0 raw18704step0Labels = mixedMoment B raw18704step1 raw18704step1Labels := by
      have ha : raw18704step1 = raw18704step0 := by apply Matrix.ext; unfold raw18704step1 raw18704step0; decide +kernel
      have hl : raw18704step0Labels = labelEmbedding8 ∘ raw18704step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18704step0 raw18704step0Labels raw18704step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw18705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18705step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18705 raw18705Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18705 raw18705Labels = mixedMoment B raw18705step0 raw18705step0Labels := by
      have ha : raw18705step0 = (fun i j => raw18705 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18705step0 raw18705; decide +kernel
      have hl : raw18705step0Labels = raw18705Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18705 raw18705Labels permutation682 permutation2
    mixedMoment B raw18705step0 raw18705step0Labels = mixedMoment B raw18705step1 raw18705step1Labels := by
      have ha : raw18705step1 = -raw18705step0 := by apply Matrix.ext; change ∀ i j, raw18705step1 i j = -(raw18705step0 i j); unfold raw18705step1 raw18705step0; decide +kernel
      have hl : raw18705step1Labels = raw18705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18706 raw18706Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw18706 raw18706Labels = mixedMoment B raw18706step0 raw18706step0Labels := by
      have ha : raw18706step0 = (fun i j => raw18706 (permutation643 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18706step0 raw18706; decide +kernel
      have hl : raw18706step0Labels = raw18706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18706 raw18706Labels permutation643 permutation6
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw18707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18707step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18707 raw18707Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw18707 raw18707Labels = mixedMoment B raw18707step0 raw18707step0Labels := by
      have ha : raw18707step0 = (fun i j => raw18707 (permutation641 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18707step0 raw18707; decide +kernel
      have hl : raw18707step0Labels = raw18707Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18707 raw18707Labels permutation641 permutation6
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw18708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18708 raw18708Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw18708 raw18708Labels = mixedMoment B raw18708step0 raw18708step0Labels := by
      have ha : raw18708step0 = (fun i j => raw18708 (permutation641 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18708step0 raw18708; decide +kernel
      have hl : raw18708step0Labels = raw18708Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18708 raw18708Labels permutation641 permutation6
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw18709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18709step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18709step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18709 raw18709Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw18709 raw18709Labels = mixedMoment B raw18709step0 raw18709step0Labels := by
      have hz : ∀ j, raw18709 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18709step0 = (fun i j => raw18709 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18709step0 raw18709; decide +kernel
      have hl : raw18709step0Labels = raw18709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18709 raw18709Labels permutation520 hz
    mixedMoment B raw18709step0 raw18709step0Labels = mixedMoment B raw18709step1 raw18709step1Labels := by
      have ha : raw18709step1 = (fun i j => raw18709step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18709step1 raw18709step0; decide +kernel
      have hl : raw18709step1Labels = raw18709step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18709step0 raw18709step0Labels permutation140 permutation6
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw18710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18710 raw18710Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw18710 raw18710Labels = mixedMoment B raw18710step0 raw18710step0Labels := by
      have ha : raw18710step0 = (fun i j => raw18710 (permutation641 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18710step0 raw18710; decide +kernel
      have hl : raw18710step0Labels = raw18710Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18710 raw18710Labels permutation641 permutation6
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw18711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18711 raw18711Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw18711 raw18711Labels = mixedMoment B raw18711step0 raw18711step0Labels := by
      have ha : raw18711step0 = (fun i j => raw18711 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18711step0 raw18711; decide +kernel
      have hl : raw18711step0Labels = raw18711Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18711 raw18711Labels permutation181 permutation3
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw18712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18712step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18712step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18712 raw18712Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw18712 raw18712Labels = mixedMoment B raw18712step0 raw18712step0Labels := by
      have ha : raw18712step0 = (fun i j => raw18712 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18712step0 raw18712; decide +kernel
      have hl : raw18712step0Labels = raw18712Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18712 raw18712Labels permutation181 permutation3
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw18713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18713 raw18713Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw18713 raw18713Labels = mixedMoment B raw18713step0 raw18713step0Labels := by
      have ha : raw18713step0 = (fun i j => raw18713 (permutation641 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18713step0 raw18713; decide +kernel
      have hl : raw18713step0Labels = raw18713Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18713 raw18713Labels permutation641 permutation6
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw18714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18714step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18714step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18714 raw18714Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw18714 raw18714Labels = mixedMoment B raw18714step0 raw18714step0Labels := by
      have hz : ∀ j, raw18714 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18714step0 = (fun i j => raw18714 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18714step0 raw18714; decide +kernel
      have hl : raw18714step0Labels = raw18714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18714 raw18714Labels permutation520 hz
    mixedMoment B raw18714step0 raw18714step0Labels = mixedMoment B raw18714step1 raw18714step1Labels := by
      have ha : raw18714step1 = (fun i j => raw18714step0 (permutation140 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18714step1 raw18714step0; decide +kernel
      have hl : raw18714step1Labels = raw18714step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18714step0 raw18714step0Labels permutation140 permutation6
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw18715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18715 raw18715Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw18715 raw18715Labels = mixedMoment B raw18715step0 raw18715step0Labels := by
      have ha : raw18715step0 = (fun i j => raw18715 (permutation641 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18715step0 raw18715; decide +kernel
      have hl : raw18715step0Labels = raw18715Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18715 raw18715Labels permutation641 permutation6
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw18716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18716 raw18716Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw18716 raw18716Labels = mixedMoment B raw18716step0 raw18716step0Labels := by
      have ha : raw18716step0 = (fun i j => raw18716 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18716step0 raw18716; decide +kernel
      have hl : raw18716step0Labels = raw18716Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18716 raw18716Labels permutation171 permutation3
    _ = mixedMoment B node2587 node2587Labels := by rfl

def raw18717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18717step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18717 raw18717Labels = mixedMoment B node3927 node3927Labels := by
  calc
    mixedMoment B raw18717 raw18717Labels = mixedMoment B raw18717step0 raw18717step0Labels := by
      have ha : raw18717step0 = (fun i j => raw18717 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18717step0 raw18717; decide +kernel
      have hl : raw18717step0Labels = raw18717Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18717 raw18717Labels permutation171 permutation3
    _ = mixedMoment B node3927 node3927Labels := by rfl

def raw18718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18718 raw18718Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw18718 raw18718Labels = mixedMoment B raw18718step0 raw18718step0Labels := by
      have ha : raw18718step0 = (fun i j => raw18718 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18718step0 raw18718; decide +kernel
      have hl : raw18718step0Labels = raw18718Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18718 raw18718Labels permutation162 permutation3
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw18719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18719step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18719step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18719step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18719step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18719 raw18719Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw18719 raw18719Labels = mixedMoment B raw18719step0 raw18719step0Labels := by
      have hz : ∀ j, raw18719 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18719step0 = (fun i j => raw18719 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18719step0 raw18719; decide +kernel
      have hl : raw18719step0Labels = raw18719Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18719 raw18719Labels permutation520 hz
    mixedMoment B raw18719step0 raw18719step0Labels = mixedMoment B raw18719step1 raw18719step1Labels := by
      have ha : raw18719step1 = (fun i j => raw18719step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18719step1 raw18719step0; decide +kernel
      have hl : raw18719step1Labels = raw18719step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18719step0 raw18719step0Labels permutation36 permutation3
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw18720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18720step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18720 raw18720Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw18720 raw18720Labels = mixedMoment B raw18720step0 raw18720step0Labels := by
      have ha : raw18720step0 = (fun i j => raw18720 (permutation641 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18720step0 raw18720; decide +kernel
      have hl : raw18720step0Labels = raw18720Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18720 raw18720Labels permutation641 permutation6
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw18721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw18721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18721 raw18721Labels = mixedMoment B node2550 node2550Labels := by
  calc
    mixedMoment B raw18721 raw18721Labels = mixedMoment B raw18721step0 raw18721step0Labels := by
      have ha : raw18721step0 = (fun i j => raw18721 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18721step0 raw18721; decide +kernel
      have hl : raw18721step0Labels = raw18721Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18721 raw18721Labels permutation157 permutation3
    _ = mixedMoment B node2550 node2550Labels := by rfl

def raw18722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18722step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18722 raw18722Labels = mixedMoment B node3442 node3442Labels := by
  calc
    mixedMoment B raw18722 raw18722Labels = mixedMoment B raw18722step0 raw18722step0Labels := by
      have ha : raw18722step0 = (fun i j => raw18722 (permutation503 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18722step0 raw18722; decide +kernel
      have hl : raw18722step0Labels = raw18722Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18722 raw18722Labels permutation503 permutation3
    mixedMoment B raw18722step0 raw18722step0Labels = mixedMoment B raw18722step1 raw18722step1Labels := by
      have ha : raw18722step1 = -raw18722step0 := by apply Matrix.ext; change ∀ i j, raw18722step1 i j = -(raw18722step0 i j); unfold raw18722step1 raw18722step0; decide +kernel
      have hl : raw18722step1Labels = raw18722step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3442 node3442Labels := by rfl

def raw18723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18723step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18723 raw18723Labels = mixedMoment B node3445 node3445Labels := by
  calc
    mixedMoment B raw18723 raw18723Labels = mixedMoment B raw18723step0 raw18723step0Labels := by
      have ha : raw18723step0 = (fun i j => raw18723 (permutation502 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18723step0 raw18723; decide +kernel
      have hl : raw18723step0Labels = raw18723Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18723 raw18723Labels permutation502 permutation3
    mixedMoment B raw18723step0 raw18723step0Labels = mixedMoment B raw18723step1 raw18723step1Labels := by
      have ha : raw18723step1 = -raw18723step0 := by apply Matrix.ext; change ∀ i j, raw18723step1 i j = -(raw18723step0 i j); unfold raw18723step1 raw18723step0; decide +kernel
      have hl : raw18723step1Labels = raw18723step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3445 node3445Labels := by rfl

def raw18724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18724step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18724step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18724 raw18724Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw18724 raw18724Labels = mixedMoment B raw18724step0 raw18724step0Labels := by
      have hz : ∀ j, raw18724 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18724step0 = (fun i j => raw18724 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18724step0 raw18724; decide +kernel
      have hl : raw18724step0Labels = raw18724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18724 raw18724Labels permutation520 hz
    mixedMoment B raw18724step0 raw18724step0Labels = mixedMoment B raw18724step1 raw18724step1Labels := by
      have ha : raw18724step1 = (fun i j => raw18724step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18724step1 raw18724step0; decide +kernel
      have hl : raw18724step1Labels = raw18724step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18724step0 raw18724step0Labels permutation127 permutation3
    mixedMoment B raw18724step1 raw18724step1Labels = mixedMoment B raw18724step2 raw18724step2Labels := by
      have ha : raw18724step2 = -raw18724step1 := by apply Matrix.ext; change ∀ i j, raw18724step2 i j = -(raw18724step1 i j); unfold raw18724step2 raw18724step1; decide +kernel
      have hl : raw18724step2Labels = raw18724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw18725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18725step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18725step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18725 raw18725Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw18725 raw18725Labels = mixedMoment B raw18725step0 raw18725step0Labels := by
      have ha : raw18725step0 = (fun i j => raw18725 (permutation498 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18725step0 raw18725; decide +kernel
      have hl : raw18725step0Labels = raw18725Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18725 raw18725Labels permutation498 permutation3
    mixedMoment B raw18725step0 raw18725step0Labels = mixedMoment B raw18725step1 raw18725step1Labels := by
      have ha : raw18725step1 = -raw18725step0 := by apply Matrix.ext; change ∀ i j, raw18725step1 i j = -(raw18725step0 i j); unfold raw18725step1 raw18725step0; decide +kernel
      have hl : raw18725step1Labels = raw18725step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw18726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18726 raw18726Labels = mixedMoment B node2551 node2551Labels := by
  calc
    mixedMoment B raw18726 raw18726Labels = mixedMoment B raw18726step0 raw18726step0Labels := by
      have ha : raw18726step0 = (fun i j => raw18726 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18726step0 raw18726; decide +kernel
      have hl : raw18726step0Labels = raw18726Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18726 raw18726Labels permutation156 permutation3
    _ = mixedMoment B node2551 node2551Labels := by rfl

def raw18727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18727step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18727 raw18727Labels = mixedMoment B node3748 node3748Labels := by
  calc
    mixedMoment B raw18727 raw18727Labels = mixedMoment B raw18727step0 raw18727step0Labels := by
      have ha : raw18727step0 = (fun i j => raw18727 (permutation567 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18727step0 raw18727; decide +kernel
      have hl : raw18727step0Labels = raw18727Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18727 raw18727Labels permutation567 permutation3
    mixedMoment B raw18727step0 raw18727step0Labels = mixedMoment B raw18727step1 raw18727step1Labels := by
      have ha : raw18727step1 = -raw18727step0 := by apply Matrix.ext; change ∀ i j, raw18727step1 i j = -(raw18727step0 i j); unfold raw18727step1 raw18727step0; decide +kernel
      have hl : raw18727step1Labels = raw18727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3748 node3748Labels := by rfl

def raw18728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18728step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18728 raw18728Labels = mixedMoment B node3750 node3750Labels := by
  calc
    mixedMoment B raw18728 raw18728Labels = mixedMoment B raw18728step0 raw18728step0Labels := by
      have ha : raw18728step0 = (fun i j => raw18728 (permutation566 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18728step0 raw18728; decide +kernel
      have hl : raw18728step0Labels = raw18728Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18728 raw18728Labels permutation566 permutation3
    mixedMoment B raw18728step0 raw18728step0Labels = mixedMoment B raw18728step1 raw18728step1Labels := by
      have ha : raw18728step1 = -raw18728step0 := by apply Matrix.ext; change ∀ i j, raw18728step1 i j = -(raw18728step0 i j); unfold raw18728step1 raw18728step0; decide +kernel
      have hl : raw18728step1Labels = raw18728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3750 node3750Labels := by rfl

def raw18729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18729step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18729 raw18729Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw18729 raw18729Labels = mixedMoment B raw18729step0 raw18729step0Labels := by
      have ha : raw18729step0 = (fun i j => raw18729 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18729step0 raw18729; decide +kernel
      have hl : raw18729step0Labels = raw18729Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18729 raw18729Labels permutation589 permutation3
    mixedMoment B raw18729step0 raw18729step0Labels = mixedMoment B raw18729step1 raw18729step1Labels := by
      have ha : raw18729step1 = -raw18729step0 := by apply Matrix.ext; change ∀ i j, raw18729step1 i j = -(raw18729step0 i j); unfold raw18729step1 raw18729step0; decide +kernel
      have hl : raw18729step1Labels = raw18729step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw18730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw18730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18730step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18730 raw18730Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw18730 raw18730Labels = mixedMoment B raw18730step0 raw18730step0Labels := by
      have ha : raw18730step0 = (fun i j => raw18730 (permutation562 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18730step0 raw18730; decide +kernel
      have hl : raw18730step0Labels = raw18730Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18730 raw18730Labels permutation562 permutation3
    mixedMoment B raw18730step0 raw18730step0Labels = mixedMoment B raw18730step1 raw18730step1Labels := by
      have ha : raw18730step1 = -raw18730step0 := by apply Matrix.ext; change ∀ i j, raw18730step1 i j = -(raw18730step0 i j); unfold raw18730step1 raw18730step0; decide +kernel
      have hl : raw18730step1Labels = raw18730step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw18731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18731 raw18731Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw18731 raw18731Labels = mixedMoment B raw18731step0 raw18731step0Labels := by
      have ha : raw18731step0 = (fun i j => raw18731 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18731step0 raw18731; decide +kernel
      have hl : raw18731step0Labels = raw18731Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18731 raw18731Labels permutation154 permutation3
    _ = mixedMoment B node2557 node2557Labels := by rfl

def raw18732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18732 raw18732Labels = mixedMoment B node3922 node3922Labels := by
  calc
    mixedMoment B raw18732 raw18732Labels = mixedMoment B raw18732step0 raw18732step0Labels := by
      have ha : raw18732step0 = (fun i j => raw18732 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18732step0 raw18732; decide +kernel
      have hl : raw18732step0Labels = raw18732Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18732 raw18732Labels permutation154 permutation3
    _ = mixedMoment B node3922 node3922Labels := by rfl

def raw18733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18733Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18733step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18733 raw18733Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw18733 raw18733Labels = mixedMoment B raw18733step0 raw18733step0Labels := by
      have ha : raw18733step0 = (fun i j => raw18733 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18733step0 raw18733; decide +kernel
      have hl : raw18733step0Labels = raw18733Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18733 raw18733Labels permutation178 permutation3
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw18734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18734Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18734step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18734 raw18734Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw18734 raw18734Labels = mixedMoment B raw18734step0 raw18734step0Labels := by
      have ha : raw18734step0 = (fun i j => raw18734 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18734step0 raw18734; decide +kernel
      have hl : raw18734step0Labels = raw18734Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18734 raw18734Labels permutation152 permutation3
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw18735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18735Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18735step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18735step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18735 raw18735Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw18735 raw18735Labels = mixedMoment B raw18735step0 raw18735step0Labels := by
      have hz : ∀ j, raw18735 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18735step0 = (fun i j => raw18735 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18735step0 raw18735; decide +kernel
      have hl : raw18735step0Labels = raw18735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18735 raw18735Labels permutation520 hz
    mixedMoment B raw18735step0 raw18735step0Labels = mixedMoment B raw18735step1 raw18735step1Labels := by
      have ha : raw18735step1 = (fun i j => raw18735step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18735step1 raw18735step0; decide +kernel
      have hl : raw18735step1Labels = raw18735step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18735step0 raw18735step0Labels permutation32 permutation3
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw18736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18736step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18736 raw18736Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw18736 raw18736Labels = mixedMoment B raw18736step0 raw18736step0Labels := by
      have ha : raw18736step0 = (fun i j => raw18736 (permutation488 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18736step0 raw18736; decide +kernel
      have hl : raw18736step0Labels = raw18736Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18736 raw18736Labels permutation488 permutation5
    mixedMoment B raw18736step0 raw18736step0Labels = mixedMoment B raw18736step1 raw18736step1Labels := by
      have ha : raw18736step1 = raw18736step0 := by apply Matrix.ext; unfold raw18736step1 raw18736step0; decide +kernel
      have hl : raw18736step0Labels = labelEmbedding1 ∘ raw18736step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18736step0 raw18736step0Labels raw18736step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw18737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18737step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18737 raw18737Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw18737 raw18737Labels = mixedMoment B raw18737step0 raw18737step0Labels := by
      have ha : raw18737step0 = (fun i j => raw18737 (permutation485 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18737step0 raw18737; decide +kernel
      have hl : raw18737step0Labels = raw18737Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18737 raw18737Labels permutation485 permutation5
    mixedMoment B raw18737step0 raw18737step0Labels = mixedMoment B raw18737step1 raw18737step1Labels := by
      have ha : raw18737step1 = raw18737step0 := by apply Matrix.ext; unfold raw18737step1 raw18737step0; decide +kernel
      have hl : raw18737step0Labels = labelEmbedding1 ∘ raw18737step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18737step0 raw18737step0Labels raw18737step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3976 node3976Labels := by rfl

def raw18738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18738 raw18738Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw18738 raw18738Labels = mixedMoment B raw18738step0 raw18738step0Labels := by
      have hz : ∀ j, raw18738 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18738step0 = (fun i j => raw18738 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18738step0 raw18738; decide +kernel
      have hl : raw18738step0Labels = raw18738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18738 raw18738Labels permutation520 hz
    mixedMoment B raw18738step0 raw18738step0Labels = mixedMoment B raw18738step1 raw18738step1Labels := by
      have ha : raw18738step1 = (fun i j => raw18738step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18738step1 raw18738step0; decide +kernel
      have hl : raw18738step1Labels = raw18738step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18738step0 raw18738step0Labels permutation144 permutation7
    mixedMoment B raw18738step1 raw18738step1Labels = mixedMoment B raw18738step2 raw18738step2Labels := by
      have ha : raw18738step2 = raw18738step1 := by apply Matrix.ext; unfold raw18738step2 raw18738step1; decide +kernel
      have hl : raw18738step1Labels = labelEmbedding1 ∘ raw18738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18738step1 raw18738step1Labels raw18738step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw18739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18739 raw18739Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw18739 raw18739Labels = mixedMoment B raw18739step0 raw18739step0Labels := by
      have ha : raw18739step0 = (fun i j => raw18739 (permutation484 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18739step0 raw18739; decide +kernel
      have hl : raw18739step0Labels = raw18739Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18739 raw18739Labels permutation484 permutation5
    mixedMoment B raw18739step0 raw18739step0Labels = mixedMoment B raw18739step1 raw18739step1Labels := by
      have ha : raw18739step1 = raw18739step0 := by apply Matrix.ext; unfold raw18739step1 raw18739step0; decide +kernel
      have hl : raw18739step0Labels = labelEmbedding1 ∘ raw18739step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18739step0 raw18739step0Labels raw18739step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw18740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18740step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18740step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18740 raw18740Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw18740 raw18740Labels = mixedMoment B raw18740step0 raw18740step0Labels := by
      have ha : raw18740step0 = (fun i j => raw18740 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18740step0 raw18740; decide +kernel
      have hl : raw18740step0Labels = raw18740Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18740 raw18740Labels permutation195 permutation5
    mixedMoment B raw18740step0 raw18740step0Labels = mixedMoment B raw18740step1 raw18740step1Labels := by
      have ha : raw18740step1 = -raw18740step0 := by apply Matrix.ext; change ∀ i j, raw18740step1 i j = -(raw18740step0 i j); unfold raw18740step1 raw18740step0; decide +kernel
      have hl : raw18740step1Labels = raw18740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18740step1 raw18740step1Labels = mixedMoment B raw18740step2 raw18740step2Labels := by
      have ha : raw18740step2 = raw18740step1 := by apply Matrix.ext; unfold raw18740step2 raw18740step1; decide +kernel
      have hl : raw18740step1Labels = labelEmbedding1 ∘ raw18740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18740step1 raw18740step1Labels raw18740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3503 node3503Labels := by rfl

def raw18741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18741step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18741step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18741 raw18741Labels = mixedMoment B node3947 node3947Labels := by
  calc
    mixedMoment B raw18741 raw18741Labels = mixedMoment B raw18741step0 raw18741step0Labels := by
      have ha : raw18741step0 = (fun i j => raw18741 (permutation362 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18741step0 raw18741; decide +kernel
      have hl : raw18741step0Labels = raw18741Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18741 raw18741Labels permutation362 permutation5
    mixedMoment B raw18741step0 raw18741step0Labels = mixedMoment B raw18741step1 raw18741step1Labels := by
      have ha : raw18741step1 = -raw18741step0 := by apply Matrix.ext; change ∀ i j, raw18741step1 i j = -(raw18741step0 i j); unfold raw18741step1 raw18741step0; decide +kernel
      have hl : raw18741step1Labels = raw18741step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18741step1 raw18741step1Labels = mixedMoment B raw18741step2 raw18741step2Labels := by
      have ha : raw18741step2 = raw18741step1 := by apply Matrix.ext; unfold raw18741step2 raw18741step1; decide +kernel
      have hl : raw18741step1Labels = labelEmbedding1 ∘ raw18741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18741step1 raw18741step1Labels raw18741step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3947 node3947Labels := by rfl

def raw18742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18742step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18742 raw18742Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw18742 raw18742Labels = mixedMoment B raw18742step0 raw18742step0Labels := by
      have hz : ∀ j, raw18742 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18742step0 = (fun i j => raw18742 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18742step0 raw18742; decide +kernel
      have hl : raw18742step0Labels = raw18742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18742 raw18742Labels permutation520 hz
    mixedMoment B raw18742step0 raw18742step0Labels = mixedMoment B raw18742step1 raw18742step1Labels := by
      have ha : raw18742step1 = (fun i j => raw18742step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18742step1 raw18742step0; decide +kernel
      have hl : raw18742step1Labels = raw18742step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18742step0 raw18742step0Labels permutation115 permutation5
    mixedMoment B raw18742step1 raw18742step1Labels = mixedMoment B raw18742step2 raw18742step2Labels := by
      have ha : raw18742step2 = raw18742step1 := by apply Matrix.ext; unfold raw18742step2 raw18742step1; decide +kernel
      have hl : raw18742step1Labels = labelEmbedding1 ∘ raw18742step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18742step1 raw18742step1Labels raw18742step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw18743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18743 raw18743Labels = mixedMoment B node3966 node3966Labels := by
  calc
    mixedMoment B raw18743 raw18743Labels = mixedMoment B raw18743step0 raw18743step0Labels := by
      have ha : raw18743step0 = (fun i j => raw18743 (permutation491 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18743step0 raw18743; decide +kernel
      have hl : raw18743step0Labels = raw18743Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18743 raw18743Labels permutation491 permutation5
    mixedMoment B raw18743step0 raw18743step0Labels = mixedMoment B raw18743step1 raw18743step1Labels := by
      have ha : raw18743step1 = raw18743step0 := by apply Matrix.ext; unfold raw18743step1 raw18743step0; decide +kernel
      have hl : raw18743step0Labels = labelEmbedding1 ∘ raw18743step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18743step0 raw18743step0Labels raw18743step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3966 node3966Labels := by rfl

def raw18744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18744step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18744 raw18744Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw18744 raw18744Labels = mixedMoment B raw18744step0 raw18744step0Labels := by
      have ha : raw18744step0 = (fun i j => raw18744 (permutation247 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18744step0 raw18744; decide +kernel
      have hl : raw18744step0Labels = raw18744Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18744 raw18744Labels permutation247 permutation5
    mixedMoment B raw18744step0 raw18744step0Labels = mixedMoment B raw18744step1 raw18744step1Labels := by
      have ha : raw18744step1 = -raw18744step0 := by apply Matrix.ext; change ∀ i j, raw18744step1 i j = -(raw18744step0 i j); unfold raw18744step1 raw18744step0; decide +kernel
      have hl : raw18744step1Labels = raw18744step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18744step1 raw18744step1Labels = mixedMoment B raw18744step2 raw18744step2Labels := by
      have ha : raw18744step2 = raw18744step1 := by apply Matrix.ext; unfold raw18744step2 raw18744step1; decide +kernel
      have hl : raw18744step1Labels = labelEmbedding1 ∘ raw18744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18744step1 raw18744step1Labels raw18744step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw18745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18745 raw18745Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw18745 raw18745Labels = mixedMoment B raw18745step0 raw18745step0Labels := by
      have ha : raw18745step0 = (fun i j => raw18745 (permutation497 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18745step0 raw18745; decide +kernel
      have hl : raw18745step0Labels = raw18745Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18745 raw18745Labels permutation497 permutation5
    mixedMoment B raw18745step0 raw18745step0Labels = mixedMoment B raw18745step1 raw18745step1Labels := by
      have ha : raw18745step1 = raw18745step0 := by apply Matrix.ext; unfold raw18745step1 raw18745step0; decide +kernel
      have hl : raw18745step0Labels = labelEmbedding1 ∘ raw18745step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18745step0 raw18745step0Labels raw18745step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3973 node3973Labels := by rfl

def raw18746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18746step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18746step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18746step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18746step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18746 raw18746Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw18746 raw18746Labels = mixedMoment B raw18746step0 raw18746step0Labels := by
      have hz : ∀ j, raw18746 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18746step0 = (fun i j => raw18746 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18746step0 raw18746; decide +kernel
      have hl : raw18746step0Labels = raw18746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18746 raw18746Labels permutation520 hz
    mixedMoment B raw18746step0 raw18746step0Labels = mixedMoment B raw18746step1 raw18746step1Labels := by
      have ha : raw18746step1 = (fun i j => raw18746step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18746step1 raw18746step0; decide +kernel
      have hl : raw18746step1Labels = raw18746step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18746step0 raw18746step0Labels permutation145 permutation7
    mixedMoment B raw18746step1 raw18746step1Labels = mixedMoment B raw18746step2 raw18746step2Labels := by
      have ha : raw18746step2 = raw18746step1 := by apply Matrix.ext; unfold raw18746step2 raw18746step1; decide +kernel
      have hl : raw18746step1Labels = labelEmbedding1 ∘ raw18746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18746step1 raw18746step1Labels raw18746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw18747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18747step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18747step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18747step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18747 raw18747Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw18747 raw18747Labels = mixedMoment B raw18747step0 raw18747step0Labels := by
      have ha : raw18747step0 = (fun i j => raw18747 (permutation496 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18747step0 raw18747; decide +kernel
      have hl : raw18747step0Labels = raw18747Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18747 raw18747Labels permutation496 permutation5
    mixedMoment B raw18747step0 raw18747step0Labels = mixedMoment B raw18747step1 raw18747step1Labels := by
      have ha : raw18747step1 = raw18747step0 := by apply Matrix.ext; unfold raw18747step1 raw18747step0; decide +kernel
      have hl : raw18747step0Labels = labelEmbedding1 ∘ raw18747step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18747step0 raw18747step0Labels raw18747step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw18748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18748step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18748 raw18748Labels = mixedMoment B node2476 node2476Labels := by
  calc
    mixedMoment B raw18748 raw18748Labels = mixedMoment B raw18748step0 raw18748step0Labels := by
      have ha : raw18748step0 = (fun i j => raw18748 (permutation494 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18748step0 raw18748; decide +kernel
      have hl : raw18748step0Labels = raw18748Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18748 raw18748Labels permutation494 permutation5
    mixedMoment B raw18748step0 raw18748step0Labels = mixedMoment B raw18748step1 raw18748step1Labels := by
      have ha : raw18748step1 = raw18748step0 := by apply Matrix.ext; unfold raw18748step1 raw18748step0; decide +kernel
      have hl : raw18748step0Labels = labelEmbedding1 ∘ raw18748step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18748step0 raw18748step0Labels raw18748step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2476 node2476Labels := by rfl

def raw18749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18749step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18749 raw18749Labels = mixedMoment B node2501 node2501Labels := by
  calc
    mixedMoment B raw18749 raw18749Labels = mixedMoment B raw18749step0 raw18749step0Labels := by
      have ha : raw18749step0 = (fun i j => raw18749 (permutation503 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18749step0 raw18749; decide +kernel
      have hl : raw18749step0Labels = raw18749Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18749 raw18749Labels permutation503 permutation5
    mixedMoment B raw18749step0 raw18749step0Labels = mixedMoment B raw18749step1 raw18749step1Labels := by
      have ha : raw18749step1 = raw18749step0 := by apply Matrix.ext; unfold raw18749step1 raw18749step0; decide +kernel
      have hl : raw18749step0Labels = labelEmbedding1 ∘ raw18749step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18749step0 raw18749step0Labels raw18749step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2501 node2501Labels := by rfl

def raw18750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18750step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18750step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18750 raw18750Labels = mixedMoment B node2478 node2478Labels := by
  calc
    mixedMoment B raw18750 raw18750Labels = mixedMoment B raw18750step0 raw18750step0Labels := by
      have ha : raw18750step0 = (fun i j => raw18750 (permutation493 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18750step0 raw18750; decide +kernel
      have hl : raw18750step0Labels = raw18750Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18750 raw18750Labels permutation493 permutation5
    mixedMoment B raw18750step0 raw18750step0Labels = mixedMoment B raw18750step1 raw18750step1Labels := by
      have ha : raw18750step1 = raw18750step0 := by apply Matrix.ext; unfold raw18750step1 raw18750step0; decide +kernel
      have hl : raw18750step0Labels = labelEmbedding1 ∘ raw18750step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18750step0 raw18750step0Labels raw18750step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2478 node2478Labels := by rfl

def raw18751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18751 raw18751Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw18751 raw18751Labels = mixedMoment B raw18751step0 raw18751step0Labels := by
      have hz : ∀ j, raw18751 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18751step0 = (fun i j => raw18751 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18751step0 raw18751; decide +kernel
      have hl : raw18751step0Labels = raw18751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18751 raw18751Labels permutation520 hz
    mixedMoment B raw18751step0 raw18751step0Labels = mixedMoment B raw18751step1 raw18751step1Labels := by
      have ha : raw18751step1 = (fun i j => raw18751step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18751step1 raw18751step0; decide +kernel
      have hl : raw18751step1Labels = raw18751step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18751step0 raw18751step0Labels permutation115 permutation5
    mixedMoment B raw18751step1 raw18751step1Labels = mixedMoment B raw18751step2 raw18751step2Labels := by
      have ha : raw18751step2 = raw18751step1 := by apply Matrix.ext; unfold raw18751step2 raw18751step1; decide +kernel
      have hl : raw18751step1Labels = labelEmbedding1 ∘ raw18751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18751step1 raw18751step1Labels raw18751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw18752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18752step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18752step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18752step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18752step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18752 raw18752Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw18752 raw18752Labels = mixedMoment B raw18752step0 raw18752step0Labels := by
      have ha : raw18752step0 = (fun i j => raw18752 (permutation491 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18752step0 raw18752; decide +kernel
      have hl : raw18752step0Labels = raw18752Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18752 raw18752Labels permutation491 permutation5
    mixedMoment B raw18752step0 raw18752step0Labels = mixedMoment B raw18752step1 raw18752step1Labels := by
      have ha : raw18752step1 = raw18752step0 := by apply Matrix.ext; unfold raw18752step1 raw18752step0; decide +kernel
      have hl : raw18752step0Labels = labelEmbedding1 ∘ raw18752step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18752step0 raw18752step0Labels raw18752step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw18753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw18753step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18753step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw18753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18753 raw18753Labels = mixedMoment B node3499 node3499Labels := by
  calc
    mixedMoment B raw18753 raw18753Labels = mixedMoment B raw18753step0 raw18753step0Labels := by
      have ha : raw18753step0 = (fun i j => raw18753 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18753step0 raw18753; decide +kernel
      have hl : raw18753step0Labels = raw18753Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18753 raw18753Labels permutation194 permutation5
    mixedMoment B raw18753step0 raw18753step0Labels = mixedMoment B raw18753step1 raw18753step1Labels := by
      have ha : raw18753step1 = -raw18753step0 := by apply Matrix.ext; change ∀ i j, raw18753step1 i j = -(raw18753step0 i j); unfold raw18753step1 raw18753step0; decide +kernel
      have hl : raw18753step1Labels = raw18753step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18753step1 raw18753step1Labels = mixedMoment B raw18753step2 raw18753step2Labels := by
      have ha : raw18753step2 = raw18753step1 := by apply Matrix.ext; unfold raw18753step2 raw18753step1; decide +kernel
      have hl : raw18753step1Labels = labelEmbedding1 ∘ raw18753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18753step1 raw18753step1Labels raw18753step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3499 node3499Labels := by rfl

def raw18754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw18754step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18754 raw18754Labels = mixedMoment B node3700 node3700Labels := by
  calc
    mixedMoment B raw18754 raw18754Labels = mixedMoment B raw18754step0 raw18754step0Labels := by
      have ha : raw18754step0 = (fun i j => raw18754 (permutation567 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18754step0 raw18754; decide +kernel
      have hl : raw18754step0Labels = raw18754Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18754 raw18754Labels permutation567 permutation5
    mixedMoment B raw18754step0 raw18754step0Labels = mixedMoment B raw18754step1 raw18754step1Labels := by
      have ha : raw18754step1 = raw18754step0 := by apply Matrix.ext; unfold raw18754step1 raw18754step0; decide +kernel
      have hl : raw18754step0Labels = labelEmbedding1 ∘ raw18754step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18754step0 raw18754step0Labels raw18754step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3700 node3700Labels := by rfl

def raw18755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18755step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18755step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18755 raw18755Labels = mixedMoment B node3688 node3688Labels := by
  calc
    mixedMoment B raw18755 raw18755Labels = mixedMoment B raw18755step0 raw18755step0Labels := by
      have ha : raw18755step0 = (fun i j => raw18755 (permutation558 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18755step0 raw18755; decide +kernel
      have hl : raw18755step0Labels = raw18755Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18755 raw18755Labels permutation558 permutation5
    mixedMoment B raw18755step0 raw18755step0Labels = mixedMoment B raw18755step1 raw18755step1Labels := by
      have ha : raw18755step1 = raw18755step0 := by apply Matrix.ext; unfold raw18755step1 raw18755step0; decide +kernel
      have hl : raw18755step0Labels = labelEmbedding1 ∘ raw18755step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18755step0 raw18755step0Labels raw18755step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3688 node3688Labels := by rfl

def raw18756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw18756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18756step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18756step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18756 raw18756Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw18756 raw18756Labels = mixedMoment B raw18756step0 raw18756step0Labels := by
      have ha : raw18756step0 = (fun i j => raw18756 (permutation556 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18756step0 raw18756; decide +kernel
      have hl : raw18756step0Labels = raw18756Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18756 raw18756Labels permutation556 permutation5
    mixedMoment B raw18756step0 raw18756step0Labels = mixedMoment B raw18756step1 raw18756step1Labels := by
      have ha : raw18756step1 = raw18756step0 := by apply Matrix.ext; unfold raw18756step1 raw18756step0; decide +kernel
      have hl : raw18756step0Labels = labelEmbedding1 ∘ raw18756step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18756step0 raw18756step0Labels raw18756step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3691 node3691Labels := by rfl

def raw18757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18757step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18757step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18757 raw18757Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw18757 raw18757Labels = mixedMoment B raw18757step0 raw18757step0Labels := by
      have ha : raw18757step0 = (fun i j => raw18757 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18757step0 raw18757; decide +kernel
      have hl : raw18757step0Labels = raw18757Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18757 raw18757Labels permutation646 permutation7
    mixedMoment B raw18757step0 raw18757step0Labels = mixedMoment B raw18757step1 raw18757step1Labels := by
      have ha : raw18757step1 = raw18757step0 := by apply Matrix.ext; unfold raw18757step1 raw18757step0; decide +kernel
      have hl : raw18757step0Labels = labelEmbedding1 ∘ raw18757step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18757step0 raw18757step0Labels raw18757step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw18758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18758 raw18758Labels = mixedMoment B node3978 node3978Labels := by
  calc
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw18759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18759 raw18759Labels = mixedMoment B node3084 node3084Labels := by
  calc
    _ = mixedMoment B node3084 node3084Labels := by rfl

def raw18760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18760 raw18760Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw18760 raw18760Labels = mixedMoment B raw18760step0 raw18760step0Labels := by
      have ha : raw18760step0 = (fun i j => raw18760 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18760step0 raw18760; decide +kernel
      have hl : raw18760step0Labels = raw18760Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18760 raw18760Labels permutation160 permutation2
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw18761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw18761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18761 raw18761Labels = mixedMoment B node2938 node2938Labels := by
  calc
    mixedMoment B raw18761 raw18761Labels = mixedMoment B raw18761step0 raw18761step0Labels := by
      have ha : raw18761step0 = (fun i j => raw18761 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18761step0 raw18761; decide +kernel
      have hl : raw18761step0Labels = raw18761Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18761 raw18761Labels permutation155 permutation2
    _ = mixedMoment B node2938 node2938Labels := by rfl

def raw18762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18762 raw18762Labels = mixedMoment B node2935 node2935Labels := by
  calc
    mixedMoment B raw18762 raw18762Labels = mixedMoment B raw18762step0 raw18762step0Labels := by
      have ha : raw18762step0 = (fun i j => raw18762 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18762step0 raw18762; decide +kernel
      have hl : raw18762step0Labels = raw18762Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18762 raw18762Labels permutation153 permutation2
    _ = mixedMoment B node2935 node2935Labels := by rfl

def raw18763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18763 raw18763Labels = mixedMoment B node2933 node2933Labels := by
  calc
    _ = mixedMoment B node2933 node2933Labels := by rfl

def raw18764 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]
def raw18764Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18764step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw18764step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18764step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw18764step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw18764step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw18764step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical18764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18764 raw18764Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw18764 raw18764Labels = mixedMoment B raw18764step0 raw18764step0Labels := by
      have hz : ∀ j, raw18764 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18764step0 = (fun i j => raw18764 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18764step0 raw18764; decide +kernel
      have hl : raw18764step0Labels = raw18764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18764 raw18764Labels permutation520 hz
    mixedMoment B raw18764step0 raw18764step0Labels = mixedMoment B raw18764step1 raw18764step1Labels := by
      have ha : raw18764step1 = (fun i j => raw18764step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw18764step1 raw18764step0; decide +kernel
      have hl : raw18764step1Labels = raw18764step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18764step0 raw18764step0Labels permutation140 permutation0
    mixedMoment B raw18764step1 raw18764step1Labels = mixedMoment B raw18764step2 raw18764step2Labels := by
      have ha : raw18764step2 = -raw18764step1 := by apply Matrix.ext; change ∀ i j, raw18764step2 i j = -(raw18764step1 i j); unfold raw18764step2 raw18764step1; decide +kernel
      have hl : raw18764step2Labels = raw18764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw18765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18765 raw18765Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18765 raw18765Labels = mixedMoment B raw18765step0 raw18765step0Labels := by
      have ha : raw18765step0 = (fun i j => raw18765 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18765step0 raw18765; decide +kernel
      have hl : raw18765step0Labels = raw18765Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18765 raw18765Labels permutation265 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw18766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18766step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18766step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18766step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18766step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18766 raw18766Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw18766 raw18766Labels = mixedMoment B raw18766step0 raw18766step0Labels := by
      have ha : raw18766step0 = (fun i j => raw18766 (permutation350 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18766step0 raw18766; decide +kernel
      have hl : raw18766step0Labels = raw18766Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18766 raw18766Labels permutation350 permutation5
    mixedMoment B raw18766step0 raw18766step0Labels = mixedMoment B raw18766step1 raw18766step1Labels := by
      have ha : raw18766step1 = -raw18766step0 := by apply Matrix.ext; change ∀ i j, raw18766step1 i j = -(raw18766step0 i j); unfold raw18766step1 raw18766step0; decide +kernel
      have hl : raw18766step1Labels = raw18766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18766step1 raw18766step1Labels = mixedMoment B raw18766step2 raw18766step2Labels := by
      have ha : raw18766step2 = raw18766step1 := by apply Matrix.ext; unfold raw18766step2 raw18766step1; decide +kernel
      have hl : raw18766step1Labels = labelEmbedding8 ∘ raw18766step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18766step1 raw18766step1Labels raw18766step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw18767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18767 raw18767Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw18767 raw18767Labels = mixedMoment B raw18767step0 raw18767step0Labels := by
      have hz : ∀ j, raw18767 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18767step0 = (fun i j => raw18767 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18767step0 raw18767; decide +kernel
      have hl : raw18767step0Labels = raw18767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18767 raw18767Labels permutation434 hz
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw18768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18768 raw18768Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw18768 raw18768Labels = mixedMoment B raw18768step0 raw18768step0Labels := by
      have hz : ∀ j, raw18768 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18768step0 = (fun i j => raw18768 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18768step0 raw18768; decide +kernel
      have hl : raw18768step0Labels = raw18768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18768 raw18768Labels permutation520 hz
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw18769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18769step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18769 raw18769Labels = mixedMoment B node5498 node5498Labels := by
  calc
    mixedMoment B raw18769 raw18769Labels = mixedMoment B raw18769step0 raw18769step0Labels := by
      have ha : raw18769step0 = (fun i j => raw18769 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18769step0 raw18769; decide +kernel
      have hl : raw18769step0Labels = raw18769Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18769 raw18769Labels permutation156 permutation2
    _ = mixedMoment B node5498 node5498Labels := by rfl

def raw18770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18770step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18770step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18770step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18770 raw18770Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw18770 raw18770Labels = mixedMoment B raw18770step0 raw18770step0Labels := by
      have ha : raw18770step0 = (fun i j => raw18770 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18770step0 raw18770; decide +kernel
      have hl : raw18770step0Labels = raw18770Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18770 raw18770Labels permutation180 permutation3
    mixedMoment B raw18770step0 raw18770step0Labels = mixedMoment B raw18770step1 raw18770step1Labels := by
      have ha : raw18770step1 = raw18770step0 := by apply Matrix.ext; unfold raw18770step1 raw18770step0; decide +kernel
      have hl : raw18770step0Labels = labelEmbedding6 ∘ raw18770step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18770step0 raw18770step0Labels raw18770step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw18771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18771 raw18771Labels = mixedMoment B node5464 node5464Labels := by
  calc
    mixedMoment B raw18771 raw18771Labels = mixedMoment B raw18771step0 raw18771step0Labels := by
      have ha : raw18771step0 = (fun i j => raw18771 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18771step0 raw18771; decide +kernel
      have hl : raw18771step0Labels = raw18771Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18771 raw18771Labels permutation160 permutation2
    _ = mixedMoment B node5464 node5464Labels := by rfl

def raw18772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18772 raw18772Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw18772 raw18772Labels = mixedMoment B raw18772step0 raw18772step0Labels := by
      have hz : ∀ j, raw18772 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18772step0 = (fun i j => raw18772 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18772step0 raw18772; decide +kernel
      have hl : raw18772step0Labels = raw18772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18772 raw18772Labels permutation434 hz
    mixedMoment B raw18772step0 raw18772step0Labels = mixedMoment B raw18772step1 raw18772step1Labels := by
      have ha : raw18772step1 = (fun i j => raw18772step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18772step1 raw18772step0; decide +kernel
      have hl : raw18772step1Labels = raw18772step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18772step0 raw18772step0Labels permutation34 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw18773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18773step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18773 raw18773Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw18773 raw18773Labels = mixedMoment B raw18773step0 raw18773step0Labels := by
      have hz : ∀ j, raw18773 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18773step0 = (fun i j => raw18773 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18773step0 raw18773; decide +kernel
      have hl : raw18773step0Labels = raw18773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18773 raw18773Labels permutation520 hz
    mixedMoment B raw18773step0 raw18773step0Labels = mixedMoment B raw18773step1 raw18773step1Labels := by
      have ha : raw18773step1 = (fun i j => raw18773step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18773step1 raw18773step0; decide +kernel
      have hl : raw18773step1Labels = raw18773step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18773step0 raw18773step0Labels permutation34 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw18774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18774 raw18774Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw18774 raw18774Labels = mixedMoment B raw18774step0 raw18774step0Labels := by
      have ha : raw18774step0 = (fun i j => raw18774 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18774step0 raw18774; decide +kernel
      have hl : raw18774step0Labels = raw18774Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18774 raw18774Labels permutation173 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw18775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18775step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18775step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18775step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18775step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18775 raw18775Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw18775 raw18775Labels = mixedMoment B raw18775step0 raw18775step0Labels := by
      have ha : raw18775step0 = (fun i j => raw18775 (permutation503 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18775step0 raw18775; decide +kernel
      have hl : raw18775step0Labels = raw18775Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18775 raw18775Labels permutation503 permutation3
    mixedMoment B raw18775step0 raw18775step0Labels = mixedMoment B raw18775step1 raw18775step1Labels := by
      have ha : raw18775step1 = -raw18775step0 := by apply Matrix.ext; change ∀ i j, raw18775step1 i j = -(raw18775step0 i j); unfold raw18775step1 raw18775step0; decide +kernel
      have hl : raw18775step1Labels = raw18775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18775step1 raw18775step1Labels = mixedMoment B raw18775step2 raw18775step2Labels := by
      have ha : raw18775step2 = raw18775step1 := by apply Matrix.ext; unfold raw18775step2 raw18775step1; decide +kernel
      have hl : raw18775step1Labels = labelEmbedding6 ∘ raw18775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18775step1 raw18775step1Labels raw18775step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw18776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18776step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18776step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18776step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18776step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18776 raw18776Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw18776 raw18776Labels = mixedMoment B raw18776step0 raw18776step0Labels := by
      have ha : raw18776step0 = (fun i j => raw18776 (permutation502 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18776step0 raw18776; decide +kernel
      have hl : raw18776step0Labels = raw18776Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18776 raw18776Labels permutation502 permutation3
    mixedMoment B raw18776step0 raw18776step0Labels = mixedMoment B raw18776step1 raw18776step1Labels := by
      have ha : raw18776step1 = -raw18776step0 := by apply Matrix.ext; change ∀ i j, raw18776step1 i j = -(raw18776step0 i j); unfold raw18776step1 raw18776step0; decide +kernel
      have hl : raw18776step1Labels = raw18776step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18776step1 raw18776step1Labels = mixedMoment B raw18776step2 raw18776step2Labels := by
      have ha : raw18776step2 = raw18776step1 := by apply Matrix.ext; unfold raw18776step2 raw18776step1; decide +kernel
      have hl : raw18776step1Labels = labelEmbedding6 ∘ raw18776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18776step1 raw18776step1Labels raw18776step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw18777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw18777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw18777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18777step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18777step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18777step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18777step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18777 raw18777Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18777 raw18777Labels = mixedMoment B raw18777step0 raw18777step0Labels := by
      have hz : ∀ j, raw18777 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18777step0 = (fun i j => raw18777 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18777step0 raw18777; decide +kernel
      have hl : raw18777step0Labels = raw18777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18777 raw18777Labels permutation520 hz
    mixedMoment B raw18777step0 raw18777step0Labels = mixedMoment B raw18777step1 raw18777step1Labels := by
      have ha : raw18777step1 = (fun i j => raw18777step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18777step1 raw18777step0; decide +kernel
      have hl : raw18777step1Labels = raw18777step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18777step0 raw18777step0Labels permutation127 permutation3
    mixedMoment B raw18777step1 raw18777step1Labels = mixedMoment B raw18777step2 raw18777step2Labels := by
      have ha : raw18777step2 = -raw18777step1 := by apply Matrix.ext; change ∀ i j, raw18777step2 i j = -(raw18777step1 i j); unfold raw18777step2 raw18777step1; decide +kernel
      have hl : raw18777step2Labels = raw18777step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18777step2 raw18777step2Labels = mixedMoment B raw18777step3 raw18777step3Labels := by
      have ha : raw18777step3 = raw18777step2 := by apply Matrix.ext; unfold raw18777step3 raw18777step2; decide +kernel
      have hl : raw18777step2Labels = labelEmbedding6 ∘ raw18777step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18777step2 raw18777step2Labels raw18777step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw18778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw18778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18778step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18778step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18778step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18778step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18778 raw18778Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw18778 raw18778Labels = mixedMoment B raw18778step0 raw18778step0Labels := by
      have ha : raw18778step0 = (fun i j => raw18778 (permutation498 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18778step0 raw18778; decide +kernel
      have hl : raw18778step0Labels = raw18778Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18778 raw18778Labels permutation498 permutation3
    mixedMoment B raw18778step0 raw18778step0Labels = mixedMoment B raw18778step1 raw18778step1Labels := by
      have ha : raw18778step1 = -raw18778step0 := by apply Matrix.ext; change ∀ i j, raw18778step1 i j = -(raw18778step0 i j); unfold raw18778step1 raw18778step0; decide +kernel
      have hl : raw18778step1Labels = raw18778step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18778step1 raw18778step1Labels = mixedMoment B raw18778step2 raw18778step2Labels := by
      have ha : raw18778step2 = raw18778step1 := by apply Matrix.ext; unfold raw18778step2 raw18778step1; decide +kernel
      have hl : raw18778step1Labels = labelEmbedding6 ∘ raw18778step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18778step1 raw18778step1Labels raw18778step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw18779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw18779step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18779step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw18779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18779 raw18779Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw18779 raw18779Labels = mixedMoment B raw18779step0 raw18779step0Labels := by
      have ha : raw18779step0 = (fun i j => raw18779 (permutation567 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18779step0 raw18779; decide +kernel
      have hl : raw18779step0Labels = raw18779Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18779 raw18779Labels permutation567 permutation3
    mixedMoment B raw18779step0 raw18779step0Labels = mixedMoment B raw18779step1 raw18779step1Labels := by
      have ha : raw18779step1 = -raw18779step0 := by apply Matrix.ext; change ∀ i j, raw18779step1 i j = -(raw18779step0 i j); unfold raw18779step1 raw18779step0; decide +kernel
      have hl : raw18779step1Labels = raw18779step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18779step1 raw18779step1Labels = mixedMoment B raw18779step2 raw18779step2Labels := by
      have ha : raw18779step2 = raw18779step1 := by apply Matrix.ext; unfold raw18779step2 raw18779step1; decide +kernel
      have hl : raw18779step1Labels = labelEmbedding6 ∘ raw18779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18779step1 raw18779step1Labels raw18779step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw18780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw18780step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18780step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18780step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw18780step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18780 raw18780Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw18780 raw18780Labels = mixedMoment B raw18780step0 raw18780step0Labels := by
      have ha : raw18780step0 = (fun i j => raw18780 (permutation566 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18780step0 raw18780; decide +kernel
      have hl : raw18780step0Labels = raw18780Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18780 raw18780Labels permutation566 permutation3
    mixedMoment B raw18780step0 raw18780step0Labels = mixedMoment B raw18780step1 raw18780step1Labels := by
      have ha : raw18780step1 = -raw18780step0 := by apply Matrix.ext; change ∀ i j, raw18780step1 i j = -(raw18780step0 i j); unfold raw18780step1 raw18780step0; decide +kernel
      have hl : raw18780step1Labels = raw18780step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18780step1 raw18780step1Labels = mixedMoment B raw18780step2 raw18780step2Labels := by
      have ha : raw18780step2 = raw18780step1 := by apply Matrix.ext; unfold raw18780step2 raw18780step1; decide +kernel
      have hl : raw18780step1Labels = labelEmbedding6 ∘ raw18780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18780step1 raw18780step1Labels raw18780step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw18781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw18781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw18781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18781step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18781step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18781step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18781step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18781 raw18781Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18781 raw18781Labels = mixedMoment B raw18781step0 raw18781step0Labels := by
      have hz : ∀ j, raw18781 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18781step0 = (fun i j => raw18781 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18781step0 raw18781; decide +kernel
      have hl : raw18781step0Labels = raw18781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18781 raw18781Labels permutation434 hz
    mixedMoment B raw18781step0 raw18781step0Labels = mixedMoment B raw18781step1 raw18781step1Labels := by
      have ha : raw18781step1 = (fun i j => raw18781step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18781step1 raw18781step0; decide +kernel
      have hl : raw18781step1Labels = raw18781step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18781step0 raw18781step0Labels permutation127 permutation3
    mixedMoment B raw18781step1 raw18781step1Labels = mixedMoment B raw18781step2 raw18781step2Labels := by
      have ha : raw18781step2 = -raw18781step1 := by apply Matrix.ext; change ∀ i j, raw18781step2 i j = -(raw18781step1 i j); unfold raw18781step2 raw18781step1; decide +kernel
      have hl : raw18781step2Labels = raw18781step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18781step2 raw18781step2Labels = mixedMoment B raw18781step3 raw18781step3Labels := by
      have ha : raw18781step3 = raw18781step2 := by apply Matrix.ext; unfold raw18781step3 raw18781step2; decide +kernel
      have hl : raw18781step2Labels = labelEmbedding6 ∘ raw18781step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18781step2 raw18781step2Labels raw18781step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw18782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw18782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18782step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18782step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18782step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18782step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18782step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18782 raw18782Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw18782 raw18782Labels = mixedMoment B raw18782step0 raw18782step0Labels := by
      have ha : raw18782step0 = (fun i j => raw18782 (permutation562 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18782step0 raw18782; decide +kernel
      have hl : raw18782step0Labels = raw18782Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18782 raw18782Labels permutation562 permutation3
    mixedMoment B raw18782step0 raw18782step0Labels = mixedMoment B raw18782step1 raw18782step1Labels := by
      have ha : raw18782step1 = -raw18782step0 := by apply Matrix.ext; change ∀ i j, raw18782step1 i j = -(raw18782step0 i j); unfold raw18782step1 raw18782step0; decide +kernel
      have hl : raw18782step1Labels = raw18782step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18782step1 raw18782step1Labels = mixedMoment B raw18782step2 raw18782step2Labels := by
      have ha : raw18782step2 = raw18782step1 := by apply Matrix.ext; unfold raw18782step2 raw18782step1; decide +kernel
      have hl : raw18782step1Labels = labelEmbedding6 ∘ raw18782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18782step1 raw18782step1Labels raw18782step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw18783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18783step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18783step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18783step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18783step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18783 raw18783Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw18783 raw18783Labels = mixedMoment B raw18783step0 raw18783step0Labels := by
      have ha : raw18783step0 = (fun i j => raw18783 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18783step0 raw18783; decide +kernel
      have hl : raw18783step0Labels = raw18783Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18783 raw18783Labels permutation152 permutation3
    mixedMoment B raw18783step0 raw18783step0Labels = mixedMoment B raw18783step1 raw18783step1Labels := by
      have ha : raw18783step1 = raw18783step0 := by apply Matrix.ext; unfold raw18783step1 raw18783step0; decide +kernel
      have hl : raw18783step0Labels = labelEmbedding6 ∘ raw18783step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18783step0 raw18783step0Labels raw18783step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

def raw18784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18784step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18784 raw18784Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw18784 raw18784Labels = mixedMoment B raw18784step0 raw18784step0Labels := by
      have ha : raw18784step0 = (fun i j => raw18784 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18784step0 raw18784; decide +kernel
      have hl : raw18784step0Labels = raw18784Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18784 raw18784Labels permutation176 permutation3
    mixedMoment B raw18784step0 raw18784step0Labels = mixedMoment B raw18784step1 raw18784step1Labels := by
      have ha : raw18784step1 = raw18784step0 := by apply Matrix.ext; unfold raw18784step1 raw18784step0; decide +kernel
      have hl : raw18784step0Labels = labelEmbedding6 ∘ raw18784step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18784step0 raw18784step0Labels raw18784step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw18785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18785 raw18785Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw18785 raw18785Labels = mixedMoment B raw18785step0 raw18785step0Labels := by
      have hz : ∀ j, raw18785 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18785step0 = (fun i j => raw18785 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18785step0 raw18785; decide +kernel
      have hl : raw18785step0Labels = raw18785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18785 raw18785Labels permutation434 hz
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw18786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw18786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18786 raw18786Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw18786 raw18786Labels = mixedMoment B raw18786step0 raw18786step0Labels := by
      have hz : ∀ j, raw18786 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18786step0 = (fun i j => raw18786 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18786step0 raw18786; decide +kernel
      have hl : raw18786step0Labels = raw18786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18786 raw18786Labels permutation520 hz
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw18787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18787step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18787 raw18787Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18787 raw18787Labels = mixedMoment B raw18787step0 raw18787step0Labels := by
      have ha : raw18787step0 = (fun i j => raw18787 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18787step0 raw18787; decide +kernel
      have hl : raw18787step0Labels = raw18787Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18787 raw18787Labels permutation265 permutation3
    mixedMoment B raw18787step0 raw18787step0Labels = mixedMoment B raw18787step1 raw18787step1Labels := by
      have ha : raw18787step1 = raw18787step0 := by apply Matrix.ext; unfold raw18787step1 raw18787step0; decide +kernel
      have hl : raw18787step0Labels = labelEmbedding6 ∘ raw18787step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18787step0 raw18787step0Labels raw18787step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18788 raw18788Labels = mixedMoment B node5497 node5497Labels := by
  calc
    mixedMoment B raw18788 raw18788Labels = mixedMoment B raw18788step0 raw18788step0Labels := by
      have ha : raw18788step0 = (fun i j => raw18788 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18788step0 raw18788; decide +kernel
      have hl : raw18788step0Labels = raw18788Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18788 raw18788Labels permutation180 permutation2
    _ = mixedMoment B node5497 node5497Labels := by rfl

def raw18789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18789 raw18789Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw18789 raw18789Labels = mixedMoment B raw18789step0 raw18789step0Labels := by
      have ha : raw18789step0 = (fun i j => raw18789 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18789step0 raw18789; decide +kernel
      have hl : raw18789step0Labels = raw18789Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18789 raw18789Labels permutation155 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

def raw18790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18790step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18790step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18790 raw18790Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw18790 raw18790Labels = mixedMoment B raw18790step0 raw18790step0Labels := by
      have hz : ∀ j, raw18790 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18790step0 = (fun i j => raw18790 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18790step0 raw18790; decide +kernel
      have hl : raw18790step0Labels = raw18790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18790 raw18790Labels permutation590 hz
    mixedMoment B raw18790step0 raw18790step0Labels = mixedMoment B raw18790step1 raw18790step1Labels := by
      have ha : raw18790step1 = (fun i j => raw18790step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18790step1 raw18790step0; decide +kernel
      have hl : raw18790step1Labels = raw18790step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18790step0 raw18790step0Labels permutation127 permutation2
    mixedMoment B raw18790step1 raw18790step1Labels = mixedMoment B raw18790step2 raw18790step2Labels := by
      have ha : raw18790step2 = -raw18790step1 := by apply Matrix.ext; change ∀ i j, raw18790step2 i j = -(raw18790step1 i j); unfold raw18790step2 raw18790step1; decide +kernel
      have hl : raw18790step2Labels = raw18790step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw18791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18791step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18791 raw18791Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw18791 raw18791Labels = mixedMoment B raw18791step0 raw18791step0Labels := by
      have hz : ∀ j, raw18791 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18791step0 = (fun i j => raw18791 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18791step0 raw18791; decide +kernel
      have hl : raw18791step0Labels = raw18791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18791 raw18791Labels permutation265 hz
    mixedMoment B raw18791step0 raw18791step0Labels = mixedMoment B raw18791step1 raw18791step1Labels := by
      have ha : raw18791step1 = (fun i j => raw18791step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18791step1 raw18791step0; decide +kernel
      have hl : raw18791step1Labels = raw18791step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18791step0 raw18791step0Labels permutation32 permutation3
    mixedMoment B raw18791step1 raw18791step1Labels = mixedMoment B raw18791step2 raw18791step2Labels := by
      have ha : raw18791step2 = raw18791step1 := by apply Matrix.ext; unfold raw18791step2 raw18791step1; decide +kernel
      have hl : raw18791step1Labels = labelEmbedding6 ∘ raw18791step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18791step1 raw18791step1Labels raw18791step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw18792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18792step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18792 raw18792Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw18792 raw18792Labels = mixedMoment B raw18792step0 raw18792step0Labels := by
      have ha : raw18792step0 = (fun i j => raw18792 (permutation274 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18792step0 raw18792; decide +kernel
      have hl : raw18792step0Labels = raw18792Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18792 raw18792Labels permutation274 permutation3
    mixedMoment B raw18792step0 raw18792step0Labels = mixedMoment B raw18792step1 raw18792step1Labels := by
      have ha : raw18792step1 = raw18792step0 := by apply Matrix.ext; unfold raw18792step1 raw18792step0; decide +kernel
      have hl : raw18792step0Labels = labelEmbedding6 ∘ raw18792step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18792step0 raw18792step0Labels raw18792step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw18793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18793step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18793step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18793 raw18793Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw18793 raw18793Labels = mixedMoment B raw18793step0 raw18793step0Labels := by
      have ha : raw18793step0 = (fun i j => raw18793 (permutation167 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18793step0 raw18793; decide +kernel
      have hl : raw18793step0Labels = raw18793Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18793 raw18793Labels permutation167 permutation3
    mixedMoment B raw18793step0 raw18793step0Labels = mixedMoment B raw18793step1 raw18793step1Labels := by
      have ha : raw18793step1 = raw18793step0 := by apply Matrix.ext; unfold raw18793step1 raw18793step0; decide +kernel
      have hl : raw18793step0Labels = labelEmbedding6 ∘ raw18793step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18793step0 raw18793step0Labels raw18793step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw18794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18794step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18794step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18794 raw18794Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18794 raw18794Labels = mixedMoment B raw18794step0 raw18794step0Labels := by
      have hz : ∀ j, raw18794 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18794step0 = (fun i j => raw18794 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18794step0 raw18794; decide +kernel
      have hl : raw18794step0Labels = raw18794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18794 raw18794Labels permutation590 hz
    mixedMoment B raw18794step0 raw18794step0Labels = mixedMoment B raw18794step1 raw18794step1Labels := by
      have ha : raw18794step1 = (fun i j => raw18794step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18794step1 raw18794step0; decide +kernel
      have hl : raw18794step1Labels = raw18794step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18794step0 raw18794step0Labels permutation35 permutation3
    mixedMoment B raw18794step1 raw18794step1Labels = mixedMoment B raw18794step2 raw18794step2Labels := by
      have ha : raw18794step2 = raw18794step1 := by apply Matrix.ext; unfold raw18794step2 raw18794step1; decide +kernel
      have hl : raw18794step1Labels = labelEmbedding6 ∘ raw18794step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18794step1 raw18794step1Labels raw18794step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw18795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18795step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18795 raw18795Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw18795 raw18795Labels = mixedMoment B raw18795step0 raw18795step0Labels := by
      have ha : raw18795step0 = (fun i j => raw18795 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18795step0 raw18795; decide +kernel
      have hl : raw18795step0Labels = raw18795Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18795 raw18795Labels permutation268 permutation3
    mixedMoment B raw18795step0 raw18795step0Labels = mixedMoment B raw18795step1 raw18795step1Labels := by
      have ha : raw18795step1 = raw18795step0 := by apply Matrix.ext; unfold raw18795step1 raw18795step0; decide +kernel
      have hl : raw18795step0Labels = labelEmbedding6 ∘ raw18795step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18795step0 raw18795step0Labels raw18795step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw18796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18796step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18796 raw18796Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw18796 raw18796Labels = mixedMoment B raw18796step0 raw18796step0Labels := by
      have ha : raw18796step0 = (fun i j => raw18796 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18796step0 raw18796; decide +kernel
      have hl : raw18796step0Labels = raw18796Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18796 raw18796Labels permutation181 permutation2
    _ = mixedMoment B node5476 node5476Labels := by rfl

def raw18797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18797 raw18797Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw18797 raw18797Labels = mixedMoment B raw18797step0 raw18797step0Labels := by
      have ha : raw18797step0 = (fun i j => raw18797 (permutation165 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18797step0 raw18797; decide +kernel
      have hl : raw18797step0Labels = raw18797Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18797 raw18797Labels permutation165 permutation3
    mixedMoment B raw18797step0 raw18797step0Labels = mixedMoment B raw18797step1 raw18797step1Labels := by
      have ha : raw18797step1 = raw18797step0 := by apply Matrix.ext; unfold raw18797step1 raw18797step0; decide +kernel
      have hl : raw18797step0Labels = labelEmbedding6 ∘ raw18797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18797step0 raw18797step0Labels raw18797step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw18798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw18798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18798step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18798 raw18798Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw18798 raw18798Labels = mixedMoment B raw18798step0 raw18798step0Labels := by
      have hz : ∀ j, raw18798 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18798step0 = (fun i j => raw18798 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18798step0 raw18798; decide +kernel
      have hl : raw18798step0Labels = raw18798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18798 raw18798Labels permutation590 hz
    mixedMoment B raw18798step0 raw18798step0Labels = mixedMoment B raw18798step1 raw18798step1Labels := by
      have ha : raw18798step1 = (fun i j => raw18798step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18798step1 raw18798step0; decide +kernel
      have hl : raw18798step1Labels = raw18798step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18798step0 raw18798step0Labels permutation127 permutation2
    mixedMoment B raw18798step1 raw18798step1Labels = mixedMoment B raw18798step2 raw18798step2Labels := by
      have ha : raw18798step2 = -raw18798step1 := by apply Matrix.ext; change ∀ i j, raw18798step2 i j = -(raw18798step1 i j); unfold raw18798step2 raw18798step1; decide +kernel
      have hl : raw18798step2Labels = raw18798step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw18799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18799step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18799 raw18799Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw18799 raw18799Labels = mixedMoment B raw18799step0 raw18799step0Labels := by
      have ha : raw18799step0 = (fun i j => raw18799 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18799step0 raw18799; decide +kernel
      have hl : raw18799step0Labels = raw18799Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18799 raw18799Labels permutation266 permutation3
    mixedMoment B raw18799step0 raw18799step0Labels = mixedMoment B raw18799step1 raw18799step1Labels := by
      have ha : raw18799step1 = raw18799step0 := by apply Matrix.ext; unfold raw18799step1 raw18799step0; decide +kernel
      have hl : raw18799step0Labels = labelEmbedding6 ∘ raw18799step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18799step0 raw18799step0Labels raw18799step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw18800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18800 raw18800Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw18800 raw18800Labels = mixedMoment B raw18800step0 raw18800step0Labels := by
      have ha : raw18800step0 = (fun i j => raw18800 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18800step0 raw18800; decide +kernel
      have hl : raw18800step0Labels = raw18800Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18800 raw18800Labels permutation180 permutation2
    _ = mixedMoment B node5476 node5476Labels := by rfl

def raw18801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw18801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18801step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18801step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18801 raw18801Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw18801 raw18801Labels = mixedMoment B raw18801step0 raw18801step0Labels := by
      have hz : ∀ j, raw18801 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18801step0 = (fun i j => raw18801 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18801step0 raw18801; decide +kernel
      have hl : raw18801step0Labels = raw18801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18801 raw18801Labels permutation590 hz
    mixedMoment B raw18801step0 raw18801step0Labels = mixedMoment B raw18801step1 raw18801step1Labels := by
      have ha : raw18801step1 = (fun i j => raw18801step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18801step1 raw18801step0; decide +kernel
      have hl : raw18801step1Labels = raw18801step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18801step0 raw18801step0Labels permutation151 permutation2
    mixedMoment B raw18801step1 raw18801step1Labels = mixedMoment B raw18801step2 raw18801step2Labels := by
      have ha : raw18801step2 = -raw18801step1 := by apply Matrix.ext; change ∀ i j, raw18801step2 i j = -(raw18801step1 i j); unfold raw18801step2 raw18801step1; decide +kernel
      have hl : raw18801step2Labels = raw18801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw18802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18802step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18802step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18802step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18802 raw18802Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18802 raw18802Labels = mixedMoment B raw18802step0 raw18802step0Labels := by
      have ha : raw18802step0 = (fun i j => raw18802 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18802step0 raw18802; decide +kernel
      have hl : raw18802step0Labels = raw18802Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18802 raw18802Labels permutation682 permutation3
    mixedMoment B raw18802step0 raw18802step0Labels = mixedMoment B raw18802step1 raw18802step1Labels := by
      have ha : raw18802step1 = -raw18802step0 := by apply Matrix.ext; change ∀ i j, raw18802step1 i j = -(raw18802step0 i j); unfold raw18802step1 raw18802step0; decide +kernel
      have hl : raw18802step1Labels = raw18802step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18802step1 raw18802step1Labels = mixedMoment B raw18802step2 raw18802step2Labels := by
      have ha : raw18802step2 = raw18802step1 := by apply Matrix.ext; unfold raw18802step2 raw18802step1; decide +kernel
      have hl : raw18802step1Labels = labelEmbedding6 ∘ raw18802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18802step1 raw18802step1Labels raw18802step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18803step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18803step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18803 raw18803Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18803 raw18803Labels = mixedMoment B raw18803step0 raw18803step0Labels := by
      have ha : raw18803step0 = (fun i j => raw18803 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18803step0 raw18803; decide +kernel
      have hl : raw18803step0Labels = raw18803Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18803 raw18803Labels permutation269 permutation3
    mixedMoment B raw18803step0 raw18803step0Labels = mixedMoment B raw18803step1 raw18803step1Labels := by
      have ha : raw18803step1 = raw18803step0 := by apply Matrix.ext; unfold raw18803step1 raw18803step0; decide +kernel
      have hl : raw18803step0Labels = labelEmbedding6 ∘ raw18803step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18803step0 raw18803step0Labels raw18803step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw18804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18804step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18804step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18804 raw18804Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw18804 raw18804Labels = mixedMoment B raw18804step0 raw18804step0Labels := by
      have ha : raw18804step0 = (fun i j => raw18804 (permutation661 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18804step0 raw18804; decide +kernel
      have hl : raw18804step0Labels = raw18804Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18804 raw18804Labels permutation661 permutation7
    mixedMoment B raw18804step0 raw18804step0Labels = mixedMoment B raw18804step1 raw18804step1Labels := by
      have ha : raw18804step1 = raw18804step0 := by apply Matrix.ext; unfold raw18804step1 raw18804step0; decide +kernel
      have hl : raw18804step0Labels = labelEmbedding10 ∘ raw18804step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18804step0 raw18804step0Labels raw18804step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw18805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18805Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18805step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18805step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18805step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18805 raw18805Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18805 raw18805Labels = mixedMoment B raw18805step0 raw18805step0Labels := by
      have hz : ∀ j, raw18805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18805step0 = (fun i j => raw18805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18805step0 raw18805; decide +kernel
      have hl : raw18805step0Labels = raw18805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18805 raw18805Labels permutation434 hz
    mixedMoment B raw18805step0 raw18805step0Labels = mixedMoment B raw18805step1 raw18805step1Labels := by
      have ha : raw18805step1 = (fun i j => raw18805step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18805step1 raw18805step0; decide +kernel
      have hl : raw18805step1Labels = raw18805step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18805step0 raw18805step0Labels permutation138 permutation6
    mixedMoment B raw18805step1 raw18805step1Labels = mixedMoment B raw18805step2 raw18805step2Labels := by
      have ha : raw18805step2 = raw18805step1 := by apply Matrix.ext; unfold raw18805step2 raw18805step1; decide +kernel
      have hl : raw18805step1Labels = labelEmbedding9 ∘ raw18805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18805step1 raw18805step1Labels raw18805step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw18806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18806Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18806step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18806step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18806step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18806 raw18806Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18806 raw18806Labels = mixedMoment B raw18806step0 raw18806step0Labels := by
      have hz : ∀ j, raw18806 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18806step0 = (fun i j => raw18806 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18806step0 raw18806; decide +kernel
      have hl : raw18806step0Labels = raw18806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18806 raw18806Labels permutation520 hz
    mixedMoment B raw18806step0 raw18806step0Labels = mixedMoment B raw18806step1 raw18806step1Labels := by
      have ha : raw18806step1 = (fun i j => raw18806step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18806step1 raw18806step0; decide +kernel
      have hl : raw18806step1Labels = raw18806step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18806step0 raw18806step0Labels permutation138 permutation6
    mixedMoment B raw18806step1 raw18806step1Labels = mixedMoment B raw18806step2 raw18806step2Labels := by
      have ha : raw18806step2 = raw18806step1 := by apply Matrix.ext; unfold raw18806step2 raw18806step1; decide +kernel
      have hl : raw18806step1Labels = labelEmbedding9 ∘ raw18806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18806step1 raw18806step1Labels raw18806step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw18807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18807step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18807step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18807 raw18807Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18807 raw18807Labels = mixedMoment B raw18807step0 raw18807step0Labels := by
      have ha : raw18807step0 = (fun i j => raw18807 (permutation605 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18807step0 raw18807; decide +kernel
      have hl : raw18807step0Labels = raw18807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18807 raw18807Labels permutation605 permutation4
    mixedMoment B raw18807step0 raw18807step0Labels = mixedMoment B raw18807step1 raw18807step1Labels := by
      have ha : raw18807step1 = -raw18807step0 := by apply Matrix.ext; change ∀ i j, raw18807step1 i j = -(raw18807step0 i j); unfold raw18807step1 raw18807step0; decide +kernel
      have hl : raw18807step1Labels = raw18807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18807step1 raw18807step1Labels = mixedMoment B raw18807step2 raw18807step2Labels := by
      have ha : raw18807step2 = raw18807step1 := by apply Matrix.ext; unfold raw18807step2 raw18807step1; decide +kernel
      have hl : raw18807step1Labels = labelEmbedding7 ∘ raw18807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18807step1 raw18807step1Labels raw18807step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18808step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18808step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18808step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18808step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18808 raw18808Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw18808 raw18808Labels = mixedMoment B raw18808step0 raw18808step0Labels := by
      have hz : ∀ j, raw18808 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18808step0 = (fun i j => raw18808 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18808step0 raw18808; decide +kernel
      have hl : raw18808step0Labels = raw18808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18808 raw18808Labels permutation265 hz
    mixedMoment B raw18808step0 raw18808step0Labels = mixedMoment B raw18808step1 raw18808step1Labels := by
      have ha : raw18808step1 = (fun i j => raw18808step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18808step1 raw18808step0; decide +kernel
      have hl : raw18808step1Labels = raw18808step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18808step0 raw18808step0Labels permutation36 permutation3
    mixedMoment B raw18808step1 raw18808step1Labels = mixedMoment B raw18808step2 raw18808step2Labels := by
      have ha : raw18808step2 = raw18808step1 := by apply Matrix.ext; unfold raw18808step2 raw18808step1; decide +kernel
      have hl : raw18808step1Labels = labelEmbedding6 ∘ raw18808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18808step1 raw18808step1Labels raw18808step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw18809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18809 raw18809Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18809 raw18809Labels = mixedMoment B raw18809step0 raw18809step0Labels := by
      have hz : ∀ j, raw18809 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18809step0 = (fun i j => raw18809 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18809step0 raw18809; decide +kernel
      have hl : raw18809step0Labels = raw18809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18809 raw18809Labels permutation265 hz
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw18810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18810 raw18810Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw18810 raw18810Labels = mixedMoment B raw18810step0 raw18810step0Labels := by
      have hz : ∀ j, raw18810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18810step0 = (fun i j => raw18810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18810step0 raw18810; decide +kernel
      have hl : raw18810step0Labels = raw18810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18810 raw18810Labels permutation434 hz
    mixedMoment B raw18810step0 raw18810step0Labels = mixedMoment B raw18810step1 raw18810step1Labels := by
      have hz : ∀ j, raw18810step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18810step1 = (fun i j => raw18810step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18810step1 raw18810step0; decide +kernel
      have hl : raw18810step1Labels = raw18810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18810step0 raw18810step0Labels permutation56 hz
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw18811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw18811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18811step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18811step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18811step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18811 raw18811Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw18811 raw18811Labels = mixedMoment B raw18811step0 raw18811step0Labels := by
      have hz : ∀ j, raw18811 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18811step0 = (fun i j => raw18811 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18811step0 raw18811; decide +kernel
      have hl : raw18811step0Labels = raw18811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18811 raw18811Labels permutation520 hz
    mixedMoment B raw18811step0 raw18811step0Labels = mixedMoment B raw18811step1 raw18811step1Labels := by
      have hz : ∀ j, raw18811step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18811step1 = (fun i j => raw18811step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18811step1 raw18811step0; decide +kernel
      have hl : raw18811step1Labels = raw18811step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18811step0 raw18811step0Labels permutation56 hz
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw18812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw18812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18812step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18812step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18812step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18812step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18812 raw18812Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18812 raw18812Labels = mixedMoment B raw18812step0 raw18812step0Labels := by
      have hz : ∀ j, raw18812 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18812step0 = (fun i j => raw18812 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18812step0 raw18812; decide +kernel
      have hl : raw18812step0Labels = raw18812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18812 raw18812Labels permutation265 hz
    mixedMoment B raw18812step0 raw18812step0Labels = mixedMoment B raw18812step1 raw18812step1Labels := by
      have ha : raw18812step1 = (fun i j => raw18812step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18812step1 raw18812step0; decide +kernel
      have hl : raw18812step1Labels = raw18812step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18812step0 raw18812step0Labels permutation131 permutation4
    mixedMoment B raw18812step1 raw18812step1Labels = mixedMoment B raw18812step2 raw18812step2Labels := by
      have ha : raw18812step2 = -raw18812step1 := by apply Matrix.ext; change ∀ i j, raw18812step2 i j = -(raw18812step1 i j); unfold raw18812step2 raw18812step1; decide +kernel
      have hl : raw18812step2Labels = raw18812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18812step2 raw18812step2Labels = mixedMoment B raw18812step3 raw18812step3Labels := by
      have ha : raw18812step3 = raw18812step2 := by apply Matrix.ext; unfold raw18812step3 raw18812step2; decide +kernel
      have hl : raw18812step2Labels = labelEmbedding7 ∘ raw18812step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18812step2 raw18812step2Labels raw18812step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw18813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18813step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18813step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18813step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18813 raw18813Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw18813 raw18813Labels = mixedMoment B raw18813step0 raw18813step0Labels := by
      have ha : raw18813step0 = (fun i j => raw18813 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18813step0 raw18813; decide +kernel
      have hl : raw18813step0Labels = raw18813Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18813 raw18813Labels permutation173 permutation3
    mixedMoment B raw18813step0 raw18813step0Labels = mixedMoment B raw18813step1 raw18813step1Labels := by
      have ha : raw18813step1 = raw18813step0 := by apply Matrix.ext; unfold raw18813step1 raw18813step0; decide +kernel
      have hl : raw18813step0Labels = labelEmbedding6 ∘ raw18813step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18813step0 raw18813step0Labels raw18813step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

def raw18814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18814step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18814step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18814step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18814 raw18814Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw18814 raw18814Labels = mixedMoment B raw18814step0 raw18814step0Labels := by
      have ha : raw18814step0 = (fun i j => raw18814 (permutation286 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18814step0 raw18814; decide +kernel
      have hl : raw18814step0Labels = raw18814Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18814 raw18814Labels permutation286 permutation3
    mixedMoment B raw18814step0 raw18814step0Labels = mixedMoment B raw18814step1 raw18814step1Labels := by
      have ha : raw18814step1 = raw18814step0 := by apply Matrix.ext; unfold raw18814step1 raw18814step0; decide +kernel
      have hl : raw18814step0Labels = labelEmbedding6 ∘ raw18814step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18814step0 raw18814step0Labels raw18814step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

def raw18815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18815step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18815 raw18815Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18815 raw18815Labels = mixedMoment B raw18815step0 raw18815step0Labels := by
      have hz : ∀ j, raw18815 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18815step0 = (fun i j => raw18815 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18815step0 raw18815; decide +kernel
      have hl : raw18815step0Labels = raw18815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18815 raw18815Labels permutation434 hz
    mixedMoment B raw18815step0 raw18815step0Labels = mixedMoment B raw18815step1 raw18815step1Labels := by
      have ha : raw18815step1 = (fun i j => raw18815step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18815step1 raw18815step0; decide +kernel
      have hl : raw18815step1Labels = raw18815step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18815step0 raw18815step0Labels permutation37 permutation3
    mixedMoment B raw18815step1 raw18815step1Labels = mixedMoment B raw18815step2 raw18815step2Labels := by
      have ha : raw18815step2 = raw18815step1 := by apply Matrix.ext; unfold raw18815step2 raw18815step1; decide +kernel
      have hl : raw18815step1Labels = labelEmbedding6 ∘ raw18815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18815step1 raw18815step1Labels raw18815step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
