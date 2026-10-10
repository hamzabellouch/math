import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13696 raw13696Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw13696 raw13696Labels = mixedMoment B raw13696step0 raw13696step0Labels := by
      have ha : raw13696step0 = (fun i j => raw13696 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13696step0 raw13696; decide +kernel
      have hl : raw13696step0Labels = raw13696Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13696 raw13696Labels permutation177 permutation2
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw13697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw13697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13697 raw13697Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw13697 raw13697Labels = mixedMoment B raw13697step0 raw13697step0Labels := by
      have hz : ∀ j, raw13697 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13697step0 = (fun i j => raw13697 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13697step0 raw13697; decide +kernel
      have hl : raw13697step0Labels = raw13697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13697 raw13697Labels permutation590 hz
    mixedMoment B raw13697step0 raw13697step0Labels = mixedMoment B raw13697step1 raw13697step1Labels := by
      have ha : raw13697step1 = (fun i j => raw13697step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13697step1 raw13697step0; decide +kernel
      have hl : raw13697step1Labels = raw13697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13697step0 raw13697step0Labels permutation38 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw13698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13698step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13698 raw13698Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw13698 raw13698Labels = mixedMoment B raw13698step0 raw13698step0Labels := by
      have ha : raw13698step0 = (fun i j => raw13698 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13698step0 raw13698; decide +kernel
      have hl : raw13698step0Labels = raw13698Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13698 raw13698Labels permutation152 permutation3
    mixedMoment B raw13698step0 raw13698step0Labels = mixedMoment B raw13698step1 raw13698step1Labels := by
      have ha : raw13698step1 = raw13698step0 := by apply Matrix.ext; unfold raw13698step1 raw13698step0; decide +kernel
      have hl : raw13698step0Labels = labelEmbedding6 ∘ raw13698step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13698step0 raw13698step0Labels raw13698step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw13699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13699 raw13699Labels = mixedMoment B node5187 node5187Labels := by
  calc
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw13700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13700 raw13700Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw13700 raw13700Labels = mixedMoment B raw13700step0 raw13700step0Labels := by
      have ha : raw13700step0 = (fun i j => raw13700 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13700step0 raw13700; decide +kernel
      have hl : raw13700step0Labels = raw13700Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13700 raw13700Labels permutation176 permutation2
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw13701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13701 raw13701Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw13701 raw13701Labels = mixedMoment B raw13701step0 raw13701step0Labels := by
      have ha : raw13701step0 = (fun i j => raw13701 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13701step0 raw13701; decide +kernel
      have hl : raw13701step0Labels = raw13701Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13701 raw13701Labels permutation176 permutation2
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw13702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw13702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13702 raw13702Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw13702 raw13702Labels = mixedMoment B raw13702step0 raw13702step0Labels := by
      have ha : raw13702step0 = (fun i j => raw13702 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13702step0 raw13702; decide +kernel
      have hl : raw13702step0Labels = raw13702Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13702 raw13702Labels permutation178 permutation2
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw13703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13703 raw13703Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw13703 raw13703Labels = mixedMoment B raw13703step0 raw13703step0Labels := by
      have ha : raw13703step0 = (fun i j => raw13703 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13703step0 raw13703; decide +kernel
      have hl : raw13703step0Labels = raw13703Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13703 raw13703Labels permutation152 permutation3
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw13704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13704 raw13704Labels = mixedMoment B node4038 node4038Labels := by
  calc
    mixedMoment B raw13704 raw13704Labels = mixedMoment B raw13704step0 raw13704step0Labels := by
      have ha : raw13704step0 = (fun i j => raw13704 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13704step0 raw13704; decide +kernel
      have hl : raw13704step0Labels = raw13704Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13704 raw13704Labels permutation176 permutation3
    _ = mixedMoment B node4038 node4038Labels := by rfl

def raw13705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13705step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13705 raw13705Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw13705 raw13705Labels = mixedMoment B raw13705step0 raw13705step0Labels := by
      have ha : raw13705step0 = (fun i j => raw13705 (permutation198 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13705step0 raw13705; decide +kernel
      have hl : raw13705step0Labels = raw13705Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13705 raw13705Labels permutation198 permutation6
    mixedMoment B raw13705step0 raw13705step0Labels = mixedMoment B raw13705step1 raw13705step1Labels := by
      have ha : raw13705step1 = -raw13705step0 := by apply Matrix.ext; change ∀ i j, raw13705step1 i j = -(raw13705step0 i j); unfold raw13705step1 raw13705step0; decide +kernel
      have hl : raw13705step1Labels = raw13705step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw13706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13706step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13706 raw13706Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw13706 raw13706Labels = mixedMoment B raw13706step0 raw13706step0Labels := by
      have ha : raw13706step0 = (fun i j => raw13706 (permutation196 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13706step0 raw13706; decide +kernel
      have hl : raw13706step0Labels = raw13706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13706 raw13706Labels permutation196 permutation6
    mixedMoment B raw13706step0 raw13706step0Labels = mixedMoment B raw13706step1 raw13706step1Labels := by
      have ha : raw13706step1 = -raw13706step0 := by apply Matrix.ext; change ∀ i j, raw13706step1 i j = -(raw13706step0 i j); unfold raw13706step1 raw13706step0; decide +kernel
      have hl : raw13706step1Labels = raw13706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw13707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13707step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13707 raw13707Labels = mixedMoment B node4036 node4036Labels := by
  calc
    mixedMoment B raw13707 raw13707Labels = mixedMoment B raw13707step0 raw13707step0Labels := by
      have hz : ∀ j, raw13707 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13707step0 = (fun i j => raw13707 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13707step0 raw13707; decide +kernel
      have hl : raw13707step0Labels = raw13707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13707 raw13707Labels permutation590 hz
    mixedMoment B raw13707step0 raw13707step0Labels = mixedMoment B raw13707step1 raw13707step1Labels := by
      have ha : raw13707step1 = (fun i j => raw13707step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13707step1 raw13707step0; decide +kernel
      have hl : raw13707step1Labels = raw13707step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13707step0 raw13707step0Labels permutation41 permutation6
    mixedMoment B raw13707step1 raw13707step1Labels = mixedMoment B raw13707step2 raw13707step2Labels := by
      have ha : raw13707step2 = -raw13707step1 := by apply Matrix.ext; change ∀ i j, raw13707step2 i j = -(raw13707step1 i j); unfold raw13707step2 raw13707step1; decide +kernel
      have hl : raw13707step2Labels = raw13707step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4036 node4036Labels := by rfl

def raw13708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13708step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13708step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13708 raw13708Labels = mixedMoment B node1265 node1265Labels := by
  calc
    mixedMoment B raw13708 raw13708Labels = mixedMoment B raw13708step0 raw13708step0Labels := by
      have ha : raw13708step0 = (fun i j => raw13708 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13708step0 raw13708; decide +kernel
      have hl : raw13708step0Labels = raw13708Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13708 raw13708Labels permutation176 permutation3
    _ = mixedMoment B node1265 node1265Labels := by rfl

def raw13709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13709 raw13709Labels = mixedMoment B node2999 node2999Labels := by
  calc
    mixedMoment B raw13709 raw13709Labels = mixedMoment B raw13709step0 raw13709step0Labels := by
      have ha : raw13709step0 = (fun i j => raw13709 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13709step0 raw13709; decide +kernel
      have hl : raw13709step0Labels = raw13709Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13709 raw13709Labels permutation176 permutation3
    _ = mixedMoment B node2999 node2999Labels := by rfl

def raw13710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13710 raw13710Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw13710 raw13710Labels = mixedMoment B raw13710step0 raw13710step0Labels := by
      have ha : raw13710step0 = (fun i j => raw13710 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13710step0 raw13710; decide +kernel
      have hl : raw13710step0Labels = raw13710Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13710 raw13710Labels permutation206 permutation3
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw13711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13711 raw13711Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw13711 raw13711Labels = mixedMoment B raw13711step0 raw13711step0Labels := by
      have ha : raw13711step0 = (fun i j => raw13711 (permutation230 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13711step0 raw13711; decide +kernel
      have hl : raw13711step0Labels = raw13711Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13711 raw13711Labels permutation230 permutation3
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw13712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13712 raw13712Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw13712 raw13712Labels = mixedMoment B raw13712step0 raw13712step0Labels := by
      have hz : ∀ j, raw13712 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13712step0 = (fun i j => raw13712 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13712step0 raw13712; decide +kernel
      have hl : raw13712step0Labels = raw13712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13712 raw13712Labels permutation590 hz
    mixedMoment B raw13712step0 raw13712step0Labels = mixedMoment B raw13712step1 raw13712step1Labels := by
      have ha : raw13712step1 = (fun i j => raw13712step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13712step1 raw13712step0; decide +kernel
      have hl : raw13712step1Labels = raw13712step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13712step0 raw13712step0Labels permutation38 permutation3
    _ = mixedMoment B node3111 node3111Labels := by rfl

def raw13713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13713step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13713step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13713 raw13713Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw13713 raw13713Labels = mixedMoment B raw13713step0 raw13713step0Labels := by
      have ha : raw13713step0 = (fun i j => raw13713 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13713step0 raw13713; decide +kernel
      have hl : raw13713step0Labels = raw13713Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13713 raw13713Labels permutation161 permutation3
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw13714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13714 raw13714Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw13714 raw13714Labels = mixedMoment B raw13714step0 raw13714step0Labels := by
      have ha : raw13714step0 = (fun i j => raw13714 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13714step0 raw13714; decide +kernel
      have hl : raw13714step0Labels = raw13714Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13714 raw13714Labels permutation161 permutation3
    _ = mixedMoment B node2878 node2878Labels := by rfl

def raw13715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13715Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13715step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13715 raw13715Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13715 raw13715Labels = mixedMoment B raw13715step0 raw13715step0Labels := by
      have ha : raw13715step0 = (fun i j => raw13715 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13715step0 raw13715; decide +kernel
      have hl : raw13715step0Labels = raw13715Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13715 raw13715Labels permutation161 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13716Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13716step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13716 raw13716Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13716 raw13716Labels = mixedMoment B raw13716step0 raw13716step0Labels := by
      have ha : raw13716step0 = (fun i j => raw13716 (permutation167 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13716step0 raw13716; decide +kernel
      have hl : raw13716step0Labels = raw13716Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13716 raw13716Labels permutation167 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13717Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13717step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13717step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13717step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13717step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13717 raw13717Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw13717 raw13717Labels = mixedMoment B raw13717step0 raw13717step0Labels := by
      have hz : ∀ j, raw13717 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13717step0 = (fun i j => raw13717 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13717step0 raw13717; decide +kernel
      have hl : raw13717step0Labels = raw13717Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13717 raw13717Labels permutation590 hz
    mixedMoment B raw13717step0 raw13717step0Labels = mixedMoment B raw13717step1 raw13717step1Labels := by
      have ha : raw13717step1 = (fun i j => raw13717step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13717step1 raw13717step0; decide +kernel
      have hl : raw13717step1Labels = raw13717step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13717step0 raw13717step0Labels permutation35 permutation3
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw13718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13718Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13718step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13718 raw13718Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw13718 raw13718Labels = mixedMoment B raw13718step0 raw13718step0Labels := by
      have ha : raw13718step0 = (fun i j => raw13718 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13718step0 raw13718; decide +kernel
      have hl : raw13718step0Labels = raw13718Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13718 raw13718Labels permutation155 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw13719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13719Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13719step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13719 raw13719Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw13719 raw13719Labels = mixedMoment B raw13719step0 raw13719step0Labels := by
      have ha : raw13719step0 = (fun i j => raw13719 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13719step0 raw13719; decide +kernel
      have hl : raw13719step0Labels = raw13719Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13719 raw13719Labels permutation155 permutation3
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw13720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13720Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13720step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13720step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13720 raw13720Labels = mixedMoment B node2987 node2987Labels := by
  calc
    mixedMoment B raw13720 raw13720Labels = mixedMoment B raw13720step0 raw13720step0Labels := by
      have ha : raw13720step0 = (fun i j => raw13720 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13720step0 raw13720; decide +kernel
      have hl : raw13720step0Labels = raw13720Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13720 raw13720Labels permutation179 permutation3
    _ = mixedMoment B node2987 node2987Labels := by rfl

def raw13721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13721Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13721step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13721 raw13721Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw13721 raw13721Labels = mixedMoment B raw13721step0 raw13721step0Labels := by
      have ha : raw13721step0 = (fun i j => raw13721 (permutation165 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13721step0 raw13721; decide +kernel
      have hl : raw13721step0Labels = raw13721Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13721 raw13721Labels permutation165 permutation3
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw13722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13722Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw13722step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13722step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13722 raw13722Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw13722 raw13722Labels = mixedMoment B raw13722step0 raw13722step0Labels := by
      have hz : ∀ j, raw13722 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13722step0 = (fun i j => raw13722 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13722step0 raw13722; decide +kernel
      have hl : raw13722step0Labels = raw13722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13722 raw13722Labels permutation590 hz
    mixedMoment B raw13722step0 raw13722step0Labels = mixedMoment B raw13722step1 raw13722step1Labels := by
      have ha : raw13722step1 = (fun i j => raw13722step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13722step1 raw13722step0; decide +kernel
      have hl : raw13722step1Labels = raw13722step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13722step0 raw13722step0Labels permutation33 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw13723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13723Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13723step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13723 raw13723Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw13723 raw13723Labels = mixedMoment B raw13723step0 raw13723step0Labels := by
      have ha : raw13723step0 = (fun i j => raw13723 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13723step0 raw13723; decide +kernel
      have hl : raw13723step0Labels = raw13723Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13723 raw13723Labels permutation153 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw13724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13724Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13724step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13724 raw13724Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw13724 raw13724Labels = mixedMoment B raw13724step0 raw13724step0Labels := by
      have ha : raw13724step0 = (fun i j => raw13724 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13724step0 raw13724; decide +kernel
      have hl : raw13724step0Labels = raw13724Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13724 raw13724Labels permutation153 permutation3
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw13725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13725Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13725step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13725step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13725 raw13725Labels = mixedMoment B node2987 node2987Labels := by
  calc
    mixedMoment B raw13725 raw13725Labels = mixedMoment B raw13725step0 raw13725step0Labels := by
      have ha : raw13725step0 = (fun i j => raw13725 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13725step0 raw13725; decide +kernel
      have hl : raw13725step0Labels = raw13725Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13725 raw13725Labels permutation177 permutation3
    _ = mixedMoment B node2987 node2987Labels := by rfl

def raw13726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13726Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13726step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13726 raw13726Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw13726 raw13726Labels = mixedMoment B raw13726step0 raw13726step0Labels := by
      have ha : raw13726step0 = (fun i j => raw13726 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13726step0 raw13726; decide +kernel
      have hl : raw13726step0Labels = raw13726Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13726 raw13726Labels permutation159 permutation3
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw13727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw13727Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13727step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13727step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13727 raw13727Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw13727 raw13727Labels = mixedMoment B raw13727step0 raw13727step0Labels := by
      have hz : ∀ j, raw13727 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13727step0 = (fun i j => raw13727 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13727step0 raw13727; decide +kernel
      have hl : raw13727step0Labels = raw13727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13727 raw13727Labels permutation590 hz
    mixedMoment B raw13727step0 raw13727step0Labels = mixedMoment B raw13727step1 raw13727step1Labels := by
      have ha : raw13727step1 = (fun i j => raw13727step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13727step1 raw13727step0; decide +kernel
      have hl : raw13727step1Labels = raw13727step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13727step0 raw13727step0Labels permutation32 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw13728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13728Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13728step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13728 raw13728Labels = mixedMoment B node1212 node1212Labels := by
  calc
    mixedMoment B raw13728 raw13728Labels = mixedMoment B raw13728step0 raw13728step0Labels := by
      have ha : raw13728step0 = (fun i j => raw13728 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13728step0 raw13728; decide +kernel
      have hl : raw13728step0Labels = raw13728Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13728 raw13728Labels permutation152 permutation3
    _ = mixedMoment B node1212 node1212Labels := by rfl

def raw13729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13729Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13729step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13729 raw13729Labels = mixedMoment B node2861 node2861Labels := by
  calc
    mixedMoment B raw13729 raw13729Labels = mixedMoment B raw13729step0 raw13729step0Labels := by
      have ha : raw13729step0 = (fun i j => raw13729 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13729step0 raw13729; decide +kernel
      have hl : raw13729step0Labels = raw13729Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13729 raw13729Labels permutation152 permutation3
    _ = mixedMoment B node2861 node2861Labels := by rfl

def raw13730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13730Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13730step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13730 raw13730Labels = mixedMoment B node2986 node2986Labels := by
  calc
    mixedMoment B raw13730 raw13730Labels = mixedMoment B raw13730step0 raw13730step0Labels := by
      have ha : raw13730step0 = (fun i j => raw13730 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13730step0 raw13730; decide +kernel
      have hl : raw13730step0Labels = raw13730Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13730 raw13730Labels permutation176 permutation3
    _ = mixedMoment B node2986 node2986Labels := by rfl

def raw13731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13731Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13731step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13731 raw13731Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw13731 raw13731Labels = mixedMoment B raw13731step0 raw13731step0Labels := by
      have ha : raw13731step0 = (fun i j => raw13731 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13731step0 raw13731; decide +kernel
      have hl : raw13731step0Labels = raw13731Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13731 raw13731Labels permutation158 permutation3
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw13732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw13732Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13732step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13732step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13732 raw13732Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw13732 raw13732Labels = mixedMoment B raw13732step0 raw13732step0Labels := by
      have ha : raw13732step0 = (fun i j => raw13732 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13732step0 raw13732; decide +kernel
      have hl : raw13732step0Labels = raw13732Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13732 raw13732Labels permutation164 permutation3
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw13733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13733 raw13733Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw13733 raw13733Labels = mixedMoment B raw13733step0 raw13733step0Labels := by
      have ha : raw13733step0 = (fun i j => raw13733 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13733step0 raw13733; decide +kernel
      have hl : raw13733step0Labels = raw13733Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13733 raw13733Labels permutation194 permutation7
    mixedMoment B raw13733step0 raw13733step0Labels = mixedMoment B raw13733step1 raw13733step1Labels := by
      have ha : raw13733step1 = -raw13733step0 := by apply Matrix.ext; change ∀ i j, raw13733step1 i j = -(raw13733step0 i j); unfold raw13733step1 raw13733step0; decide +kernel
      have hl : raw13733step1Labels = raw13733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13733step1 raw13733step1Labels = mixedMoment B raw13733step2 raw13733step2Labels := by
      have ha : raw13733step2 = raw13733step1 := by apply Matrix.ext; unfold raw13733step2 raw13733step1; decide +kernel
      have hl : raw13733step1Labels = labelEmbedding1 ∘ raw13733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13733step1 raw13733step1Labels raw13733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw13734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13734step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13734 raw13734Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw13734 raw13734Labels = mixedMoment B raw13734step0 raw13734step0Labels := by
      have ha : raw13734step0 = (fun i j => raw13734 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13734step0 raw13734; decide +kernel
      have hl : raw13734step0Labels = raw13734Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13734 raw13734Labels permutation194 permutation7
    mixedMoment B raw13734step0 raw13734step0Labels = mixedMoment B raw13734step1 raw13734step1Labels := by
      have ha : raw13734step1 = -raw13734step0 := by apply Matrix.ext; change ∀ i j, raw13734step1 i j = -(raw13734step0 i j); unfold raw13734step1 raw13734step0; decide +kernel
      have hl : raw13734step1Labels = raw13734step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13734step1 raw13734step1Labels = mixedMoment B raw13734step2 raw13734step2Labels := by
      have ha : raw13734step2 = raw13734step1 := by apply Matrix.ext; unfold raw13734step2 raw13734step1; decide +kernel
      have hl : raw13734step1Labels = labelEmbedding1 ∘ raw13734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13734step1 raw13734step1Labels raw13734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

def raw13735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13735step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13735step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13735step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13735step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13735step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13735 raw13735Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw13735 raw13735Labels = mixedMoment B raw13735step0 raw13735step0Labels := by
      have ha : raw13735step0 = (fun i j => raw13735 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13735step0 raw13735; decide +kernel
      have hl : raw13735step0Labels = raw13735Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13735 raw13735Labels permutation194 permutation7
    mixedMoment B raw13735step0 raw13735step0Labels = mixedMoment B raw13735step1 raw13735step1Labels := by
      have ha : raw13735step1 = -raw13735step0 := by apply Matrix.ext; change ∀ i j, raw13735step1 i j = -(raw13735step0 i j); unfold raw13735step1 raw13735step0; decide +kernel
      have hl : raw13735step1Labels = raw13735step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13735step1 raw13735step1Labels = mixedMoment B raw13735step2 raw13735step2Labels := by
      have ha : raw13735step2 = raw13735step1 := by apply Matrix.ext; unfold raw13735step2 raw13735step1; decide +kernel
      have hl : raw13735step1Labels = labelEmbedding1 ∘ raw13735step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13735step1 raw13735step1Labels raw13735step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw13736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13736 raw13736Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw13736 raw13736Labels = mixedMoment B raw13736step0 raw13736step0Labels := by
      have ha : raw13736step0 = (fun i j => raw13736 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13736step0 raw13736; decide +kernel
      have hl : raw13736step0Labels = raw13736Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13736 raw13736Labels permutation195 permutation7
    mixedMoment B raw13736step0 raw13736step0Labels = mixedMoment B raw13736step1 raw13736step1Labels := by
      have ha : raw13736step1 = -raw13736step0 := by apply Matrix.ext; change ∀ i j, raw13736step1 i j = -(raw13736step0 i j); unfold raw13736step1 raw13736step0; decide +kernel
      have hl : raw13736step1Labels = raw13736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13736step1 raw13736step1Labels = mixedMoment B raw13736step2 raw13736step2Labels := by
      have ha : raw13736step2 = raw13736step1 := by apply Matrix.ext; unfold raw13736step2 raw13736step1; decide +kernel
      have hl : raw13736step1Labels = labelEmbedding1 ∘ raw13736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13736step1 raw13736step1Labels raw13736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw13737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13737 raw13737Labels = mixedMoment B node3859 node3859Labels := by
  calc
    mixedMoment B raw13737 raw13737Labels = mixedMoment B raw13737step0 raw13737step0Labels := by
      have hz : ∀ j, raw13737 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13737step0 = (fun i j => raw13737 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13737step0 raw13737; decide +kernel
      have hl : raw13737step0Labels = raw13737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13737 raw13737Labels permutation590 hz
    mixedMoment B raw13737step0 raw13737step0Labels = mixedMoment B raw13737step1 raw13737step1Labels := by
      have ha : raw13737step1 = (fun i j => raw13737step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13737step1 raw13737step0; decide +kernel
      have hl : raw13737step1Labels = raw13737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13737step0 raw13737step0Labels permutation38 permutation7
    mixedMoment B raw13737step1 raw13737step1Labels = mixedMoment B raw13737step2 raw13737step2Labels := by
      have ha : raw13737step2 = -raw13737step1 := by apply Matrix.ext; change ∀ i j, raw13737step2 i j = -(raw13737step1 i j); unfold raw13737step2 raw13737step1; decide +kernel
      have hl : raw13737step2Labels = raw13737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13737step2 raw13737step2Labels = mixedMoment B raw13737step3 raw13737step3Labels := by
      have ha : raw13737step3 = raw13737step2 := by apply Matrix.ext; unfold raw13737step3 raw13737step2; decide +kernel
      have hl : raw13737step2Labels = labelEmbedding1 ∘ raw13737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13737step2 raw13737step2Labels raw13737step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3859 node3859Labels := by rfl

def raw13738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13738step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13738step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13738step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13738step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13738 raw13738Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw13738 raw13738Labels = mixedMoment B raw13738step0 raw13738step0Labels := by
      have ha : raw13738step0 = (fun i j => raw13738 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13738step0 raw13738; decide +kernel
      have hl : raw13738step0Labels = raw13738Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13738 raw13738Labels permutation194 permutation7
    mixedMoment B raw13738step0 raw13738step0Labels = mixedMoment B raw13738step1 raw13738step1Labels := by
      have ha : raw13738step1 = -raw13738step0 := by apply Matrix.ext; change ∀ i j, raw13738step1 i j = -(raw13738step0 i j); unfold raw13738step1 raw13738step0; decide +kernel
      have hl : raw13738step1Labels = raw13738step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13738step1 raw13738step1Labels = mixedMoment B raw13738step2 raw13738step2Labels := by
      have ha : raw13738step2 = raw13738step1 := by apply Matrix.ext; unfold raw13738step2 raw13738step1; decide +kernel
      have hl : raw13738step1Labels = labelEmbedding1 ∘ raw13738step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13738step1 raw13738step1Labels raw13738step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

def raw13739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13739step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13739step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13739step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13739step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13739step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13739 raw13739Labels = mixedMoment B node3469 node3469Labels := by
  calc
    mixedMoment B raw13739 raw13739Labels = mixedMoment B raw13739step0 raw13739step0Labels := by
      have ha : raw13739step0 = (fun i j => raw13739 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13739step0 raw13739; decide +kernel
      have hl : raw13739step0Labels = raw13739Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13739 raw13739Labels permutation194 permutation7
    mixedMoment B raw13739step0 raw13739step0Labels = mixedMoment B raw13739step1 raw13739step1Labels := by
      have ha : raw13739step1 = -raw13739step0 := by apply Matrix.ext; change ∀ i j, raw13739step1 i j = -(raw13739step0 i j); unfold raw13739step1 raw13739step0; decide +kernel
      have hl : raw13739step1Labels = raw13739step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13739step1 raw13739step1Labels = mixedMoment B raw13739step2 raw13739step2Labels := by
      have ha : raw13739step2 = raw13739step1 := by apply Matrix.ext; unfold raw13739step2 raw13739step1; decide +kernel
      have hl : raw13739step1Labels = labelEmbedding1 ∘ raw13739step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13739step1 raw13739step1Labels raw13739step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3469 node3469Labels := by rfl

def raw13740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13740step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13740step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13740step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13740step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13740step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13740 raw13740Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw13740 raw13740Labels = mixedMoment B raw13740step0 raw13740step0Labels := by
      have ha : raw13740step0 = (fun i j => raw13740 (permutation196 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13740step0 raw13740; decide +kernel
      have hl : raw13740step0Labels = raw13740Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13740 raw13740Labels permutation196 permutation7
    mixedMoment B raw13740step0 raw13740step0Labels = mixedMoment B raw13740step1 raw13740step1Labels := by
      have ha : raw13740step1 = -raw13740step0 := by apply Matrix.ext; change ∀ i j, raw13740step1 i j = -(raw13740step0 i j); unfold raw13740step1 raw13740step0; decide +kernel
      have hl : raw13740step1Labels = raw13740step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13740step1 raw13740step1Labels = mixedMoment B raw13740step2 raw13740step2Labels := by
      have ha : raw13740step2 = raw13740step1 := by apply Matrix.ext; unfold raw13740step2 raw13740step1; decide +kernel
      have hl : raw13740step1Labels = labelEmbedding1 ∘ raw13740step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13740step1 raw13740step1Labels raw13740step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw13741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13741step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13741step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13741 raw13741Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw13741 raw13741Labels = mixedMoment B raw13741step0 raw13741step0Labels := by
      have ha : raw13741step0 = (fun i j => raw13741 (permutation198 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13741step0 raw13741; decide +kernel
      have hl : raw13741step0Labels = raw13741Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13741 raw13741Labels permutation198 permutation7
    mixedMoment B raw13741step0 raw13741step0Labels = mixedMoment B raw13741step1 raw13741step1Labels := by
      have ha : raw13741step1 = -raw13741step0 := by apply Matrix.ext; change ∀ i j, raw13741step1 i j = -(raw13741step0 i j); unfold raw13741step1 raw13741step0; decide +kernel
      have hl : raw13741step1Labels = raw13741step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13741step1 raw13741step1Labels = mixedMoment B raw13741step2 raw13741step2Labels := by
      have ha : raw13741step2 = raw13741step1 := by apply Matrix.ext; unfold raw13741step2 raw13741step1; decide +kernel
      have hl : raw13741step1Labels = labelEmbedding1 ∘ raw13741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13741step1 raw13741step1Labels raw13741step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw13742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13742 raw13742Labels = mixedMoment B node3546 node3546Labels := by
  calc
    mixedMoment B raw13742 raw13742Labels = mixedMoment B raw13742step0 raw13742step0Labels := by
      have hz : ∀ j, raw13742 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13742step0 = (fun i j => raw13742 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13742step0 raw13742; decide +kernel
      have hl : raw13742step0Labels = raw13742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13742 raw13742Labels permutation590 hz
    mixedMoment B raw13742step0 raw13742step0Labels = mixedMoment B raw13742step1 raw13742step1Labels := by
      have ha : raw13742step1 = (fun i j => raw13742step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13742step1 raw13742step0; decide +kernel
      have hl : raw13742step1Labels = raw13742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13742step0 raw13742step0Labels permutation38 permutation7
    mixedMoment B raw13742step1 raw13742step1Labels = mixedMoment B raw13742step2 raw13742step2Labels := by
      have ha : raw13742step2 = -raw13742step1 := by apply Matrix.ext; change ∀ i j, raw13742step2 i j = -(raw13742step1 i j); unfold raw13742step2 raw13742step1; decide +kernel
      have hl : raw13742step2Labels = raw13742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13742step2 raw13742step2Labels = mixedMoment B raw13742step3 raw13742step3Labels := by
      have ha : raw13742step3 = raw13742step2 := by apply Matrix.ext; unfold raw13742step3 raw13742step2; decide +kernel
      have hl : raw13742step2Labels = labelEmbedding1 ∘ raw13742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13742step2 raw13742step2Labels raw13742step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3546 node3546Labels := by rfl

def raw13743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13743step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13743step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13743step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13743 raw13743Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw13743 raw13743Labels = mixedMoment B raw13743step0 raw13743step0Labels := by
      have ha : raw13743step0 = (fun i j => raw13743 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13743step0 raw13743; decide +kernel
      have hl : raw13743step0Labels = raw13743Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13743 raw13743Labels permutation161 permutation5
    mixedMoment B raw13743step0 raw13743step0Labels = mixedMoment B raw13743step1 raw13743step1Labels := by
      have ha : raw13743step1 = -raw13743step0 := by apply Matrix.ext; change ∀ i j, raw13743step1 i j = -(raw13743step0 i j); unfold raw13743step1 raw13743step0; decide +kernel
      have hl : raw13743step1Labels = raw13743step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13743step1 raw13743step1Labels = mixedMoment B raw13743step2 raw13743step2Labels := by
      have ha : raw13743step2 = raw13743step1 := by apply Matrix.ext; unfold raw13743step2 raw13743step1; decide +kernel
      have hl : raw13743step1Labels = labelEmbedding1 ∘ raw13743step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13743step1 raw13743step1Labels raw13743step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw13744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13744step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13744step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13744step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13744step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13744step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13744 raw13744Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw13744 raw13744Labels = mixedMoment B raw13744step0 raw13744step0Labels := by
      have ha : raw13744step0 = (fun i j => raw13744 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13744step0 raw13744; decide +kernel
      have hl : raw13744step0Labels = raw13744Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13744 raw13744Labels permutation194 permutation7
    mixedMoment B raw13744step0 raw13744step0Labels = mixedMoment B raw13744step1 raw13744step1Labels := by
      have ha : raw13744step1 = -raw13744step0 := by apply Matrix.ext; change ∀ i j, raw13744step1 i j = -(raw13744step0 i j); unfold raw13744step1 raw13744step0; decide +kernel
      have hl : raw13744step1Labels = raw13744step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13744step1 raw13744step1Labels = mixedMoment B raw13744step2 raw13744step2Labels := by
      have ha : raw13744step2 = raw13744step1 := by apply Matrix.ext; unfold raw13744step2 raw13744step1; decide +kernel
      have hl : raw13744step1Labels = labelEmbedding1 ∘ raw13744step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13744step1 raw13744step1Labels raw13744step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw13745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13745step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13745step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13745step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13745step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13745step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13745 raw13745Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw13745 raw13745Labels = mixedMoment B raw13745step0 raw13745step0Labels := by
      have ha : raw13745step0 = (fun i j => raw13745 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13745step0 raw13745; decide +kernel
      have hl : raw13745step0Labels = raw13745Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13745 raw13745Labels permutation194 permutation7
    mixedMoment B raw13745step0 raw13745step0Labels = mixedMoment B raw13745step1 raw13745step1Labels := by
      have ha : raw13745step1 = -raw13745step0 := by apply Matrix.ext; change ∀ i j, raw13745step1 i j = -(raw13745step0 i j); unfold raw13745step1 raw13745step0; decide +kernel
      have hl : raw13745step1Labels = raw13745step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13745step1 raw13745step1Labels = mixedMoment B raw13745step2 raw13745step2Labels := by
      have ha : raw13745step2 = raw13745step1 := by apply Matrix.ext; unfold raw13745step2 raw13745step1; decide +kernel
      have hl : raw13745step1Labels = labelEmbedding1 ∘ raw13745step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13745step1 raw13745step1Labels raw13745step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw13746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13746step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13746 raw13746Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw13746 raw13746Labels = mixedMoment B raw13746step0 raw13746step0Labels := by
      have ha : raw13746step0 = (fun i j => raw13746 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13746step0 raw13746; decide +kernel
      have hl : raw13746step0Labels = raw13746Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13746 raw13746Labels permutation195 permutation7
    mixedMoment B raw13746step0 raw13746step0Labels = mixedMoment B raw13746step1 raw13746step1Labels := by
      have ha : raw13746step1 = -raw13746step0 := by apply Matrix.ext; change ∀ i j, raw13746step1 i j = -(raw13746step0 i j); unfold raw13746step1 raw13746step0; decide +kernel
      have hl : raw13746step1Labels = raw13746step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13746step1 raw13746step1Labels = mixedMoment B raw13746step2 raw13746step2Labels := by
      have ha : raw13746step2 = raw13746step1 := by apply Matrix.ext; unfold raw13746step2 raw13746step1; decide +kernel
      have hl : raw13746step1Labels = labelEmbedding1 ∘ raw13746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13746step1 raw13746step1Labels raw13746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw13747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13747 raw13747Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw13747 raw13747Labels = mixedMoment B raw13747step0 raw13747step0Labels := by
      have hz : ∀ j, raw13747 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13747step0 = (fun i j => raw13747 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13747step0 raw13747; decide +kernel
      have hl : raw13747step0Labels = raw13747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13747 raw13747Labels permutation590 hz
    mixedMoment B raw13747step0 raw13747step0Labels = mixedMoment B raw13747step1 raw13747step1Labels := by
      have ha : raw13747step1 = (fun i j => raw13747step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13747step1 raw13747step0; decide +kernel
      have hl : raw13747step1Labels = raw13747step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13747step0 raw13747step0Labels permutation38 permutation7
    mixedMoment B raw13747step1 raw13747step1Labels = mixedMoment B raw13747step2 raw13747step2Labels := by
      have ha : raw13747step2 = -raw13747step1 := by apply Matrix.ext; change ∀ i j, raw13747step2 i j = -(raw13747step1 i j); unfold raw13747step2 raw13747step1; decide +kernel
      have hl : raw13747step2Labels = raw13747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13747step2 raw13747step2Labels = mixedMoment B raw13747step3 raw13747step3Labels := by
      have ha : raw13747step3 = raw13747step2 := by apply Matrix.ext; unfold raw13747step3 raw13747step2; decide +kernel
      have hl : raw13747step2Labels = labelEmbedding1 ∘ raw13747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13747step2 raw13747step2Labels raw13747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw13748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13748step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13748step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13748step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13748step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13748 raw13748Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw13748 raw13748Labels = mixedMoment B raw13748step0 raw13748step0Labels := by
      have ha : raw13748step0 = (fun i j => raw13748 (permutation165 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13748step0 raw13748; decide +kernel
      have hl : raw13748step0Labels = raw13748Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13748 raw13748Labels permutation165 permutation5
    mixedMoment B raw13748step0 raw13748step0Labels = mixedMoment B raw13748step1 raw13748step1Labels := by
      have ha : raw13748step1 = -raw13748step0 := by apply Matrix.ext; change ∀ i j, raw13748step1 i j = -(raw13748step0 i j); unfold raw13748step1 raw13748step0; decide +kernel
      have hl : raw13748step1Labels = raw13748step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13748step1 raw13748step1Labels = mixedMoment B raw13748step2 raw13748step2Labels := by
      have ha : raw13748step2 = raw13748step1 := by apply Matrix.ext; unfold raw13748step2 raw13748step1; decide +kernel
      have hl : raw13748step1Labels = labelEmbedding1 ∘ raw13748step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13748step1 raw13748step1Labels raw13748step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw13749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw13749step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13749step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13749step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13749step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13749step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13749 raw13749Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw13749 raw13749Labels = mixedMoment B raw13749step0 raw13749step0Labels := by
      have ha : raw13749step0 = (fun i j => raw13749 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13749step0 raw13749; decide +kernel
      have hl : raw13749step0Labels = raw13749Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13749 raw13749Labels permutation195 permutation7
    mixedMoment B raw13749step0 raw13749step0Labels = mixedMoment B raw13749step1 raw13749step1Labels := by
      have ha : raw13749step1 = -raw13749step0 := by apply Matrix.ext; change ∀ i j, raw13749step1 i j = -(raw13749step0 i j); unfold raw13749step1 raw13749step0; decide +kernel
      have hl : raw13749step1Labels = raw13749step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13749step1 raw13749step1Labels = mixedMoment B raw13749step2 raw13749step2Labels := by
      have ha : raw13749step2 = raw13749step1 := by apply Matrix.ext; unfold raw13749step2 raw13749step1; decide +kernel
      have hl : raw13749step1Labels = labelEmbedding1 ∘ raw13749step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13749step1 raw13749step1Labels raw13749step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw13750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13750step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13750step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13750step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13750step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13750step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13750step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13750 raw13750Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw13750 raw13750Labels = mixedMoment B raw13750step0 raw13750step0Labels := by
      have ha : raw13750step0 = (fun i j => raw13750 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13750step0 raw13750; decide +kernel
      have hl : raw13750step0Labels = raw13750Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13750 raw13750Labels permutation195 permutation7
    mixedMoment B raw13750step0 raw13750step0Labels = mixedMoment B raw13750step1 raw13750step1Labels := by
      have ha : raw13750step1 = -raw13750step0 := by apply Matrix.ext; change ∀ i j, raw13750step1 i j = -(raw13750step0 i j); unfold raw13750step1 raw13750step0; decide +kernel
      have hl : raw13750step1Labels = raw13750step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13750step1 raw13750step1Labels = mixedMoment B raw13750step2 raw13750step2Labels := by
      have ha : raw13750step2 = raw13750step1 := by apply Matrix.ext; unfold raw13750step2 raw13750step1; decide +kernel
      have hl : raw13750step1Labels = labelEmbedding1 ∘ raw13750step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13750step1 raw13750step1Labels raw13750step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw13751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13751step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13751step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13751step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13751 raw13751Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw13751 raw13751Labels = mixedMoment B raw13751step0 raw13751step0Labels := by
      have ha : raw13751step0 = (fun i j => raw13751 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13751step0 raw13751; decide +kernel
      have hl : raw13751step0Labels = raw13751Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13751 raw13751Labels permutation195 permutation7
    mixedMoment B raw13751step0 raw13751step0Labels = mixedMoment B raw13751step1 raw13751step1Labels := by
      have ha : raw13751step1 = -raw13751step0 := by apply Matrix.ext; change ∀ i j, raw13751step1 i j = -(raw13751step0 i j); unfold raw13751step1 raw13751step0; decide +kernel
      have hl : raw13751step1Labels = raw13751step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13751step1 raw13751step1Labels = mixedMoment B raw13751step2 raw13751step2Labels := by
      have ha : raw13751step2 = raw13751step1 := by apply Matrix.ext; unfold raw13751step2 raw13751step1; decide +kernel
      have hl : raw13751step1Labels = labelEmbedding1 ∘ raw13751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13751step1 raw13751step1Labels raw13751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

def raw13752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw13752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13752step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13752step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13752step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13752 raw13752Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw13752 raw13752Labels = mixedMoment B raw13752step0 raw13752step0Labels := by
      have hz : ∀ j, raw13752 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13752step0 = (fun i j => raw13752 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13752step0 raw13752; decide +kernel
      have hl : raw13752step0Labels = raw13752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13752 raw13752Labels permutation590 hz
    mixedMoment B raw13752step0 raw13752step0Labels = mixedMoment B raw13752step1 raw13752step1Labels := by
      have ha : raw13752step1 = (fun i j => raw13752step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13752step1 raw13752step0; decide +kernel
      have hl : raw13752step1Labels = raw13752step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13752step0 raw13752step0Labels permutation39 permutation7
    mixedMoment B raw13752step1 raw13752step1Labels = mixedMoment B raw13752step2 raw13752step2Labels := by
      have ha : raw13752step2 = -raw13752step1 := by apply Matrix.ext; change ∀ i j, raw13752step2 i j = -(raw13752step1 i j); unfold raw13752step2 raw13752step1; decide +kernel
      have hl : raw13752step2Labels = raw13752step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13752step2 raw13752step2Labels = mixedMoment B raw13752step3 raw13752step3Labels := by
      have ha : raw13752step3 = raw13752step2 := by apply Matrix.ext; unfold raw13752step3 raw13752step2; decide +kernel
      have hl : raw13752step2Labels = labelEmbedding1 ∘ raw13752step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13752step2 raw13752step2Labels raw13752step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw13753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13753step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13753step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13753step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13753step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13753step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13753step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13753 raw13753Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw13753 raw13753Labels = mixedMoment B raw13753step0 raw13753step0Labels := by
      have ha : raw13753step0 = (fun i j => raw13753 (permutation159 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13753step0 raw13753; decide +kernel
      have hl : raw13753step0Labels = raw13753Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13753 raw13753Labels permutation159 permutation5
    mixedMoment B raw13753step0 raw13753step0Labels = mixedMoment B raw13753step1 raw13753step1Labels := by
      have ha : raw13753step1 = -raw13753step0 := by apply Matrix.ext; change ∀ i j, raw13753step1 i j = -(raw13753step0 i j); unfold raw13753step1 raw13753step0; decide +kernel
      have hl : raw13753step1Labels = raw13753step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13753step1 raw13753step1Labels = mixedMoment B raw13753step2 raw13753step2Labels := by
      have ha : raw13753step2 = raw13753step1 := by apply Matrix.ext; unfold raw13753step2 raw13753step1; decide +kernel
      have hl : raw13753step1Labels = labelEmbedding1 ∘ raw13753step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13753step1 raw13753step1Labels raw13753step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw13754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13754step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw13754step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13754step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13754step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13754step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13754step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13754 raw13754Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw13754 raw13754Labels = mixedMoment B raw13754step0 raw13754step0Labels := by
      have ha : raw13754step0 = (fun i j => raw13754 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13754step0 raw13754; decide +kernel
      have hl : raw13754step0Labels = raw13754Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13754 raw13754Labels permutation194 permutation7
    mixedMoment B raw13754step0 raw13754step0Labels = mixedMoment B raw13754step1 raw13754step1Labels := by
      have ha : raw13754step1 = -raw13754step0 := by apply Matrix.ext; change ∀ i j, raw13754step1 i j = -(raw13754step0 i j); unfold raw13754step1 raw13754step0; decide +kernel
      have hl : raw13754step1Labels = raw13754step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13754step1 raw13754step1Labels = mixedMoment B raw13754step2 raw13754step2Labels := by
      have ha : raw13754step2 = raw13754step1 := by apply Matrix.ext; unfold raw13754step2 raw13754step1; decide +kernel
      have hl : raw13754step1Labels = labelEmbedding1 ∘ raw13754step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13754step1 raw13754step1Labels raw13754step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw13755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13755step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13755step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13755step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13755step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13755step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13755step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13755 raw13755Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw13755 raw13755Labels = mixedMoment B raw13755step0 raw13755step0Labels := by
      have ha : raw13755step0 = (fun i j => raw13755 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13755step0 raw13755; decide +kernel
      have hl : raw13755step0Labels = raw13755Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13755 raw13755Labels permutation194 permutation7
    mixedMoment B raw13755step0 raw13755step0Labels = mixedMoment B raw13755step1 raw13755step1Labels := by
      have ha : raw13755step1 = -raw13755step0 := by apply Matrix.ext; change ∀ i j, raw13755step1 i j = -(raw13755step0 i j); unfold raw13755step1 raw13755step0; decide +kernel
      have hl : raw13755step1Labels = raw13755step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13755step1 raw13755step1Labels = mixedMoment B raw13755step2 raw13755step2Labels := by
      have ha : raw13755step2 = raw13755step1 := by apply Matrix.ext; unfold raw13755step2 raw13755step1; decide +kernel
      have hl : raw13755step1Labels = labelEmbedding1 ∘ raw13755step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13755step1 raw13755step1Labels raw13755step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw13756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13756step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13756step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13756step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13756step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13756step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13756 raw13756Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw13756 raw13756Labels = mixedMoment B raw13756step0 raw13756step0Labels := by
      have ha : raw13756step0 = (fun i j => raw13756 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13756step0 raw13756; decide +kernel
      have hl : raw13756step0Labels = raw13756Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13756 raw13756Labels permutation194 permutation7
    mixedMoment B raw13756step0 raw13756step0Labels = mixedMoment B raw13756step1 raw13756step1Labels := by
      have ha : raw13756step1 = -raw13756step0 := by apply Matrix.ext; change ∀ i j, raw13756step1 i j = -(raw13756step0 i j); unfold raw13756step1 raw13756step0; decide +kernel
      have hl : raw13756step1Labels = raw13756step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13756step1 raw13756step1Labels = mixedMoment B raw13756step2 raw13756step2Labels := by
      have ha : raw13756step2 = raw13756step1 := by apply Matrix.ext; unfold raw13756step2 raw13756step1; decide +kernel
      have hl : raw13756step1Labels = labelEmbedding1 ∘ raw13756step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13756step1 raw13756step1Labels raw13756step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

def raw13757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw13757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13757step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13757step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13757step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13757 raw13757Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw13757 raw13757Labels = mixedMoment B raw13757step0 raw13757step0Labels := by
      have hz : ∀ j, raw13757 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13757step0 = (fun i j => raw13757 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13757step0 raw13757; decide +kernel
      have hl : raw13757step0Labels = raw13757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13757 raw13757Labels permutation590 hz
    mixedMoment B raw13757step0 raw13757step0Labels = mixedMoment B raw13757step1 raw13757step1Labels := by
      have ha : raw13757step1 = (fun i j => raw13757step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13757step1 raw13757step0; decide +kernel
      have hl : raw13757step1Labels = raw13757step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13757step0 raw13757step0Labels permutation38 permutation7
    mixedMoment B raw13757step1 raw13757step1Labels = mixedMoment B raw13757step2 raw13757step2Labels := by
      have ha : raw13757step2 = -raw13757step1 := by apply Matrix.ext; change ∀ i j, raw13757step2 i j = -(raw13757step1 i j); unfold raw13757step2 raw13757step1; decide +kernel
      have hl : raw13757step2Labels = raw13757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13757step2 raw13757step2Labels = mixedMoment B raw13757step3 raw13757step3Labels := by
      have ha : raw13757step3 = raw13757step2 := by apply Matrix.ext; unfold raw13757step3 raw13757step2; decide +kernel
      have hl : raw13757step2Labels = labelEmbedding1 ∘ raw13757step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13757step2 raw13757step2Labels raw13757step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw13758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13758Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw13758step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13758step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13758step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13758 raw13758Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw13758 raw13758Labels = mixedMoment B raw13758step0 raw13758step0Labels := by
      have ha : raw13758step0 = (fun i j => raw13758 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13758step0 raw13758; decide +kernel
      have hl : raw13758step0Labels = raw13758Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13758 raw13758Labels permutation160 permutation5
    mixedMoment B raw13758step0 raw13758step0Labels = mixedMoment B raw13758step1 raw13758step1Labels := by
      have ha : raw13758step1 = -raw13758step0 := by apply Matrix.ext; change ∀ i j, raw13758step1 i j = -(raw13758step0 i j); unfold raw13758step1 raw13758step0; decide +kernel
      have hl : raw13758step1Labels = raw13758step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13758step1 raw13758step1Labels = mixedMoment B raw13758step2 raw13758step2Labels := by
      have ha : raw13758step2 = raw13758step1 := by apply Matrix.ext; unfold raw13758step2 raw13758step1; decide +kernel
      have hl : raw13758step1Labels = labelEmbedding1 ∘ raw13758step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13758step1 raw13758step1Labels raw13758step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw13759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13759Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13759step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13759step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13759step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13759step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13759step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13759step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13759 raw13759Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw13759 raw13759Labels = mixedMoment B raw13759step0 raw13759step0Labels := by
      have ha : raw13759step0 = (fun i j => raw13759 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13759step0 raw13759; decide +kernel
      have hl : raw13759step0Labels = raw13759Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13759 raw13759Labels permutation194 permutation7
    mixedMoment B raw13759step0 raw13759step0Labels = mixedMoment B raw13759step1 raw13759step1Labels := by
      have ha : raw13759step1 = -raw13759step0 := by apply Matrix.ext; change ∀ i j, raw13759step1 i j = -(raw13759step0 i j); unfold raw13759step1 raw13759step0; decide +kernel
      have hl : raw13759step1Labels = raw13759step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13759step1 raw13759step1Labels = mixedMoment B raw13759step2 raw13759step2Labels := by
      have ha : raw13759step2 = raw13759step1 := by apply Matrix.ext; unfold raw13759step2 raw13759step1; decide +kernel
      have hl : raw13759step1Labels = labelEmbedding1 ∘ raw13759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13759step1 raw13759step1Labels raw13759step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw13760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13760Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13760step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13760step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13760step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13760step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13760 raw13760Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw13760 raw13760Labels = mixedMoment B raw13760step0 raw13760step0Labels := by
      have ha : raw13760step0 = (fun i j => raw13760 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13760step0 raw13760; decide +kernel
      have hl : raw13760step0Labels = raw13760Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13760 raw13760Labels permutation194 permutation7
    mixedMoment B raw13760step0 raw13760step0Labels = mixedMoment B raw13760step1 raw13760step1Labels := by
      have ha : raw13760step1 = -raw13760step0 := by apply Matrix.ext; change ∀ i j, raw13760step1 i j = -(raw13760step0 i j); unfold raw13760step1 raw13760step0; decide +kernel
      have hl : raw13760step1Labels = raw13760step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13760step1 raw13760step1Labels = mixedMoment B raw13760step2 raw13760step2Labels := by
      have ha : raw13760step2 = raw13760step1 := by apply Matrix.ext; unfold raw13760step2 raw13760step1; decide +kernel
      have hl : raw13760step1Labels = labelEmbedding1 ∘ raw13760step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13760step1 raw13760step1Labels raw13760step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

def raw13761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13761Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13761step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13761step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13761step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13761step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13761 raw13761Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw13761 raw13761Labels = mixedMoment B raw13761step0 raw13761step0Labels := by
      have ha : raw13761step0 = (fun i j => raw13761 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13761step0 raw13761; decide +kernel
      have hl : raw13761step0Labels = raw13761Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13761 raw13761Labels permutation194 permutation7
    mixedMoment B raw13761step0 raw13761step0Labels = mixedMoment B raw13761step1 raw13761step1Labels := by
      have ha : raw13761step1 = -raw13761step0 := by apply Matrix.ext; change ∀ i j, raw13761step1 i j = -(raw13761step0 i j); unfold raw13761step1 raw13761step0; decide +kernel
      have hl : raw13761step1Labels = raw13761step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13761step1 raw13761step1Labels = mixedMoment B raw13761step2 raw13761step2Labels := by
      have ha : raw13761step2 = raw13761step1 := by apply Matrix.ext; unfold raw13761step2 raw13761step1; decide +kernel
      have hl : raw13761step1Labels = labelEmbedding1 ∘ raw13761step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13761step1 raw13761step1Labels raw13761step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw13762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw13762Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13762step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13762step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13762step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13762step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13762step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13762 raw13762Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw13762 raw13762Labels = mixedMoment B raw13762step0 raw13762step0Labels := by
      have ha : raw13762step0 = (fun i j => raw13762 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13762step0 raw13762; decide +kernel
      have hl : raw13762step0Labels = raw13762Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13762 raw13762Labels permutation195 permutation7
    mixedMoment B raw13762step0 raw13762step0Labels = mixedMoment B raw13762step1 raw13762step1Labels := by
      have ha : raw13762step1 = -raw13762step0 := by apply Matrix.ext; change ∀ i j, raw13762step1 i j = -(raw13762step0 i j); unfold raw13762step1 raw13762step0; decide +kernel
      have hl : raw13762step1Labels = raw13762step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13762step1 raw13762step1Labels = mixedMoment B raw13762step2 raw13762step2Labels := by
      have ha : raw13762step2 = raw13762step1 := by apply Matrix.ext; unfold raw13762step2 raw13762step1; decide +kernel
      have hl : raw13762step1Labels = labelEmbedding1 ∘ raw13762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13762step1 raw13762step1Labels raw13762step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw13763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13763 raw13763Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw13763 raw13763Labels = mixedMoment B raw13763step0 raw13763step0Labels := by
      have ha : raw13763step0 = (fun i j => raw13763 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13763step0 raw13763; decide +kernel
      have hl : raw13763step0Labels = raw13763Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13763 raw13763Labels permutation194 permutation2
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw13764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13764Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13764step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13764step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13764 raw13764Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13764 raw13764Labels = mixedMoment B raw13764step0 raw13764step0Labels := by
      have ha : raw13764step0 = (fun i j => raw13764 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13764step0 raw13764; decide +kernel
      have hl : raw13764step0Labels = raw13764Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13764 raw13764Labels permutation180 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw13765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13765Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13765step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13765step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13765 raw13765Labels = mixedMoment B node2510 node2510Labels := by
  calc
    mixedMoment B raw13765 raw13765Labels = mixedMoment B raw13765step0 raw13765step0Labels := by
      have ha : raw13765step0 = (fun i j => raw13765 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13765step0 raw13765; decide +kernel
      have hl : raw13765step0Labels = raw13765Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13765 raw13765Labels permutation194 permutation2
    _ = mixedMoment B node2510 node2510Labels := by rfl

def raw13766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13766Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13766step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13766 raw13766Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13766 raw13766Labels = mixedMoment B raw13766step0 raw13766step0Labels := by
      have ha : raw13766step0 = (fun i j => raw13766 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13766step0 raw13766; decide +kernel
      have hl : raw13766step0Labels = raw13766Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13766 raw13766Labels permutation186 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw13767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw13767Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13767step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13767step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13767 raw13767Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13767 raw13767Labels = mixedMoment B raw13767step0 raw13767step0Labels := by
      have ha : raw13767step0 = (fun i j => raw13767 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13767step0 raw13767; decide +kernel
      have hl : raw13767step0Labels = raw13767Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13767 raw13767Labels permutation192 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw13768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw13768Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13768step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13768step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13768 raw13768Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw13768 raw13768Labels = mixedMoment B raw13768step0 raw13768step0Labels := by
      have hz : ∀ j, raw13768 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13768step0 = (fun i j => raw13768 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13768step0 raw13768; decide +kernel
      have hl : raw13768step0Labels = raw13768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13768 raw13768Labels permutation590 hz
    mixedMoment B raw13768step0 raw13768step0Labels = mixedMoment B raw13768step1 raw13768step1Labels := by
      have ha : raw13768step1 = (fun i j => raw13768step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13768step1 raw13768step0; decide +kernel
      have hl : raw13768step1Labels = raw13768step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13768step0 raw13768step0Labels permutation38 permutation2
    _ = mixedMoment B node2741 node2741Labels := by rfl

def raw13769 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![0, 0]]
def raw13769Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13769step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw13769step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13769step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw13769step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical13769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13769 raw13769Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13769 raw13769Labels = mixedMoment B raw13769step0 raw13769step0Labels := by
      have hz : ∀ j, raw13769 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13769step0 = (fun i j => raw13769 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13769step0 raw13769; decide +kernel
      have hl : raw13769step0Labels = raw13769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13769 raw13769Labels permutation590 hz
    mixedMoment B raw13769step0 raw13769step0Labels = mixedMoment B raw13769step1 raw13769step1Labels := by
      have ha : raw13769step1 = (fun i j => raw13769step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13769step1 raw13769step0; decide +kernel
      have hl : raw13769step1Labels = raw13769step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13769step0 raw13769step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw13770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13770Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13770step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13770step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13770 raw13770Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw13770 raw13770Labels = mixedMoment B raw13770step0 raw13770step0Labels := by
      have ha : raw13770step0 = (fun i j => raw13770 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13770step0 raw13770; decide +kernel
      have hl : raw13770step0Labels = raw13770Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13770 raw13770Labels permutation156 permutation2
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw13771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13771Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13771step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13771 raw13771Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw13771 raw13771Labels = mixedMoment B raw13771step0 raw13771step0Labels := by
      have ha : raw13771step0 = (fun i j => raw13771 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13771step0 raw13771; decide +kernel
      have hl : raw13771step0Labels = raw13771Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13771 raw13771Labels permutation156 permutation2
    _ = mixedMoment B node2631 node2631Labels := by rfl

def raw13772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw13772Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13772step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13772 raw13772Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw13772 raw13772Labels = mixedMoment B raw13772step0 raw13772step0Labels := by
      have ha : raw13772step0 = (fun i j => raw13772 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13772step0 raw13772; decide +kernel
      have hl : raw13772step0Labels = raw13772Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13772 raw13772Labels permutation157 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

def raw13773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw13773Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13773step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13773 raw13773Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw13773 raw13773Labels = mixedMoment B raw13773step0 raw13773step0Labels := by
      have ha : raw13773step0 = (fun i j => raw13773 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13773step0 raw13773; decide +kernel
      have hl : raw13773step0Labels = raw13773Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13773 raw13773Labels permutation156 permutation2
    _ = mixedMoment B node2615 node2615Labels := by rfl

def raw13774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13774Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13774 raw13774Labels = mixedMoment B node2617 node2617Labels := by
  calc
    _ = mixedMoment B node2617 node2617Labels := by rfl

def raw13775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13775 raw13775Labels = mixedMoment B node5482 node5482Labels := by
  calc
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw13776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13776step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13776step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13776step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13776 raw13776Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw13776 raw13776Labels = mixedMoment B raw13776step0 raw13776step0Labels := by
      have ha : raw13776step0 = (fun i j => raw13776 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13776step0 raw13776; decide +kernel
      have hl : raw13776step0Labels = raw13776Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13776 raw13776Labels permutation180 permutation3
    mixedMoment B raw13776step0 raw13776step0Labels = mixedMoment B raw13776step1 raw13776step1Labels := by
      have ha : raw13776step1 = raw13776step0 := by apply Matrix.ext; unfold raw13776step1 raw13776step0; decide +kernel
      have hl : raw13776step0Labels = labelEmbedding6 ∘ raw13776step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13776step0 raw13776step0Labels raw13776step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw13777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13777 raw13777Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw13777 raw13777Labels = mixedMoment B raw13777step0 raw13777step0Labels := by
      have hz : ∀ j, raw13777 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13777step0 = (fun i j => raw13777 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13777step0 raw13777; decide +kernel
      have hl : raw13777step0Labels = raw13777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13777 raw13777Labels permutation434 hz
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw13778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13778 raw13778Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw13778 raw13778Labels = mixedMoment B raw13778step0 raw13778step0Labels := by
      have hz : ∀ j, raw13778 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13778step0 = (fun i j => raw13778 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13778step0 raw13778; decide +kernel
      have hl : raw13778step0Labels = raw13778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13778 raw13778Labels permutation520 hz
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw13779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13779step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13779step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13779step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13779 raw13779Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw13779 raw13779Labels = mixedMoment B raw13779step0 raw13779step0Labels := by
      have ha : raw13779step0 = (fun i j => raw13779 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13779step0 raw13779; decide +kernel
      have hl : raw13779step0Labels = raw13779Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13779 raw13779Labels permutation194 permutation3
    mixedMoment B raw13779step0 raw13779step0Labels = mixedMoment B raw13779step1 raw13779step1Labels := by
      have ha : raw13779step1 = raw13779step0 := by apply Matrix.ext; unfold raw13779step1 raw13779step0; decide +kernel
      have hl : raw13779step0Labels = labelEmbedding6 ∘ raw13779step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13779step0 raw13779step0Labels raw13779step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw13780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13780step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13780step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13780step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13780 raw13780Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw13780 raw13780Labels = mixedMoment B raw13780step0 raw13780step0Labels := by
      have ha : raw13780step0 = (fun i j => raw13780 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13780step0 raw13780; decide +kernel
      have hl : raw13780step0Labels = raw13780Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13780 raw13780Labels permutation197 permutation3
    mixedMoment B raw13780step0 raw13780step0Labels = mixedMoment B raw13780step1 raw13780step1Labels := by
      have ha : raw13780step1 = raw13780step0 := by apply Matrix.ext; unfold raw13780step1 raw13780step0; decide +kernel
      have hl : raw13780step0Labels = labelEmbedding6 ∘ raw13780step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13780step0 raw13780step0Labels raw13780step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw13781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13781step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13781step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13781 raw13781Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw13781 raw13781Labels = mixedMoment B raw13781step0 raw13781step0Labels := by
      have ha : raw13781step0 = (fun i j => raw13781 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13781step0 raw13781; decide +kernel
      have hl : raw13781step0Labels = raw13781Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13781 raw13781Labels permutation197 permutation3
    mixedMoment B raw13781step0 raw13781step0Labels = mixedMoment B raw13781step1 raw13781step1Labels := by
      have ha : raw13781step1 = raw13781step0 := by apply Matrix.ext; unfold raw13781step1 raw13781step0; decide +kernel
      have hl : raw13781step0Labels = labelEmbedding6 ∘ raw13781step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13781step0 raw13781step0Labels raw13781step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw13782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13782step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13782step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13782step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13782 raw13782Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw13782 raw13782Labels = mixedMoment B raw13782step0 raw13782step0Labels := by
      have hz : ∀ j, raw13782 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13782step0 = (fun i j => raw13782 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13782step0 raw13782; decide +kernel
      have hl : raw13782step0Labels = raw13782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13782 raw13782Labels permutation434 hz
    mixedMoment B raw13782step0 raw13782step0Labels = mixedMoment B raw13782step1 raw13782step1Labels := by
      have ha : raw13782step1 = (fun i j => raw13782step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13782step1 raw13782step0; decide +kernel
      have hl : raw13782step1Labels = raw13782step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13782step0 raw13782step0Labels permutation43 permutation3
    mixedMoment B raw13782step1 raw13782step1Labels = mixedMoment B raw13782step2 raw13782step2Labels := by
      have ha : raw13782step2 = raw13782step1 := by apply Matrix.ext; unfold raw13782step2 raw13782step1; decide +kernel
      have hl : raw13782step1Labels = labelEmbedding6 ∘ raw13782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13782step1 raw13782step1Labels raw13782step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw13783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13783step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13783step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13783 raw13783Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw13783 raw13783Labels = mixedMoment B raw13783step0 raw13783step0Labels := by
      have hz : ∀ j, raw13783 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13783step0 = (fun i j => raw13783 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13783step0 raw13783; decide +kernel
      have hl : raw13783step0Labels = raw13783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13783 raw13783Labels permutation520 hz
    mixedMoment B raw13783step0 raw13783step0Labels = mixedMoment B raw13783step1 raw13783step1Labels := by
      have ha : raw13783step1 = (fun i j => raw13783step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13783step1 raw13783step0; decide +kernel
      have hl : raw13783step1Labels = raw13783step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13783step0 raw13783step0Labels permutation43 permutation3
    mixedMoment B raw13783step1 raw13783step1Labels = mixedMoment B raw13783step2 raw13783step2Labels := by
      have ha : raw13783step2 = raw13783step1 := by apply Matrix.ext; unfold raw13783step2 raw13783step1; decide +kernel
      have hl : raw13783step1Labels = labelEmbedding6 ∘ raw13783step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13783step1 raw13783step1Labels raw13783step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw13784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13784step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13784step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13784step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13784 raw13784Labels = mixedMoment B node5247 node5247Labels := by
  calc
    mixedMoment B raw13784 raw13784Labels = mixedMoment B raw13784step0 raw13784step0Labels := by
      have ha : raw13784step0 = (fun i j => raw13784 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13784step0 raw13784; decide +kernel
      have hl : raw13784step0Labels = raw13784Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13784 raw13784Labels permutation197 permutation3
    mixedMoment B raw13784step0 raw13784step0Labels = mixedMoment B raw13784step1 raw13784step1Labels := by
      have ha : raw13784step1 = raw13784step0 := by apply Matrix.ext; unfold raw13784step1 raw13784step0; decide +kernel
      have hl : raw13784step0Labels = labelEmbedding6 ∘ raw13784step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13784step0 raw13784step0Labels raw13784step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw13785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13785step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13785step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13785 raw13785Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw13785 raw13785Labels = mixedMoment B raw13785step0 raw13785step0Labels := by
      have ha : raw13785step0 = (fun i j => raw13785 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13785step0 raw13785; decide +kernel
      have hl : raw13785step0Labels = raw13785Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13785 raw13785Labels permutation156 permutation3
    mixedMoment B raw13785step0 raw13785step0Labels = mixedMoment B raw13785step1 raw13785step1Labels := by
      have ha : raw13785step1 = raw13785step0 := by apply Matrix.ext; unfold raw13785step1 raw13785step0; decide +kernel
      have hl : raw13785step0Labels = labelEmbedding6 ∘ raw13785step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13785step0 raw13785step0Labels raw13785step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw13786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13786step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13786 raw13786Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw13786 raw13786Labels = mixedMoment B raw13786step0 raw13786step0Labels := by
      have ha : raw13786step0 = (fun i j => raw13786 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13786step0 raw13786; decide +kernel
      have hl : raw13786step0Labels = raw13786Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13786 raw13786Labels permutation156 permutation3
    mixedMoment B raw13786step0 raw13786step0Labels = mixedMoment B raw13786step1 raw13786step1Labels := by
      have ha : raw13786step1 = raw13786step0 := by apply Matrix.ext; unfold raw13786step1 raw13786step0; decide +kernel
      have hl : raw13786step0Labels = labelEmbedding6 ∘ raw13786step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13786step0 raw13786step0Labels raw13786step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw13787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13787step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13787step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13787 raw13787Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13787 raw13787Labels = mixedMoment B raw13787step0 raw13787step0Labels := by
      have hz : ∀ j, raw13787 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13787step0 = (fun i j => raw13787 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13787step0 raw13787; decide +kernel
      have hl : raw13787step0Labels = raw13787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13787 raw13787Labels permutation434 hz
    mixedMoment B raw13787step0 raw13787step0Labels = mixedMoment B raw13787step1 raw13787step1Labels := by
      have ha : raw13787step1 = (fun i j => raw13787step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13787step1 raw13787step0; decide +kernel
      have hl : raw13787step1Labels = raw13787step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13787step0 raw13787step0Labels permutation33 permutation3
    mixedMoment B raw13787step1 raw13787step1Labels = mixedMoment B raw13787step2 raw13787step2Labels := by
      have ha : raw13787step2 = raw13787step1 := by apply Matrix.ext; unfold raw13787step2 raw13787step1; decide +kernel
      have hl : raw13787step1Labels = labelEmbedding6 ∘ raw13787step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13787step1 raw13787step1Labels raw13787step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw13788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13788step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13788 raw13788Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw13788 raw13788Labels = mixedMoment B raw13788step0 raw13788step0Labels := by
      have hz : ∀ j, raw13788 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13788step0 = (fun i j => raw13788 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13788step0 raw13788; decide +kernel
      have hl : raw13788step0Labels = raw13788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13788 raw13788Labels permutation520 hz
    mixedMoment B raw13788step0 raw13788step0Labels = mixedMoment B raw13788step1 raw13788step1Labels := by
      have ha : raw13788step1 = (fun i j => raw13788step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13788step1 raw13788step0; decide +kernel
      have hl : raw13788step1Labels = raw13788step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13788step0 raw13788step0Labels permutation33 permutation3
    mixedMoment B raw13788step1 raw13788step1Labels = mixedMoment B raw13788step2 raw13788step2Labels := by
      have ha : raw13788step2 = raw13788step1 := by apply Matrix.ext; unfold raw13788step2 raw13788step1; decide +kernel
      have hl : raw13788step1Labels = labelEmbedding6 ∘ raw13788step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13788step1 raw13788step1Labels raw13788step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw13789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13789step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13789step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13789 raw13789Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13789 raw13789Labels = mixedMoment B raw13789step0 raw13789step0Labels := by
      have ha : raw13789step0 = (fun i j => raw13789 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13789step0 raw13789; decide +kernel
      have hl : raw13789step0Labels = raw13789Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13789 raw13789Labels permutation246 permutation3
    mixedMoment B raw13789step0 raw13789step0Labels = mixedMoment B raw13789step1 raw13789step1Labels := by
      have ha : raw13789step1 = raw13789step0 := by apply Matrix.ext; unfold raw13789step1 raw13789step0; decide +kernel
      have hl : raw13789step0Labels = labelEmbedding6 ∘ raw13789step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13789step0 raw13789step0Labels raw13789step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw13790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13790step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13790step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13790step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13790 raw13790Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw13790 raw13790Labels = mixedMoment B raw13790step0 raw13790step0Labels := by
      have ha : raw13790step0 = (fun i j => raw13790 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13790step0 raw13790; decide +kernel
      have hl : raw13790step0Labels = raw13790Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13790 raw13790Labels permutation181 permutation3
    mixedMoment B raw13790step0 raw13790step0Labels = mixedMoment B raw13790step1 raw13790step1Labels := by
      have ha : raw13790step1 = raw13790step0 := by apply Matrix.ext; unfold raw13790step1 raw13790step0; decide +kernel
      have hl : raw13790step0Labels = labelEmbedding6 ∘ raw13790step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13790step0 raw13790step0Labels raw13790step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw13791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13791step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13791 raw13791Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw13791 raw13791Labels = mixedMoment B raw13791step0 raw13791step0Labels := by
      have ha : raw13791step0 = (fun i j => raw13791 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13791step0 raw13791; decide +kernel
      have hl : raw13791step0Labels = raw13791Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13791 raw13791Labels permutation157 permutation3
    mixedMoment B raw13791step0 raw13791step0Labels = mixedMoment B raw13791step1 raw13791step1Labels := by
      have ha : raw13791step1 = raw13791step0 := by apply Matrix.ext; unfold raw13791step1 raw13791step0; decide +kernel
      have hl : raw13791step0Labels = labelEmbedding6 ∘ raw13791step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13791step0 raw13791step0Labels raw13791step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw13792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13792step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13792 raw13792Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw13792 raw13792Labels = mixedMoment B raw13792step0 raw13792step0Labels := by
      have ha : raw13792step0 = (fun i j => raw13792 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13792step0 raw13792; decide +kernel
      have hl : raw13792step0Labels = raw13792Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13792 raw13792Labels permutation181 permutation3
    mixedMoment B raw13792step0 raw13792step0Labels = mixedMoment B raw13792step1 raw13792step1Labels := by
      have ha : raw13792step1 = raw13792step0 := by apply Matrix.ext; unfold raw13792step1 raw13792step0; decide +kernel
      have hl : raw13792step0Labels = labelEmbedding6 ∘ raw13792step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13792step0 raw13792step0Labels raw13792step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw13793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw13793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13793step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13793 raw13793Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw13793 raw13793Labels = mixedMoment B raw13793step0 raw13793step0Labels := by
      have hz : ∀ j, raw13793 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13793step0 = (fun i j => raw13793 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13793step0 raw13793; decide +kernel
      have hl : raw13793step0Labels = raw13793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13793 raw13793Labels permutation520 hz
    mixedMoment B raw13793step0 raw13793step0Labels = mixedMoment B raw13793step1 raw13793step1Labels := by
      have ha : raw13793step1 = (fun i j => raw13793step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13793step1 raw13793step0; decide +kernel
      have hl : raw13793step1Labels = raw13793step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13793step0 raw13793step0Labels permutation39 permutation3
    mixedMoment B raw13793step1 raw13793step1Labels = mixedMoment B raw13793step2 raw13793step2Labels := by
      have ha : raw13793step2 = raw13793step1 := by apply Matrix.ext; unfold raw13793step2 raw13793step1; decide +kernel
      have hl : raw13793step1Labels = labelEmbedding6 ∘ raw13793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13793step1 raw13793step1Labels raw13793step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw13794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13794step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13794step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13794 raw13794Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw13794 raw13794Labels = mixedMoment B raw13794step0 raw13794step0Labels := by
      have ha : raw13794step0 = (fun i j => raw13794 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13794step0 raw13794; decide +kernel
      have hl : raw13794step0Labels = raw13794Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13794 raw13794Labels permutation195 permutation3
    mixedMoment B raw13794step0 raw13794step0Labels = mixedMoment B raw13794step1 raw13794step1Labels := by
      have ha : raw13794step1 = raw13794step0 := by apply Matrix.ext; unfold raw13794step1 raw13794step0; decide +kernel
      have hl : raw13794step0Labels = labelEmbedding6 ∘ raw13794step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13794step0 raw13794step0Labels raw13794step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw13795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13795step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13795 raw13795Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw13795 raw13795Labels = mixedMoment B raw13795step0 raw13795step0Labels := by
      have ha : raw13795step0 = (fun i j => raw13795 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13795step0 raw13795; decide +kernel
      have hl : raw13795step0Labels = raw13795Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13795 raw13795Labels permutation180 permutation3
    mixedMoment B raw13795step0 raw13795step0Labels = mixedMoment B raw13795step1 raw13795step1Labels := by
      have ha : raw13795step1 = raw13795step0 := by apply Matrix.ext; unfold raw13795step1 raw13795step0; decide +kernel
      have hl : raw13795step0Labels = labelEmbedding6 ∘ raw13795step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13795step0 raw13795step0Labels raw13795step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw13796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13796step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13796 raw13796Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw13796 raw13796Labels = mixedMoment B raw13796step0 raw13796step0Labels := by
      have ha : raw13796step0 = (fun i j => raw13796 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13796step0 raw13796; decide +kernel
      have hl : raw13796step0Labels = raw13796Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13796 raw13796Labels permutation156 permutation3
    mixedMoment B raw13796step0 raw13796step0Labels = mixedMoment B raw13796step1 raw13796step1Labels := by
      have ha : raw13796step1 = raw13796step0 := by apply Matrix.ext; unfold raw13796step1 raw13796step0; decide +kernel
      have hl : raw13796step0Labels = labelEmbedding6 ∘ raw13796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13796step0 raw13796step0Labels raw13796step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw13797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13797 raw13797Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw13797 raw13797Labels = mixedMoment B raw13797step0 raw13797step0Labels := by
      have ha : raw13797step0 = (fun i j => raw13797 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13797step0 raw13797; decide +kernel
      have hl : raw13797step0Labels = raw13797Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13797 raw13797Labels permutation180 permutation3
    mixedMoment B raw13797step0 raw13797step0Labels = mixedMoment B raw13797step1 raw13797step1Labels := by
      have ha : raw13797step1 = raw13797step0 := by apply Matrix.ext; unfold raw13797step1 raw13797step0; decide +kernel
      have hl : raw13797step0Labels = labelEmbedding6 ∘ raw13797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13797step0 raw13797step0Labels raw13797step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw13798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw13798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw13798step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13798step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13798step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13798 raw13798Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw13798 raw13798Labels = mixedMoment B raw13798step0 raw13798step0Labels := by
      have hz : ∀ j, raw13798 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13798step0 = (fun i j => raw13798 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13798step0 raw13798; decide +kernel
      have hl : raw13798step0Labels = raw13798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13798 raw13798Labels permutation434 hz
    mixedMoment B raw13798step0 raw13798step0Labels = mixedMoment B raw13798step1 raw13798step1Labels := by
      have ha : raw13798step1 = (fun i j => raw13798step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13798step1 raw13798step0; decide +kernel
      have hl : raw13798step1Labels = raw13798step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13798step0 raw13798step0Labels permutation39 permutation3
    mixedMoment B raw13798step1 raw13798step1Labels = mixedMoment B raw13798step2 raw13798step2Labels := by
      have ha : raw13798step2 = raw13798step1 := by apply Matrix.ext; unfold raw13798step2 raw13798step1; decide +kernel
      have hl : raw13798step1Labels = labelEmbedding6 ∘ raw13798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13798step1 raw13798step1Labels raw13798step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw13799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw13799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13799step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw13799step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13799 raw13799Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw13799 raw13799Labels = mixedMoment B raw13799step0 raw13799step0Labels := by
      have ha : raw13799step0 = (fun i j => raw13799 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13799step0 raw13799; decide +kernel
      have hl : raw13799step0Labels = raw13799Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13799 raw13799Labels permutation194 permutation3
    mixedMoment B raw13799step0 raw13799step0Labels = mixedMoment B raw13799step1 raw13799step1Labels := by
      have ha : raw13799step1 = raw13799step0 := by apply Matrix.ext; unfold raw13799step1 raw13799step0; decide +kernel
      have hl : raw13799step0Labels = labelEmbedding6 ∘ raw13799step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13799step0 raw13799step0Labels raw13799step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw13800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13800step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13800step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13800 raw13800Labels = mixedMoment B node4399 node4399Labels := by
  calc
    mixedMoment B raw13800 raw13800Labels = mixedMoment B raw13800step0 raw13800step0Labels := by
      have ha : raw13800step0 = (fun i j => raw13800 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13800step0 raw13800; decide +kernel
      have hl : raw13800step0Labels = raw13800Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13800 raw13800Labels permutation176 permutation3
    mixedMoment B raw13800step0 raw13800step0Labels = mixedMoment B raw13800step1 raw13800step1Labels := by
      have ha : raw13800step1 = raw13800step0 := by apply Matrix.ext; unfold raw13800step1 raw13800step0; decide +kernel
      have hl : raw13800step0Labels = labelEmbedding6 ∘ raw13800step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13800step0 raw13800step0Labels raw13800step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4399 node4399Labels := by rfl

def raw13801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13801 raw13801Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw13801 raw13801Labels = mixedMoment B raw13801step0 raw13801step0Labels := by
      have ha : raw13801step0 = (fun i j => raw13801 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13801step0 raw13801; decide +kernel
      have hl : raw13801step0Labels = raw13801Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13801 raw13801Labels permutation152 permutation3
    mixedMoment B raw13801step0 raw13801step0Labels = mixedMoment B raw13801step1 raw13801step1Labels := by
      have ha : raw13801step1 = raw13801step0 := by apply Matrix.ext; unfold raw13801step1 raw13801step0; decide +kernel
      have hl : raw13801step0Labels = labelEmbedding6 ∘ raw13801step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13801step0 raw13801step0Labels raw13801step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw13802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13802step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13802step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13802step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13802step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13802 raw13802Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw13802 raw13802Labels = mixedMoment B raw13802step0 raw13802step0Labels := by
      have ha : raw13802step0 = (fun i j => raw13802 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13802step0 raw13802; decide +kernel
      have hl : raw13802step0Labels = raw13802Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13802 raw13802Labels permutation176 permutation3
    mixedMoment B raw13802step0 raw13802step0Labels = mixedMoment B raw13802step1 raw13802step1Labels := by
      have ha : raw13802step1 = raw13802step0 := by apply Matrix.ext; unfold raw13802step1 raw13802step0; decide +kernel
      have hl : raw13802step0Labels = labelEmbedding6 ∘ raw13802step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13802step0 raw13802step0Labels raw13802step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4998 node4998Labels := by rfl

def raw13803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13803step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13803step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13803 raw13803Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw13803 raw13803Labels = mixedMoment B raw13803step0 raw13803step0Labels := by
      have hz : ∀ j, raw13803 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13803step0 = (fun i j => raw13803 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13803step0 raw13803; decide +kernel
      have hl : raw13803step0Labels = raw13803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13803 raw13803Labels permutation434 hz
    mixedMoment B raw13803step0 raw13803step0Labels = mixedMoment B raw13803step1 raw13803step1Labels := by
      have ha : raw13803step1 = (fun i j => raw13803step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13803step1 raw13803step0; decide +kernel
      have hl : raw13803step1Labels = raw13803step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13803step0 raw13803step0Labels permutation38 permutation3
    mixedMoment B raw13803step1 raw13803step1Labels = mixedMoment B raw13803step2 raw13803step2Labels := by
      have ha : raw13803step2 = raw13803step1 := by apply Matrix.ext; unfold raw13803step2 raw13803step1; decide +kernel
      have hl : raw13803step1Labels = labelEmbedding6 ∘ raw13803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13803step1 raw13803step1Labels raw13803step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw13804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw13804Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13804step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13804step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13804step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13804 raw13804Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw13804 raw13804Labels = mixedMoment B raw13804step0 raw13804step0Labels := by
      have hz : ∀ j, raw13804 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13804step0 = (fun i j => raw13804 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13804step0 raw13804; decide +kernel
      have hl : raw13804step0Labels = raw13804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13804 raw13804Labels permutation520 hz
    mixedMoment B raw13804step0 raw13804step0Labels = mixedMoment B raw13804step1 raw13804step1Labels := by
      have ha : raw13804step1 = (fun i j => raw13804step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13804step1 raw13804step0; decide +kernel
      have hl : raw13804step1Labels = raw13804step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13804step0 raw13804step0Labels permutation38 permutation3
    mixedMoment B raw13804step1 raw13804step1Labels = mixedMoment B raw13804step2 raw13804step2Labels := by
      have ha : raw13804step2 = raw13804step1 := by apply Matrix.ext; unfold raw13804step2 raw13804step1; decide +kernel
      have hl : raw13804step1Labels = labelEmbedding6 ∘ raw13804step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13804step1 raw13804step1Labels raw13804step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw13805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13805 raw13805Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw13805 raw13805Labels = mixedMoment B raw13805step0 raw13805step0Labels := by
      have ha : raw13805step0 = (fun i j => raw13805 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13805step0 raw13805; decide +kernel
      have hl : raw13805step0Labels = raw13805Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13805 raw13805Labels permutation156 permutation3
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw13806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13806 raw13806Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw13806 raw13806Labels = mixedMoment B raw13806step0 raw13806step0Labels := by
      have ha : raw13806step0 = (fun i j => raw13806 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13806step0 raw13806; decide +kernel
      have hl : raw13806step0Labels = raw13806Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13806 raw13806Labels permutation180 permutation3
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw13807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13807 raw13807Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw13807 raw13807Labels = mixedMoment B raw13807step0 raw13807step0Labels := by
      have hz : ∀ j, raw13807 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13807step0 = (fun i j => raw13807 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13807step0 raw13807; decide +kernel
      have hl : raw13807step0Labels = raw13807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13807 raw13807Labels permutation434 hz
    mixedMoment B raw13807step0 raw13807step0Labels = mixedMoment B raw13807step1 raw13807step1Labels := by
      have ha : raw13807step1 = (fun i j => raw13807step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13807step1 raw13807step0; decide +kernel
      have hl : raw13807step1Labels = raw13807step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13807step0 raw13807step0Labels permutation39 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw13808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13808step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13808step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13808step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13808 raw13808Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw13808 raw13808Labels = mixedMoment B raw13808step0 raw13808step0Labels := by
      have hz : ∀ j, raw13808 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13808step0 = (fun i j => raw13808 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13808step0 raw13808; decide +kernel
      have hl : raw13808step0Labels = raw13808Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13808 raw13808Labels permutation520 hz
    mixedMoment B raw13808step0 raw13808step0Labels = mixedMoment B raw13808step1 raw13808step1Labels := by
      have ha : raw13808step1 = (fun i j => raw13808step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13808step1 raw13808step0; decide +kernel
      have hl : raw13808step1Labels = raw13808step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13808step0 raw13808step0Labels permutation39 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw13809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13809 raw13809Labels = mixedMoment B node4009 node4009Labels := by
  calc
    mixedMoment B raw13809 raw13809Labels = mixedMoment B raw13809step0 raw13809step0Labels := by
      have ha : raw13809step0 = (fun i j => raw13809 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13809step0 raw13809; decide +kernel
      have hl : raw13809step0Labels = raw13809Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13809 raw13809Labels permutation194 permutation3
    _ = mixedMoment B node4009 node4009Labels := by rfl

def raw13810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13810 raw13810Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw13810 raw13810Labels = mixedMoment B raw13810step0 raw13810step0Labels := by
      have ha : raw13810step0 = (fun i j => raw13810 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13810step0 raw13810; decide +kernel
      have hl : raw13810step0Labels = raw13810Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13810 raw13810Labels permutation197 permutation3
    _ = mixedMoment B node998 node998Labels := by rfl

def raw13811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13811 raw13811Labels = mixedMoment B node2398 node2398Labels := by
  calc
    mixedMoment B raw13811 raw13811Labels = mixedMoment B raw13811step0 raw13811step0Labels := by
      have ha : raw13811step0 = (fun i j => raw13811 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13811step0 raw13811; decide +kernel
      have hl : raw13811step0Labels = raw13811Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13811 raw13811Labels permutation197 permutation3
    _ = mixedMoment B node2398 node2398Labels := by rfl

def raw13812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13812 raw13812Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw13812 raw13812Labels = mixedMoment B raw13812step0 raw13812step0Labels := by
      have hz : ∀ j, raw13812 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13812step0 = (fun i j => raw13812 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13812step0 raw13812; decide +kernel
      have hl : raw13812step0Labels = raw13812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13812 raw13812Labels permutation434 hz
    mixedMoment B raw13812step0 raw13812step0Labels = mixedMoment B raw13812step1 raw13812step1Labels := by
      have ha : raw13812step1 = (fun i j => raw13812step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13812step1 raw13812step0; decide +kernel
      have hl : raw13812step1Labels = raw13812step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13812step0 raw13812step0Labels permutation43 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw13813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13813step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13813 raw13813Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw13813 raw13813Labels = mixedMoment B raw13813step0 raw13813step0Labels := by
      have hz : ∀ j, raw13813 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13813step0 = (fun i j => raw13813 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13813step0 raw13813; decide +kernel
      have hl : raw13813step0Labels = raw13813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13813 raw13813Labels permutation520 hz
    mixedMoment B raw13813step0 raw13813step0Labels = mixedMoment B raw13813step1 raw13813step1Labels := by
      have ha : raw13813step1 = (fun i j => raw13813step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13813step1 raw13813step0; decide +kernel
      have hl : raw13813step1Labels = raw13813step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13813step0 raw13813step0Labels permutation43 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw13814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13814 raw13814Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw13814 raw13814Labels = mixedMoment B raw13814step0 raw13814step0Labels := by
      have ha : raw13814step0 = (fun i j => raw13814 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13814step0 raw13814; decide +kernel
      have hl : raw13814step0Labels = raw13814Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13814 raw13814Labels permutation197 permutation3
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw13815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13815step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13815 raw13815Labels = mixedMoment B node1039 node1039Labels := by
  calc
    mixedMoment B raw13815 raw13815Labels = mixedMoment B raw13815step0 raw13815step0Labels := by
      have ha : raw13815step0 = (fun i j => raw13815 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13815step0 raw13815; decide +kernel
      have hl : raw13815step0Labels = raw13815Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13815 raw13815Labels permutation156 permutation3
    _ = mixedMoment B node1039 node1039Labels := by rfl

def raw13816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13816step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13816 raw13816Labels = mixedMoment B node2593 node2593Labels := by
  calc
    mixedMoment B raw13816 raw13816Labels = mixedMoment B raw13816step0 raw13816step0Labels := by
      have ha : raw13816step0 = (fun i j => raw13816 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13816step0 raw13816; decide +kernel
      have hl : raw13816step0Labels = raw13816Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13816 raw13816Labels permutation156 permutation3
    _ = mixedMoment B node2593 node2593Labels := by rfl

def raw13817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13817Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13817step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13817 raw13817Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw13817 raw13817Labels = mixedMoment B raw13817step0 raw13817step0Labels := by
      have hz : ∀ j, raw13817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw13817step0 = (fun i j => raw13817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw13817step0 raw13817; decide +kernel
      have hl : raw13817step0Labels = raw13817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13817 raw13817Labels permutation434 hz
    mixedMoment B raw13817step0 raw13817step0Labels = mixedMoment B raw13817step1 raw13817step1Labels := by
      have ha : raw13817step1 = (fun i j => raw13817step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13817step1 raw13817step0; decide +kernel
      have hl : raw13817step1Labels = raw13817step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13817step0 raw13817step0Labels permutation33 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw13818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13818Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13818step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13818step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13818 raw13818Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw13818 raw13818Labels = mixedMoment B raw13818step0 raw13818step0Labels := by
      have hz : ∀ j, raw13818 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13818step0 = (fun i j => raw13818 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13818step0 raw13818; decide +kernel
      have hl : raw13818step0Labels = raw13818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13818 raw13818Labels permutation520 hz
    mixedMoment B raw13818step0 raw13818step0Labels = mixedMoment B raw13818step1 raw13818step1Labels := by
      have ha : raw13818step1 = (fun i j => raw13818step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13818step1 raw13818step0; decide +kernel
      have hl : raw13818step1Labels = raw13818step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13818step0 raw13818step0Labels permutation33 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw13819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw13819Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13819step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13819 raw13819Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13819 raw13819Labels = mixedMoment B raw13819step0 raw13819step0Labels := by
      have ha : raw13819step0 = (fun i j => raw13819 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13819step0 raw13819; decide +kernel
      have hl : raw13819step0Labels = raw13819Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13819 raw13819Labels permutation246 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw13820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13820Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13820step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13820step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13820 raw13820Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw13820 raw13820Labels = mixedMoment B raw13820step0 raw13820step0Labels := by
      have ha : raw13820step0 = (fun i j => raw13820 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13820step0 raw13820; decide +kernel
      have hl : raw13820step0Labels = raw13820Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13820 raw13820Labels permutation181 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

def raw13821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13821Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13821step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13821step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13821 raw13821Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw13821 raw13821Labels = mixedMoment B raw13821step0 raw13821step0Labels := by
      have ha : raw13821step0 = (fun i j => raw13821 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13821step0 raw13821; decide +kernel
      have hl : raw13821step0Labels = raw13821Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13821 raw13821Labels permutation157 permutation3
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw13822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13822Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13822step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13822 raw13822Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw13822 raw13822Labels = mixedMoment B raw13822step0 raw13822step0Labels := by
      have ha : raw13822step0 = (fun i j => raw13822 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13822step0 raw13822; decide +kernel
      have hl : raw13822step0Labels = raw13822Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13822 raw13822Labels permutation181 permutation3
    _ = mixedMoment B node2382 node2382Labels := by rfl

def raw13823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw13823Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw13823step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13823step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13823 raw13823Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw13823 raw13823Labels = mixedMoment B raw13823step0 raw13823step0Labels := by
      have hz : ∀ j, raw13823 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13823step0 = (fun i j => raw13823 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13823step0 raw13823; decide +kernel
      have hl : raw13823step0Labels = raw13823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13823 raw13823Labels permutation520 hz
    mixedMoment B raw13823step0 raw13823step0Labels = mixedMoment B raw13823step1 raw13823step1Labels := by
      have ha : raw13823step1 = (fun i j => raw13823step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13823step1 raw13823step0; decide +kernel
      have hl : raw13823step1Labels = raw13823step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13823step0 raw13823step0Labels permutation39 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
