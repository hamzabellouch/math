import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw34944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34944step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34944 raw34944Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw34944 raw34944Labels = mixedMoment B raw34944step0 raw34944step0Labels := by
      have hz : ∀ j, raw34944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34944step0 = (fun i j => raw34944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34944step0 raw34944; decide +kernel
      have hl : raw34944step0Labels = raw34944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34944 raw34944Labels permutation346 hz
    mixedMoment B raw34944step0 raw34944step0Labels = mixedMoment B raw34944step1 raw34944step1Labels := by
      have ha : raw34944step1 = (fun i j => raw34944step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34944step1 raw34944step0; decide +kernel
      have hl : raw34944step1Labels = raw34944step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34944step0 raw34944step0Labels permutation126 permutation2
    mixedMoment B raw34944step1 raw34944step1Labels = mixedMoment B raw34944step2 raw34944step2Labels := by
      have ha : raw34944step2 = -raw34944step1 := by apply Matrix.ext; change ∀ i j, raw34944step2 i j = -(raw34944step1 i j); unfold raw34944step2 raw34944step1; decide +kernel
      have hl : raw34944step2Labels = raw34944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw34945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw34945step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw34945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34945 raw34945Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw34945 raw34945Labels = mixedMoment B raw34945step0 raw34945step0Labels := by
      have hz : ∀ j, raw34945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34945step0 = (fun i j => raw34945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34945step0 raw34945; decide +kernel
      have hl : raw34945step0Labels = raw34945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34945 raw34945Labels permutation346 hz
    mixedMoment B raw34945step0 raw34945step0Labels = mixedMoment B raw34945step1 raw34945step1Labels := by
      have ha : raw34945step1 = (fun i j => raw34945step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34945step1 raw34945step0; decide +kernel
      have hl : raw34945step1Labels = raw34945step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34945step0 raw34945step0Labels permutation32 permutation3
    mixedMoment B raw34945step1 raw34945step1Labels = mixedMoment B raw34945step2 raw34945step2Labels := by
      have ha : raw34945step2 = raw34945step1 := by apply Matrix.ext; unfold raw34945step2 raw34945step1; decide +kernel
      have hl : raw34945step1Labels = labelEmbedding6 ∘ raw34945step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34945step1 raw34945step1Labels raw34945step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw34946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34946step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34946 raw34946Labels = mixedMoment B node4668 node4668Labels := by
  calc
    mixedMoment B raw34946 raw34946Labels = mixedMoment B raw34946step0 raw34946step0Labels := by
      have ha : raw34946step0 = (fun i j => raw34946 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34946step0 raw34946; decide +kernel
      have hl : raw34946step0Labels = raw34946Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34946 raw34946Labels permutation158 permutation3
    mixedMoment B raw34946step0 raw34946step0Labels = mixedMoment B raw34946step1 raw34946step1Labels := by
      have ha : raw34946step1 = raw34946step0 := by apply Matrix.ext; unfold raw34946step1 raw34946step0; decide +kernel
      have hl : raw34946step0Labels = labelEmbedding6 ∘ raw34946step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34946step0 raw34946step0Labels raw34946step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4668 node4668Labels := by rfl

def raw34947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34947 raw34947Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw34947 raw34947Labels = mixedMoment B raw34947step0 raw34947step0Labels := by
      have ha : raw34947step0 = (fun i j => raw34947 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34947step0 raw34947; decide +kernel
      have hl : raw34947step0Labels = raw34947Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34947 raw34947Labels permutation272 permutation2
    _ = mixedMoment B node4955 node4955Labels := by rfl

def raw34948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34948 raw34948Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw34948 raw34948Labels = mixedMoment B raw34948step0 raw34948step0Labels := by
      have ha : raw34948step0 = (fun i j => raw34948 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34948step0 raw34948; decide +kernel
      have hl : raw34948step0Labels = raw34948Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34948 raw34948Labels permutation583 permutation2
    mixedMoment B raw34948step0 raw34948step0Labels = mixedMoment B raw34948step1 raw34948step1Labels := by
      have ha : raw34948step1 = -raw34948step0 := by apply Matrix.ext; change ∀ i j, raw34948step1 i j = -(raw34948step0 i j); unfold raw34948step1 raw34948step0; decide +kernel
      have hl : raw34948step1Labels = raw34948step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5336 node5336Labels := by rfl

def raw34949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34949 raw34949Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw34949 raw34949Labels = mixedMoment B raw34949step0 raw34949step0Labels := by
      have ha : raw34949step0 = (fun i j => raw34949 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34949step0 raw34949; decide +kernel
      have hl : raw34949step0Labels = raw34949Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34949 raw34949Labels permutation272 permutation2
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw34950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34950step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34950step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34950 raw34950Labels = mixedMoment B node4690 node4690Labels := by
  calc
    mixedMoment B raw34950 raw34950Labels = mixedMoment B raw34950step0 raw34950step0Labels := by
      have hz : ∀ j, raw34950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34950step0 = (fun i j => raw34950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34950step0 raw34950; decide +kernel
      have hl : raw34950step0Labels = raw34950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34950 raw34950Labels permutation346 hz
    mixedMoment B raw34950step0 raw34950step0Labels = mixedMoment B raw34950step1 raw34950step1Labels := by
      have ha : raw34950step1 = (fun i j => raw34950step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34950step1 raw34950step0; decide +kernel
      have hl : raw34950step1Labels = raw34950step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34950step0 raw34950step0Labels permutation32 permutation3
    mixedMoment B raw34950step1 raw34950step1Labels = mixedMoment B raw34950step2 raw34950step2Labels := by
      have ha : raw34950step2 = raw34950step1 := by apply Matrix.ext; unfold raw34950step2 raw34950step1; decide +kernel
      have hl : raw34950step1Labels = labelEmbedding6 ∘ raw34950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34950step1 raw34950step1Labels raw34950step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4690 node4690Labels := by rfl

def raw34951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34951 raw34951Labels = mixedMoment B node4966 node4966Labels := by
  calc
    mixedMoment B raw34951 raw34951Labels = mixedMoment B raw34951step0 raw34951step0Labels := by
      have hz : ∀ j, raw34951 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34951step0 = (fun i j => raw34951 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34951step0 raw34951; decide +kernel
      have hl : raw34951step0Labels = raw34951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34951 raw34951Labels permutation346 hz
    mixedMoment B raw34951step0 raw34951step0Labels = mixedMoment B raw34951step1 raw34951step1Labels := by
      have ha : raw34951step1 = (fun i j => raw34951step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34951step1 raw34951step0; decide +kernel
      have hl : raw34951step1Labels = raw34951step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34951step0 raw34951step0Labels permutation57 permutation2
    _ = mixedMoment B node4966 node4966Labels := by rfl

def raw34952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34952step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34952 raw34952Labels = mixedMoment B node5339 node5339Labels := by
  calc
    mixedMoment B raw34952 raw34952Labels = mixedMoment B raw34952step0 raw34952step0Labels := by
      have ha : raw34952step0 = (fun i j => raw34952 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34952step0 raw34952; decide +kernel
      have hl : raw34952step0Labels = raw34952Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34952 raw34952Labels permutation588 permutation2
    mixedMoment B raw34952step0 raw34952step0Labels = mixedMoment B raw34952step1 raw34952step1Labels := by
      have ha : raw34952step1 = -raw34952step0 := by apply Matrix.ext; change ∀ i j, raw34952step1 i j = -(raw34952step0 i j); unfold raw34952step1 raw34952step0; decide +kernel
      have hl : raw34952step1Labels = raw34952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5339 node5339Labels := by rfl

def raw34953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34953step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34953 raw34953Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw34953 raw34953Labels = mixedMoment B raw34953step0 raw34953step0Labels := by
      have hz : ∀ j, raw34953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34953step0 = (fun i j => raw34953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34953step0 raw34953; decide +kernel
      have hl : raw34953step0Labels = raw34953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34953 raw34953Labels permutation346 hz
    mixedMoment B raw34953step0 raw34953step0Labels = mixedMoment B raw34953step1 raw34953step1Labels := by
      have ha : raw34953step1 = (fun i j => raw34953step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34953step1 raw34953step0; decide +kernel
      have hl : raw34953step1Labels = raw34953step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34953step0 raw34953step0Labels permutation57 permutation2
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw34954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34954step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34954step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34954 raw34954Labels = mixedMoment B node4670 node4670Labels := by
  calc
    mixedMoment B raw34954 raw34954Labels = mixedMoment B raw34954step0 raw34954step0Labels := by
      have hz : ∀ j, raw34954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34954step0 = (fun i j => raw34954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34954step0 raw34954; decide +kernel
      have hl : raw34954step0Labels = raw34954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34954 raw34954Labels permutation346 hz
    mixedMoment B raw34954step0 raw34954step0Labels = mixedMoment B raw34954step1 raw34954step1Labels := by
      have ha : raw34954step1 = (fun i j => raw34954step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34954step1 raw34954step0; decide +kernel
      have hl : raw34954step1Labels = raw34954step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34954step0 raw34954step0Labels permutation33 permutation3
    mixedMoment B raw34954step1 raw34954step1Labels = mixedMoment B raw34954step2 raw34954step2Labels := by
      have ha : raw34954step2 = raw34954step1 := by apply Matrix.ext; unfold raw34954step2 raw34954step1; decide +kernel
      have hl : raw34954step1Labels = labelEmbedding6 ∘ raw34954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34954step1 raw34954step1Labels raw34954step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4670 node4670Labels := by rfl

def raw34955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw34955step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34955step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34955 raw34955Labels = mixedMoment B node4934 node4934Labels := by
  calc
    mixedMoment B raw34955 raw34955Labels = mixedMoment B raw34955step0 raw34955step0Labels := by
      have hz : ∀ j, raw34955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34955step0 = (fun i j => raw34955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34955step0 raw34955; decide +kernel
      have hl : raw34955step0Labels = raw34955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34955 raw34955Labels permutation346 hz
    mixedMoment B raw34955step0 raw34955step0Labels = mixedMoment B raw34955step1 raw34955step1Labels := by
      have ha : raw34955step1 = (fun i j => raw34955step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34955step1 raw34955step0; decide +kernel
      have hl : raw34955step1Labels = raw34955step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34955step0 raw34955step0Labels permutation126 permutation2
    mixedMoment B raw34955step1 raw34955step1Labels = mixedMoment B raw34955step2 raw34955step2Labels := by
      have ha : raw34955step2 = -raw34955step1 := by apply Matrix.ext; change ∀ i j, raw34955step2 i j = -(raw34955step1 i j); unfold raw34955step2 raw34955step1; decide +kernel
      have hl : raw34955step2Labels = raw34955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4934 node4934Labels := by rfl

def raw34956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34956step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34956 raw34956Labels = mixedMoment B node4931 node4931Labels := by
  calc
    mixedMoment B raw34956 raw34956Labels = mixedMoment B raw34956step0 raw34956step0Labels := by
      have ha : raw34956step0 = (fun i j => raw34956 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34956step0 raw34956; decide +kernel
      have hl : raw34956step0Labels = raw34956Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34956 raw34956Labels permutation588 permutation2
    mixedMoment B raw34956step0 raw34956step0Labels = mixedMoment B raw34956step1 raw34956step1Labels := by
      have ha : raw34956step1 = -raw34956step0 := by apply Matrix.ext; change ∀ i j, raw34956step1 i j = -(raw34956step0 i j); unfold raw34956step1 raw34956step0; decide +kernel
      have hl : raw34956step1Labels = raw34956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4931 node4931Labels := by rfl

def raw34957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34957 raw34957Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw34957 raw34957Labels = mixedMoment B raw34957step0 raw34957step0Labels := by
      have hz : ∀ j, raw34957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34957step0 = (fun i j => raw34957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34957step0 raw34957; decide +kernel
      have hl : raw34957step0Labels = raw34957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34957 raw34957Labels permutation346 hz
    mixedMoment B raw34957step0 raw34957step0Labels = mixedMoment B raw34957step1 raw34957step1Labels := by
      have ha : raw34957step1 = (fun i j => raw34957step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34957step1 raw34957step0; decide +kernel
      have hl : raw34957step1Labels = raw34957step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34957step0 raw34957step0Labels permutation126 permutation2
    mixedMoment B raw34957step1 raw34957step1Labels = mixedMoment B raw34957step2 raw34957step2Labels := by
      have ha : raw34957step2 = -raw34957step1 := by apply Matrix.ext; change ∀ i j, raw34957step2 i j = -(raw34957step1 i j); unfold raw34957step2 raw34957step1; decide +kernel
      have hl : raw34957step2Labels = raw34957step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw34958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34958step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34958step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34958 raw34958Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw34958 raw34958Labels = mixedMoment B raw34958step0 raw34958step0Labels := by
      have hz : ∀ j, raw34958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34958step0 = (fun i j => raw34958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34958step0 raw34958; decide +kernel
      have hl : raw34958step0Labels = raw34958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34958 raw34958Labels permutation346 hz
    mixedMoment B raw34958step0 raw34958step0Labels = mixedMoment B raw34958step1 raw34958step1Labels := by
      have ha : raw34958step1 = (fun i j => raw34958step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34958step1 raw34958step0; decide +kernel
      have hl : raw34958step1Labels = raw34958step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34958step0 raw34958step0Labels permutation126 permutation2
    mixedMoment B raw34958step1 raw34958step1Labels = mixedMoment B raw34958step2 raw34958step2Labels := by
      have ha : raw34958step2 = -raw34958step1 := by apply Matrix.ext; change ∀ i j, raw34958step2 i j = -(raw34958step1 i j); unfold raw34958step2 raw34958step1; decide +kernel
      have hl : raw34958step2Labels = raw34958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw34959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34959step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34959step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34959 raw34959Labels = mixedMoment B node4669 node4669Labels := by
  calc
    mixedMoment B raw34959 raw34959Labels = mixedMoment B raw34959step0 raw34959step0Labels := by
      have hz : ∀ j, raw34959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34959step0 = (fun i j => raw34959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34959step0 raw34959; decide +kernel
      have hl : raw34959step0Labels = raw34959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34959 raw34959Labels permutation346 hz
    mixedMoment B raw34959step0 raw34959step0Labels = mixedMoment B raw34959step1 raw34959step1Labels := by
      have ha : raw34959step1 = (fun i j => raw34959step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34959step1 raw34959step0; decide +kernel
      have hl : raw34959step1Labels = raw34959step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34959step0 raw34959step0Labels permutation32 permutation3
    mixedMoment B raw34959step1 raw34959step1Labels = mixedMoment B raw34959step2 raw34959step2Labels := by
      have ha : raw34959step2 = raw34959step1 := by apply Matrix.ext; unfold raw34959step2 raw34959step1; decide +kernel
      have hl : raw34959step1Labels = labelEmbedding6 ∘ raw34959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34959step1 raw34959step1Labels raw34959step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4669 node4669Labels := by rfl

def raw34960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34960 raw34960Labels = mixedMoment B node4959 node4959Labels := by
  calc
    mixedMoment B raw34960 raw34960Labels = mixedMoment B raw34960step0 raw34960step0Labels := by
      have hz : ∀ j, raw34960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34960step0 = (fun i j => raw34960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34960step0 raw34960; decide +kernel
      have hl : raw34960step0Labels = raw34960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34960 raw34960Labels permutation346 hz
    mixedMoment B raw34960step0 raw34960step0Labels = mixedMoment B raw34960step1 raw34960step1Labels := by
      have ha : raw34960step1 = (fun i j => raw34960step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34960step1 raw34960step0; decide +kernel
      have hl : raw34960step1Labels = raw34960step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34960step0 raw34960step0Labels permutation56 permutation2
    _ = mixedMoment B node4959 node4959Labels := by rfl

def raw34961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34961step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34961step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34961step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34961 raw34961Labels = mixedMoment B node4957 node4957Labels := by
  calc
    mixedMoment B raw34961 raw34961Labels = mixedMoment B raw34961step0 raw34961step0Labels := by
      have ha : raw34961step0 = (fun i j => raw34961 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34961step0 raw34961; decide +kernel
      have hl : raw34961step0Labels = raw34961Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34961 raw34961Labels permutation688 permutation3
    mixedMoment B raw34961step0 raw34961step0Labels = mixedMoment B raw34961step1 raw34961step1Labels := by
      have ha : raw34961step1 = -raw34961step0 := by apply Matrix.ext; change ∀ i j, raw34961step1 i j = -(raw34961step0 i j); unfold raw34961step1 raw34961step0; decide +kernel
      have hl : raw34961step1Labels = raw34961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34961step1 raw34961step1Labels = mixedMoment B raw34961step2 raw34961step2Labels := by
      have ha : raw34961step2 = raw34961step1 := by apply Matrix.ext; unfold raw34961step2 raw34961step1; decide +kernel
      have hl : raw34961step1Labels = labelEmbedding6 ∘ raw34961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34961step1 raw34961step1Labels raw34961step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4957 node4957Labels := by rfl

def raw34962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34962step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34962step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34962step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34962 raw34962Labels = mixedMoment B node4973 node4973Labels := by
  calc
    mixedMoment B raw34962 raw34962Labels = mixedMoment B raw34962step0 raw34962step0Labels := by
      have hz : ∀ j, raw34962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34962step0 = (fun i j => raw34962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34962step0 raw34962; decide +kernel
      have hl : raw34962step0Labels = raw34962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34962 raw34962Labels permutation346 hz
    mixedMoment B raw34962step0 raw34962step0Labels = mixedMoment B raw34962step1 raw34962step1Labels := by
      have ha : raw34962step1 = (fun i j => raw34962step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34962step1 raw34962step0; decide +kernel
      have hl : raw34962step1Labels = raw34962step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34962step0 raw34962step0Labels permutation151 permutation3
    mixedMoment B raw34962step1 raw34962step1Labels = mixedMoment B raw34962step2 raw34962step2Labels := by
      have ha : raw34962step2 = -raw34962step1 := by apply Matrix.ext; change ∀ i j, raw34962step2 i j = -(raw34962step1 i j); unfold raw34962step2 raw34962step1; decide +kernel
      have hl : raw34962step2Labels = raw34962step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34962step2 raw34962step2Labels = mixedMoment B raw34962step3 raw34962step3Labels := by
      have ha : raw34962step3 = raw34962step2 := by apply Matrix.ext; unfold raw34962step3 raw34962step2; decide +kernel
      have hl : raw34962step2Labels = labelEmbedding6 ∘ raw34962step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34962step2 raw34962step2Labels raw34962step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4973 node4973Labels := by rfl

def raw34963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34963 raw34963Labels = mixedMoment B node2943 node2943Labels := by
  calc
    mixedMoment B raw34963 raw34963Labels = mixedMoment B raw34963step0 raw34963step0Labels := by
      have hz : ∀ j, raw34963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34963step0 = (fun i j => raw34963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34963step0 raw34963; decide +kernel
      have hl : raw34963step0Labels = raw34963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34963 raw34963Labels permutation346 hz
    mixedMoment B raw34963step0 raw34963step0Labels = mixedMoment B raw34963step1 raw34963step1Labels := by
      have ha : raw34963step1 = (fun i j => raw34963step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34963step1 raw34963step0; decide +kernel
      have hl : raw34963step1Labels = raw34963step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34963step0 raw34963step0Labels permutation56 permutation3
    _ = mixedMoment B node2943 node2943Labels := by rfl

def raw34964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw34964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34964 raw34964Labels = mixedMoment B node3937 node3937Labels := by
  calc
    mixedMoment B raw34964 raw34964Labels = mixedMoment B raw34964step0 raw34964step0Labels := by
      have ha : raw34964step0 = (fun i j => raw34964 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34964step0 raw34964; decide +kernel
      have hl : raw34964step0Labels = raw34964Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34964 raw34964Labels permutation684 permutation3
    mixedMoment B raw34964step0 raw34964step0Labels = mixedMoment B raw34964step1 raw34964step1Labels := by
      have ha : raw34964step1 = -raw34964step0 := by apply Matrix.ext; change ∀ i j, raw34964step1 i j = -(raw34964step0 i j); unfold raw34964step1 raw34964step0; decide +kernel
      have hl : raw34964step1Labels = raw34964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3937 node3937Labels := by rfl

def raw34965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw34965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34965 raw34965Labels = mixedMoment B node3941 node3941Labels := by
  calc
    mixedMoment B raw34965 raw34965Labels = mixedMoment B raw34965step0 raw34965step0Labels := by
      have hz : ∀ j, raw34965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34965step0 = (fun i j => raw34965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34965step0 raw34965; decide +kernel
      have hl : raw34965step0Labels = raw34965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34965 raw34965Labels permutation346 hz
    mixedMoment B raw34965step0 raw34965step0Labels = mixedMoment B raw34965step1 raw34965step1Labels := by
      have ha : raw34965step1 = (fun i j => raw34965step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34965step1 raw34965step0; decide +kernel
      have hl : raw34965step1Labels = raw34965step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34965step0 raw34965step0Labels permutation150 permutation3
    mixedMoment B raw34965step1 raw34965step1Labels = mixedMoment B raw34965step2 raw34965step2Labels := by
      have ha : raw34965step2 = -raw34965step1 := by apply Matrix.ext; change ∀ i j, raw34965step2 i j = -(raw34965step1 i j); unfold raw34965step2 raw34965step1; decide +kernel
      have hl : raw34965step2Labels = raw34965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3941 node3941Labels := by rfl

def raw34966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34966 raw34966Labels = mixedMoment B node4035 node4035Labels := by
  calc
    mixedMoment B raw34966 raw34966Labels = mixedMoment B raw34966step0 raw34966step0Labels := by
      have hz : ∀ j, raw34966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34966step0 = (fun i j => raw34966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34966step0 raw34966; decide +kernel
      have hl : raw34966step0Labels = raw34966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34966 raw34966Labels permutation346 hz
    mixedMoment B raw34966step0 raw34966step0Labels = mixedMoment B raw34966step1 raw34966step1Labels := by
      have ha : raw34966step1 = (fun i j => raw34966step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34966step1 raw34966step0; decide +kernel
      have hl : raw34966step1Labels = raw34966step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34966step0 raw34966step0Labels permutation57 permutation3
    _ = mixedMoment B node4035 node4035Labels := by rfl

def raw34967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw34967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34967 raw34967Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw34967 raw34967Labels = mixedMoment B raw34967step0 raw34967step0Labels := by
      have hz : ∀ j, raw34967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34967step0 = (fun i j => raw34967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34967step0 raw34967; decide +kernel
      have hl : raw34967step0Labels = raw34967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34967 raw34967Labels permutation346 hz
    mixedMoment B raw34967step0 raw34967step0Labels = mixedMoment B raw34967step1 raw34967step1Labels := by
      have ha : raw34967step1 = (fun i j => raw34967step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34967step1 raw34967step0; decide +kernel
      have hl : raw34967step1Labels = raw34967step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34967step0 raw34967step0Labels permutation32 permutation3
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw34968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34968 raw34968Labels = mixedMoment B node1794 node1794Labels := by
  calc
    mixedMoment B raw34968 raw34968Labels = mixedMoment B raw34968step0 raw34968step0Labels := by
      have ha : raw34968step0 = (fun i j => raw34968 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34968step0 raw34968; decide +kernel
      have hl : raw34968step0Labels = raw34968Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34968 raw34968Labels permutation158 permutation3
    _ = mixedMoment B node1794 node1794Labels := by rfl

def raw34969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34969 raw34969Labels = mixedMoment B node2801 node2801Labels := by
  calc
    mixedMoment B raw34969 raw34969Labels = mixedMoment B raw34969step0 raw34969step0Labels := by
      have ha : raw34969step0 = (fun i j => raw34969 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34969step0 raw34969; decide +kernel
      have hl : raw34969step0Labels = raw34969Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34969 raw34969Labels permutation271 permutation3
    _ = mixedMoment B node2801 node2801Labels := by rfl

def raw34970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34970 raw34970Labels = mixedMoment B node3711 node3711Labels := by
  calc
    mixedMoment B raw34970 raw34970Labels = mixedMoment B raw34970step0 raw34970step0Labels := by
      have ha : raw34970step0 = (fun i j => raw34970 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34970step0 raw34970; decide +kernel
      have hl : raw34970step0Labels = raw34970Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34970 raw34970Labels permutation158 permutation3
    _ = mixedMoment B node3711 node3711Labels := by rfl

def raw34971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34971 raw34971Labels = mixedMoment B node3727 node3727Labels := by
  calc
    mixedMoment B raw34971 raw34971Labels = mixedMoment B raw34971step0 raw34971step0Labels := by
      have ha : raw34971step0 = (fun i j => raw34971 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34971step0 raw34971; decide +kernel
      have hl : raw34971step0Labels = raw34971Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34971 raw34971Labels permutation162 permutation3
    _ = mixedMoment B node3727 node3727Labels := by rfl

def raw34972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34972 raw34972Labels = mixedMoment B node1816 node1816Labels := by
  calc
    mixedMoment B raw34972 raw34972Labels = mixedMoment B raw34972step0 raw34972step0Labels := by
      have hz : ∀ j, raw34972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34972step0 = (fun i j => raw34972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34972step0 raw34972; decide +kernel
      have hl : raw34972step0Labels = raw34972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34972 raw34972Labels permutation346 hz
    mixedMoment B raw34972step0 raw34972step0Labels = mixedMoment B raw34972step1 raw34972step1Labels := by
      have ha : raw34972step1 = (fun i j => raw34972step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34972step1 raw34972step0; decide +kernel
      have hl : raw34972step1Labels = raw34972step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34972step0 raw34972step0Labels permutation32 permutation3
    _ = mixedMoment B node1816 node1816Labels := by rfl

def raw34973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34973step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34973step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34973 raw34973Labels = mixedMoment B node2819 node2819Labels := by
  calc
    mixedMoment B raw34973 raw34973Labels = mixedMoment B raw34973step0 raw34973step0Labels := by
      have hz : ∀ j, raw34973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34973step0 = (fun i j => raw34973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34973step0 raw34973; decide +kernel
      have hl : raw34973step0Labels = raw34973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34973 raw34973Labels permutation346 hz
    mixedMoment B raw34973step0 raw34973step0Labels = mixedMoment B raw34973step1 raw34973step1Labels := by
      have ha : raw34973step1 = (fun i j => raw34973step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34973step1 raw34973step0; decide +kernel
      have hl : raw34973step1Labels = raw34973step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34973step0 raw34973step0Labels permutation56 permutation3
    _ = mixedMoment B node2819 node2819Labels := by rfl

def raw34974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw34974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34974 raw34974Labels = mixedMoment B node3710 node3710Labels := by
  calc
    mixedMoment B raw34974 raw34974Labels = mixedMoment B raw34974step0 raw34974step0Labels := by
      have ha : raw34974step0 = (fun i j => raw34974 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34974step0 raw34974; decide +kernel
      have hl : raw34974step0Labels = raw34974Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34974 raw34974Labels permutation152 permutation3
    _ = mixedMoment B node3710 node3710Labels := by rfl

def raw34975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34975step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw34975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34975 raw34975Labels = mixedMoment B node3738 node3738Labels := by
  calc
    mixedMoment B raw34975 raw34975Labels = mixedMoment B raw34975step0 raw34975step0Labels := by
      have hz : ∀ j, raw34975 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34975step0 = (fun i j => raw34975 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34975step0 raw34975; decide +kernel
      have hl : raw34975step0Labels = raw34975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34975 raw34975Labels permutation346 hz
    mixedMoment B raw34975step0 raw34975step0Labels = mixedMoment B raw34975step1 raw34975step1Labels := by
      have ha : raw34975step1 = (fun i j => raw34975step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34975step1 raw34975step0; decide +kernel
      have hl : raw34975step1Labels = raw34975step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34975step0 raw34975step0Labels permutation36 permutation3
    _ = mixedMoment B node3738 node3738Labels := by rfl

def raw34976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34976 raw34976Labels = mixedMoment B node1796 node1796Labels := by
  calc
    mixedMoment B raw34976 raw34976Labels = mixedMoment B raw34976step0 raw34976step0Labels := by
      have hz : ∀ j, raw34976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34976step0 = (fun i j => raw34976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34976step0 raw34976; decide +kernel
      have hl : raw34976step0Labels = raw34976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34976 raw34976Labels permutation346 hz
    mixedMoment B raw34976step0 raw34976step0Labels = mixedMoment B raw34976step1 raw34976step1Labels := by
      have ha : raw34976step1 = (fun i j => raw34976step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34976step1 raw34976step0; decide +kernel
      have hl : raw34976step1Labels = raw34976step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34976step0 raw34976step0Labels permutation33 permutation3
    _ = mixedMoment B node1796 node1796Labels := by rfl

def raw34977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw34977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34977 raw34977Labels = mixedMoment B node2802 node2802Labels := by
  calc
    mixedMoment B raw34977 raw34977Labels = mixedMoment B raw34977step0 raw34977step0Labels := by
      have hz : ∀ j, raw34977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34977step0 = (fun i j => raw34977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34977step0 raw34977; decide +kernel
      have hl : raw34977step0Labels = raw34977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34977 raw34977Labels permutation346 hz
    mixedMoment B raw34977step0 raw34977step0Labels = mixedMoment B raw34977step1 raw34977step1Labels := by
      have ha : raw34977step1 = (fun i j => raw34977step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34977step1 raw34977step0; decide +kernel
      have hl : raw34977step1Labels = raw34977step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34977step0 raw34977step0Labels permutation57 permutation3
    _ = mixedMoment B node2802 node2802Labels := by rfl

def raw34978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34978 raw34978Labels = mixedMoment B node2824 node2824Labels := by
  calc
    mixedMoment B raw34978 raw34978Labels = mixedMoment B raw34978step0 raw34978step0Labels := by
      have ha : raw34978step0 = (fun i j => raw34978 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34978step0 raw34978; decide +kernel
      have hl : raw34978step0Labels = raw34978Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34978 raw34978Labels permutation589 permutation3
    mixedMoment B raw34978step0 raw34978step0Labels = mixedMoment B raw34978step1 raw34978step1Labels := by
      have ha : raw34978step1 = -raw34978step0 := by apply Matrix.ext; change ∀ i j, raw34978step1 i j = -(raw34978step0 i j); unfold raw34978step1 raw34978step0; decide +kernel
      have hl : raw34978step1Labels = raw34978step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2824 node2824Labels := by rfl

def raw34979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, -1, -1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34979 raw34979Labels = mixedMoment B node2829 node2829Labels := by
  calc
    mixedMoment B raw34979 raw34979Labels = mixedMoment B raw34979step0 raw34979step0Labels := by
      have hz : ∀ j, raw34979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34979step0 = (fun i j => raw34979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34979step0 raw34979; decide +kernel
      have hl : raw34979step0Labels = raw34979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34979 raw34979Labels permutation346 hz
    mixedMoment B raw34979step0 raw34979step0Labels = mixedMoment B raw34979step1 raw34979step1Labels := by
      have ha : raw34979step1 = (fun i j => raw34979step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34979step1 raw34979step0; decide +kernel
      have hl : raw34979step1Labels = raw34979step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34979step0 raw34979step0Labels permutation127 permutation3
    mixedMoment B raw34979step1 raw34979step1Labels = mixedMoment B raw34979step2 raw34979step2Labels := by
      have ha : raw34979step2 = -raw34979step1 := by apply Matrix.ext; change ∀ i j, raw34979step2 i j = -(raw34979step1 i j); unfold raw34979step2 raw34979step1; decide +kernel
      have hl : raw34979step2Labels = raw34979step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2829 node2829Labels := by rfl

def raw34980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw34980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw34980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34980 raw34980Labels = mixedMoment B node2990 node2990Labels := by
  calc
    mixedMoment B raw34980 raw34980Labels = mixedMoment B raw34980step0 raw34980step0Labels := by
      have hz : ∀ j, raw34980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34980step0 = (fun i j => raw34980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34980step0 raw34980; decide +kernel
      have hl : raw34980step0Labels = raw34980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34980 raw34980Labels permutation346 hz
    mixedMoment B raw34980step0 raw34980step0Labels = mixedMoment B raw34980step1 raw34980step1Labels := by
      have ha : raw34980step1 = (fun i j => raw34980step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34980step1 raw34980step0; decide +kernel
      have hl : raw34980step1Labels = raw34980step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34980step0 raw34980step0Labels permutation127 permutation3
    mixedMoment B raw34980step1 raw34980step1Labels = mixedMoment B raw34980step2 raw34980step2Labels := by
      have ha : raw34980step2 = -raw34980step1 := by apply Matrix.ext; change ∀ i j, raw34980step2 i j = -(raw34980step1 i j); unfold raw34980step2 raw34980step1; decide +kernel
      have hl : raw34980step2Labels = raw34980step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2990 node2990Labels := by rfl

def raw34981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw34981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34981 raw34981Labels = mixedMoment B node1795 node1795Labels := by
  calc
    mixedMoment B raw34981 raw34981Labels = mixedMoment B raw34981step0 raw34981step0Labels := by
      have hz : ∀ j, raw34981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34981step0 = (fun i j => raw34981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34981step0 raw34981; decide +kernel
      have hl : raw34981step0Labels = raw34981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34981 raw34981Labels permutation346 hz
    mixedMoment B raw34981step0 raw34981step0Labels = mixedMoment B raw34981step1 raw34981step1Labels := by
      have ha : raw34981step1 = (fun i j => raw34981step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34981step1 raw34981step0; decide +kernel
      have hl : raw34981step1Labels = raw34981step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34981step0 raw34981step0Labels permutation32 permutation3
    _ = mixedMoment B node1795 node1795Labels := by rfl

def raw34982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw34982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34982 raw34982Labels = mixedMoment B node2352 node2352Labels := by
  calc
    mixedMoment B raw34982 raw34982Labels = mixedMoment B raw34982step0 raw34982step0Labels := by
      have hz : ∀ j, raw34982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34982step0 = (fun i j => raw34982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34982step0 raw34982; decide +kernel
      have hl : raw34982step0Labels = raw34982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34982 raw34982Labels permutation346 hz
    mixedMoment B raw34982step0 raw34982step0Labels = mixedMoment B raw34982step1 raw34982step1Labels := by
      have ha : raw34982step1 = (fun i j => raw34982step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34982step1 raw34982step0; decide +kernel
      have hl : raw34982step1Labels = raw34982step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34982step0 raw34982step0Labels permutation150 permutation3
    mixedMoment B raw34982step1 raw34982step1Labels = mixedMoment B raw34982step2 raw34982step2Labels := by
      have ha : raw34982step2 = -raw34982step1 := by apply Matrix.ext; change ∀ i j, raw34982step2 i j = -(raw34982step1 i j); unfold raw34982step2 raw34982step1; decide +kernel
      have hl : raw34982step2Labels = raw34982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2352 node2352Labels := by rfl

def raw34983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34983 raw34983Labels = mixedMoment B node2350 node2350Labels := by
  calc
    mixedMoment B raw34983 raw34983Labels = mixedMoment B raw34983step0 raw34983step0Labels := by
      have ha : raw34983step0 = (fun i j => raw34983 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34983step0 raw34983; decide +kernel
      have hl : raw34983step0Labels = raw34983Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34983 raw34983Labels permutation688 permutation3
    mixedMoment B raw34983step0 raw34983step0Labels = mixedMoment B raw34983step1 raw34983step1Labels := by
      have ha : raw34983step1 = -raw34983step0 := by apply Matrix.ext; change ∀ i j, raw34983step1 i j = -(raw34983step0 i j); unfold raw34983step1 raw34983step0; decide +kernel
      have hl : raw34983step1Labels = raw34983step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2350 node2350Labels := by rfl

def raw34984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw34984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34984 raw34984Labels = mixedMoment B node2359 node2359Labels := by
  calc
    mixedMoment B raw34984 raw34984Labels = mixedMoment B raw34984step0 raw34984step0Labels := by
      have hz : ∀ j, raw34984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34984step0 = (fun i j => raw34984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34984step0 raw34984; decide +kernel
      have hl : raw34984step0Labels = raw34984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34984 raw34984Labels permutation346 hz
    mixedMoment B raw34984step0 raw34984step0Labels = mixedMoment B raw34984step1 raw34984step1Labels := by
      have ha : raw34984step1 = (fun i j => raw34984step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34984step1 raw34984step0; decide +kernel
      have hl : raw34984step1Labels = raw34984step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34984step0 raw34984step0Labels permutation151 permutation3
    mixedMoment B raw34984step1 raw34984step1Labels = mixedMoment B raw34984step2 raw34984step2Labels := by
      have ha : raw34984step2 = -raw34984step1 := by apply Matrix.ext; change ∀ i j, raw34984step2 i j = -(raw34984step1 i j); unfold raw34984step2 raw34984step1; decide +kernel
      have hl : raw34984step2Labels = raw34984step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2359 node2359Labels := by rfl

def raw34985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34985step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34985step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34985 raw34985Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw34985 raw34985Labels = mixedMoment B raw34985step0 raw34985step0Labels := by
      have hz : ∀ j, raw34985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34985step0 = (fun i j => raw34985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34985step0 raw34985; decide +kernel
      have hl : raw34985step0Labels = raw34985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34985 raw34985Labels permutation346 hz
    mixedMoment B raw34985step0 raw34985step0Labels = mixedMoment B raw34985step1 raw34985step1Labels := by
      have ha : raw34985step1 = (fun i j => raw34985step0 (permutation63 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34985step1 raw34985step0; decide +kernel
      have hl : raw34985step1Labels = raw34985step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34985step0 raw34985step0Labels permutation63 permutation7
    mixedMoment B raw34985step1 raw34985step1Labels = mixedMoment B raw34985step2 raw34985step2Labels := by
      have ha : raw34985step2 = -raw34985step1 := by apply Matrix.ext; change ∀ i j, raw34985step2 i j = -(raw34985step1 i j); unfold raw34985step2 raw34985step1; decide +kernel
      have hl : raw34985step2Labels = raw34985step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34985step2 raw34985step2Labels = mixedMoment B raw34985step3 raw34985step3Labels := by
      have ha : raw34985step3 = raw34985step2 := by apply Matrix.ext; unfold raw34985step3 raw34985step2; decide +kernel
      have hl : raw34985step2Labels = labelEmbedding1 ∘ raw34985step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34985step2 raw34985step2Labels raw34985step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw34986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34986 raw34986Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw34986 raw34986Labels = mixedMoment B raw34986step0 raw34986step0Labels := by
      have ha : raw34986step0 = (fun i j => raw34986 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34986step0 raw34986; decide +kernel
      have hl : raw34986step0Labels = raw34986Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34986 raw34986Labels permutation572 permutation7
    mixedMoment B raw34986step0 raw34986step0Labels = mixedMoment B raw34986step1 raw34986step1Labels := by
      have ha : raw34986step1 = raw34986step0 := by apply Matrix.ext; unfold raw34986step1 raw34986step0; decide +kernel
      have hl : raw34986step0Labels = labelEmbedding1 ∘ raw34986step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34986step0 raw34986step0Labels raw34986step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

def raw34987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34987step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34987 raw34987Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw34987 raw34987Labels = mixedMoment B raw34987step0 raw34987step0Labels := by
      have hz : ∀ j, raw34987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34987step0 = (fun i j => raw34987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34987step0 raw34987; decide +kernel
      have hl : raw34987step0Labels = raw34987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34987 raw34987Labels permutation346 hz
    mixedMoment B raw34987step0 raw34987step0Labels = mixedMoment B raw34987step1 raw34987step1Labels := by
      have ha : raw34987step1 = (fun i j => raw34987step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34987step1 raw34987step0; decide +kernel
      have hl : raw34987step1Labels = raw34987step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34987step0 raw34987step0Labels permutation123 permutation7
    mixedMoment B raw34987step1 raw34987step1Labels = mixedMoment B raw34987step2 raw34987step2Labels := by
      have ha : raw34987step2 = raw34987step1 := by apply Matrix.ext; unfold raw34987step2 raw34987step1; decide +kernel
      have hl : raw34987step1Labels = labelEmbedding1 ∘ raw34987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34987step1 raw34987step1Labels raw34987step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw34988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw34988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34988 raw34988Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw34988 raw34988Labels = mixedMoment B raw34988step0 raw34988step0Labels := by
      have hz : ∀ j, raw34988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34988step0 = (fun i j => raw34988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34988step0 raw34988; decide +kernel
      have hl : raw34988step0Labels = raw34988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34988 raw34988Labels permutation346 hz
    mixedMoment B raw34988step0 raw34988step0Labels = mixedMoment B raw34988step1 raw34988step1Labels := by
      have ha : raw34988step1 = (fun i j => raw34988step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34988step1 raw34988step0; decide +kernel
      have hl : raw34988step1Labels = raw34988step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34988step0 raw34988step0Labels permutation123 permutation7
    mixedMoment B raw34988step1 raw34988step1Labels = mixedMoment B raw34988step2 raw34988step2Labels := by
      have ha : raw34988step2 = raw34988step1 := by apply Matrix.ext; unfold raw34988step2 raw34988step1; decide +kernel
      have hl : raw34988step1Labels = labelEmbedding1 ∘ raw34988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34988step1 raw34988step1Labels raw34988step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw34989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw34989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw34989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw34989step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34989 raw34989Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw34989 raw34989Labels = mixedMoment B raw34989step0 raw34989step0Labels := by
      have hz : ∀ j, raw34989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34989step0 = (fun i j => raw34989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34989step0 raw34989; decide +kernel
      have hl : raw34989step0Labels = raw34989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34989 raw34989Labels permutation346 hz
    mixedMoment B raw34989step0 raw34989step0Labels = mixedMoment B raw34989step1 raw34989step1Labels := by
      have ha : raw34989step1 = (fun i j => raw34989step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34989step1 raw34989step0; decide +kernel
      have hl : raw34989step1Labels = raw34989step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34989step0 raw34989step0Labels permutation44 permutation5
    mixedMoment B raw34989step1 raw34989step1Labels = mixedMoment B raw34989step2 raw34989step2Labels := by
      have ha : raw34989step2 = -raw34989step1 := by apply Matrix.ext; change ∀ i j, raw34989step2 i j = -(raw34989step1 i j); unfold raw34989step2 raw34989step1; decide +kernel
      have hl : raw34989step2Labels = raw34989step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34989step2 raw34989step2Labels = mixedMoment B raw34989step3 raw34989step3Labels := by
      have ha : raw34989step3 = raw34989step2 := by apply Matrix.ext; unfold raw34989step3 raw34989step2; decide +kernel
      have hl : raw34989step2Labels = labelEmbedding1 ∘ raw34989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34989step2 raw34989step2Labels raw34989step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw34990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34990step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34990step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34990 raw34990Labels = mixedMoment B node2154 node2154Labels := by
  calc
    mixedMoment B raw34990 raw34990Labels = mixedMoment B raw34990step0 raw34990step0Labels := by
      have ha : raw34990step0 = (fun i j => raw34990 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34990step0 raw34990; decide +kernel
      have hl : raw34990step0Labels = raw34990Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34990 raw34990Labels permutation166 permutation5
    mixedMoment B raw34990step0 raw34990step0Labels = mixedMoment B raw34990step1 raw34990step1Labels := by
      have ha : raw34990step1 = -raw34990step0 := by apply Matrix.ext; change ∀ i j, raw34990step1 i j = -(raw34990step0 i j); unfold raw34990step1 raw34990step0; decide +kernel
      have hl : raw34990step1Labels = raw34990step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34990step1 raw34990step1Labels = mixedMoment B raw34990step2 raw34990step2Labels := by
      have ha : raw34990step2 = raw34990step1 := by apply Matrix.ext; unfold raw34990step2 raw34990step1; decide +kernel
      have hl : raw34990step1Labels = labelEmbedding1 ∘ raw34990step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34990step1 raw34990step1Labels raw34990step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2154 node2154Labels := by rfl

def raw34991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34991step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34991step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw34991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34991 raw34991Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw34991 raw34991Labels = mixedMoment B raw34991step0 raw34991step0Labels := by
      have ha : raw34991step0 = (fun i j => raw34991 (permutation306 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34991step0 raw34991; decide +kernel
      have hl : raw34991step0Labels = raw34991Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34991 raw34991Labels permutation306 permutation7
    mixedMoment B raw34991step0 raw34991step0Labels = mixedMoment B raw34991step1 raw34991step1Labels := by
      have ha : raw34991step1 = -raw34991step0 := by apply Matrix.ext; change ∀ i j, raw34991step1 i j = -(raw34991step0 i j); unfold raw34991step1 raw34991step0; decide +kernel
      have hl : raw34991step1Labels = raw34991step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34991step1 raw34991step1Labels = mixedMoment B raw34991step2 raw34991step2Labels := by
      have ha : raw34991step2 = raw34991step1 := by apply Matrix.ext; unfold raw34991step2 raw34991step1; decide +kernel
      have hl : raw34991step1Labels = labelEmbedding1 ∘ raw34991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34991step1 raw34991step1Labels raw34991step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

def raw34992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw34992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34992 raw34992Labels = mixedMoment B node3754 node3754Labels := by
  calc
    mixedMoment B raw34992 raw34992Labels = mixedMoment B raw34992step0 raw34992step0Labels := by
      have ha : raw34992step0 = (fun i j => raw34992 (permutation581 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34992step0 raw34992; decide +kernel
      have hl : raw34992step0Labels = raw34992Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34992 raw34992Labels permutation581 permutation7
    mixedMoment B raw34992step0 raw34992step0Labels = mixedMoment B raw34992step1 raw34992step1Labels := by
      have ha : raw34992step1 = raw34992step0 := by apply Matrix.ext; unfold raw34992step1 raw34992step0; decide +kernel
      have hl : raw34992step0Labels = labelEmbedding1 ∘ raw34992step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34992step0 raw34992step0Labels raw34992step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3754 node3754Labels := by rfl

def raw34993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34993step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34993step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34993 raw34993Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw34993 raw34993Labels = mixedMoment B raw34993step0 raw34993step0Labels := by
      have ha : raw34993step0 = (fun i j => raw34993 (permutation581 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34993step0 raw34993; decide +kernel
      have hl : raw34993step0Labels = raw34993Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34993 raw34993Labels permutation581 permutation7
    mixedMoment B raw34993step0 raw34993step0Labels = mixedMoment B raw34993step1 raw34993step1Labels := by
      have ha : raw34993step1 = raw34993step0 := by apply Matrix.ext; unfold raw34993step1 raw34993step0; decide +kernel
      have hl : raw34993step0Labels = labelEmbedding1 ∘ raw34993step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34993step0 raw34993step0Labels raw34993step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw34994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw34994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw34994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34994 raw34994Labels = mixedMoment B node2158 node2158Labels := by
  calc
    mixedMoment B raw34994 raw34994Labels = mixedMoment B raw34994step0 raw34994step0Labels := by
      have hz : ∀ j, raw34994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34994step0 = (fun i j => raw34994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34994step0 raw34994; decide +kernel
      have hl : raw34994step0Labels = raw34994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34994 raw34994Labels permutation346 hz
    mixedMoment B raw34994step0 raw34994step0Labels = mixedMoment B raw34994step1 raw34994step1Labels := by
      have ha : raw34994step1 = (fun i j => raw34994step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34994step1 raw34994step0; decide +kernel
      have hl : raw34994step1Labels = raw34994step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34994step0 raw34994step0Labels permutation35 permutation5
    mixedMoment B raw34994step1 raw34994step1Labels = mixedMoment B raw34994step2 raw34994step2Labels := by
      have ha : raw34994step2 = -raw34994step1 := by apply Matrix.ext; change ∀ i j, raw34994step2 i j = -(raw34994step1 i j); unfold raw34994step2 raw34994step1; decide +kernel
      have hl : raw34994step2Labels = raw34994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34994step2 raw34994step2Labels = mixedMoment B raw34994step3 raw34994step3Labels := by
      have ha : raw34994step3 = raw34994step2 := by apply Matrix.ext; unfold raw34994step3 raw34994step2; decide +kernel
      have hl : raw34994step2Labels = labelEmbedding1 ∘ raw34994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34994step2 raw34994step2Labels raw34994step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2158 node2158Labels := by rfl

def raw34995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34995 raw34995Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw34995 raw34995Labels = mixedMoment B raw34995step0 raw34995step0Labels := by
      have hz : ∀ j, raw34995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34995step0 = (fun i j => raw34995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34995step0 raw34995; decide +kernel
      have hl : raw34995step0Labels = raw34995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34995 raw34995Labels permutation346 hz
    mixedMoment B raw34995step0 raw34995step0Labels = mixedMoment B raw34995step1 raw34995step1Labels := by
      have ha : raw34995step1 = (fun i j => raw34995step0 (permutation63 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34995step1 raw34995step0; decide +kernel
      have hl : raw34995step1Labels = raw34995step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34995step0 raw34995step0Labels permutation63 permutation7
    mixedMoment B raw34995step1 raw34995step1Labels = mixedMoment B raw34995step2 raw34995step2Labels := by
      have ha : raw34995step2 = -raw34995step1 := by apply Matrix.ext; change ∀ i j, raw34995step2 i j = -(raw34995step1 i j); unfold raw34995step2 raw34995step1; decide +kernel
      have hl : raw34995step2Labels = raw34995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34995step2 raw34995step2Labels = mixedMoment B raw34995step3 raw34995step3Labels := by
      have ha : raw34995step3 = raw34995step2 := by apply Matrix.ext; unfold raw34995step3 raw34995step2; decide +kernel
      have hl : raw34995step2Labels = labelEmbedding1 ∘ raw34995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34995step2 raw34995step2Labels raw34995step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

def raw34996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34996step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34996 raw34996Labels = mixedMoment B node3760 node3760Labels := by
  calc
    mixedMoment B raw34996 raw34996Labels = mixedMoment B raw34996step0 raw34996step0Labels := by
      have ha : raw34996step0 = (fun i j => raw34996 (permutation581 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34996step0 raw34996; decide +kernel
      have hl : raw34996step0Labels = raw34996Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34996 raw34996Labels permutation581 permutation7
    mixedMoment B raw34996step0 raw34996step0Labels = mixedMoment B raw34996step1 raw34996step1Labels := by
      have ha : raw34996step1 = raw34996step0 := by apply Matrix.ext; unfold raw34996step1 raw34996step0; decide +kernel
      have hl : raw34996step0Labels = labelEmbedding1 ∘ raw34996step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34996step0 raw34996step0Labels raw34996step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3760 node3760Labels := by rfl

def raw34997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw34997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34997step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw34997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34997 raw34997Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw34997 raw34997Labels = mixedMoment B raw34997step0 raw34997step0Labels := by
      have hz : ∀ j, raw34997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34997step0 = (fun i j => raw34997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34997step0 raw34997; decide +kernel
      have hl : raw34997step0Labels = raw34997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34997 raw34997Labels permutation346 hz
    mixedMoment B raw34997step0 raw34997step0Labels = mixedMoment B raw34997step1 raw34997step1Labels := by
      have ha : raw34997step1 = (fun i j => raw34997step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34997step1 raw34997step0; decide +kernel
      have hl : raw34997step1Labels = raw34997step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34997step0 raw34997step0Labels permutation123 permutation7
    mixedMoment B raw34997step1 raw34997step1Labels = mixedMoment B raw34997step2 raw34997step2Labels := by
      have ha : raw34997step2 = raw34997step1 := by apply Matrix.ext; unfold raw34997step2 raw34997step1; decide +kernel
      have hl : raw34997step1Labels = labelEmbedding1 ∘ raw34997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34997step1 raw34997step1Labels raw34997step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw34998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw34998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw34998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw34998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34998 raw34998Labels = mixedMoment B node2164 node2164Labels := by
  calc
    mixedMoment B raw34998 raw34998Labels = mixedMoment B raw34998step0 raw34998step0Labels := by
      have hz : ∀ j, raw34998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34998step0 = (fun i j => raw34998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34998step0 raw34998; decide +kernel
      have hl : raw34998step0Labels = raw34998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34998 raw34998Labels permutation346 hz
    mixedMoment B raw34998step0 raw34998step0Labels = mixedMoment B raw34998step1 raw34998step1Labels := by
      have ha : raw34998step1 = (fun i j => raw34998step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34998step1 raw34998step0; decide +kernel
      have hl : raw34998step1Labels = raw34998step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34998step0 raw34998step0Labels permutation33 permutation5
    mixedMoment B raw34998step1 raw34998step1Labels = mixedMoment B raw34998step2 raw34998step2Labels := by
      have ha : raw34998step2 = -raw34998step1 := by apply Matrix.ext; change ∀ i j, raw34998step2 i j = -(raw34998step1 i j); unfold raw34998step2 raw34998step1; decide +kernel
      have hl : raw34998step2Labels = raw34998step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34998step2 raw34998step2Labels = mixedMoment B raw34998step3 raw34998step3Labels := by
      have ha : raw34998step3 = raw34998step2 := by apply Matrix.ext; unfold raw34998step3 raw34998step2; decide +kernel
      have hl : raw34998step2Labels = labelEmbedding1 ∘ raw34998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34998step2 raw34998step2Labels raw34998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2164 node2164Labels := by rfl

def raw34999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw34999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw34999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw34999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34999 raw34999Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw34999 raw34999Labels = mixedMoment B raw34999step0 raw34999step0Labels := by
      have hz : ∀ j, raw34999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34999step0 = (fun i j => raw34999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34999step0 raw34999; decide +kernel
      have hl : raw34999step0Labels = raw34999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34999 raw34999Labels permutation346 hz
    mixedMoment B raw34999step0 raw34999step0Labels = mixedMoment B raw34999step1 raw34999step1Labels := by
      have ha : raw34999step1 = (fun i j => raw34999step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34999step1 raw34999step0; decide +kernel
      have hl : raw34999step1Labels = raw34999step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34999step0 raw34999step0Labels permutation123 permutation7
    mixedMoment B raw34999step1 raw34999step1Labels = mixedMoment B raw34999step2 raw34999step2Labels := by
      have ha : raw34999step2 = raw34999step1 := by apply Matrix.ext; unfold raw34999step2 raw34999step1; decide +kernel
      have hl : raw34999step1Labels = labelEmbedding1 ∘ raw34999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34999step1 raw34999step1Labels raw34999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

def raw35000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35000step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35000 raw35000Labels = mixedMoment B node3406 node3406Labels := by
  calc
    mixedMoment B raw35000 raw35000Labels = mixedMoment B raw35000step0 raw35000step0Labels := by
      have ha : raw35000step0 = (fun i j => raw35000 (permutation581 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35000step0 raw35000; decide +kernel
      have hl : raw35000step0Labels = raw35000Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35000 raw35000Labels permutation581 permutation7
    mixedMoment B raw35000step0 raw35000step0Labels = mixedMoment B raw35000step1 raw35000step1Labels := by
      have ha : raw35000step1 = raw35000step0 := by apply Matrix.ext; unfold raw35000step1 raw35000step0; decide +kernel
      have hl : raw35000step0Labels = labelEmbedding1 ∘ raw35000step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35000step0 raw35000step0Labels raw35000step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3406 node3406Labels := by rfl

def raw35001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35001 raw35001Labels = mixedMoment B node3417 node3417Labels := by
  calc
    mixedMoment B raw35001 raw35001Labels = mixedMoment B raw35001step0 raw35001step0Labels := by
      have hz : ∀ j, raw35001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35001step0 = (fun i j => raw35001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35001step0 raw35001; decide +kernel
      have hl : raw35001step0Labels = raw35001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35001 raw35001Labels permutation346 hz
    mixedMoment B raw35001step0 raw35001step0Labels = mixedMoment B raw35001step1 raw35001step1Labels := by
      have ha : raw35001step1 = (fun i j => raw35001step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35001step1 raw35001step0; decide +kernel
      have hl : raw35001step1Labels = raw35001step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35001step0 raw35001step0Labels permutation123 permutation7
    mixedMoment B raw35001step1 raw35001step1Labels = mixedMoment B raw35001step2 raw35001step2Labels := by
      have ha : raw35001step2 = raw35001step1 := by apply Matrix.ext; unfold raw35001step2 raw35001step1; decide +kernel
      have hl : raw35001step1Labels = labelEmbedding1 ∘ raw35001step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35001step1 raw35001step1Labels raw35001step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3417 node3417Labels := by rfl

def raw35002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35002step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35002 raw35002Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw35002 raw35002Labels = mixedMoment B raw35002step0 raw35002step0Labels := by
      have hz : ∀ j, raw35002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35002step0 = (fun i j => raw35002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35002step0 raw35002; decide +kernel
      have hl : raw35002step0Labels = raw35002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35002 raw35002Labels permutation346 hz
    mixedMoment B raw35002step0 raw35002step0Labels = mixedMoment B raw35002step1 raw35002step1Labels := by
      have ha : raw35002step1 = (fun i j => raw35002step0 (permutation123 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35002step1 raw35002step0; decide +kernel
      have hl : raw35002step1Labels = raw35002step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35002step0 raw35002step0Labels permutation123 permutation7
    mixedMoment B raw35002step1 raw35002step1Labels = mixedMoment B raw35002step2 raw35002step2Labels := by
      have ha : raw35002step2 = raw35002step1 := by apply Matrix.ext; unfold raw35002step2 raw35002step1; decide +kernel
      have hl : raw35002step1Labels = labelEmbedding1 ∘ raw35002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35002step1 raw35002step1Labels raw35002step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw35003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35003step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw35003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35003step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35003step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35003step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35003 raw35003Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw35003 raw35003Labels = mixedMoment B raw35003step0 raw35003step0Labels := by
      have hz : ∀ j, raw35003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35003step0 = (fun i j => raw35003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35003step0 raw35003; decide +kernel
      have hl : raw35003step0Labels = raw35003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35003 raw35003Labels permutation346 hz
    mixedMoment B raw35003step0 raw35003step0Labels = mixedMoment B raw35003step1 raw35003step1Labels := by
      have ha : raw35003step1 = (fun i j => raw35003step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35003step1 raw35003step0; decide +kernel
      have hl : raw35003step1Labels = raw35003step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35003step0 raw35003step0Labels permutation34 permutation5
    mixedMoment B raw35003step1 raw35003step1Labels = mixedMoment B raw35003step2 raw35003step2Labels := by
      have ha : raw35003step2 = -raw35003step1 := by apply Matrix.ext; change ∀ i j, raw35003step2 i j = -(raw35003step1 i j); unfold raw35003step2 raw35003step1; decide +kernel
      have hl : raw35003step2Labels = raw35003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35003step2 raw35003step2Labels = mixedMoment B raw35003step3 raw35003step3Labels := by
      have ha : raw35003step3 = raw35003step2 := by apply Matrix.ext; unfold raw35003step3 raw35003step2; decide +kernel
      have hl : raw35003step2Labels = labelEmbedding1 ∘ raw35003step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35003step2 raw35003step2Labels raw35003step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2155 node2155Labels := by rfl

def raw35004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35004 raw35004Labels = mixedMoment B node3512 node3512Labels := by
  calc
    mixedMoment B raw35004 raw35004Labels = mixedMoment B raw35004step0 raw35004step0Labels := by
      have hz : ∀ j, raw35004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35004step0 = (fun i j => raw35004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35004step0 raw35004; decide +kernel
      have hl : raw35004step0Labels = raw35004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35004 raw35004Labels permutation346 hz
    mixedMoment B raw35004step0 raw35004step0Labels = mixedMoment B raw35004step1 raw35004step1Labels := by
      have ha : raw35004step1 = (fun i j => raw35004step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35004step1 raw35004step0; decide +kernel
      have hl : raw35004step1Labels = raw35004step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35004step0 raw35004step0Labels permutation145 permutation5
    mixedMoment B raw35004step1 raw35004step1Labels = mixedMoment B raw35004step2 raw35004step2Labels := by
      have ha : raw35004step2 = raw35004step1 := by apply Matrix.ext; unfold raw35004step2 raw35004step1; decide +kernel
      have hl : raw35004step1Labels = labelEmbedding1 ∘ raw35004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35004step1 raw35004step1Labels raw35004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3512 node3512Labels := by rfl

def raw35005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35005step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35005 raw35005Labels = mixedMoment B node3509 node3509Labels := by
  calc
    mixedMoment B raw35005 raw35005Labels = mixedMoment B raw35005step0 raw35005step0Labels := by
      have ha : raw35005step0 = (fun i j => raw35005 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35005step0 raw35005; decide +kernel
      have hl : raw35005step0Labels = raw35005Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35005 raw35005Labels permutation662 permutation5
    mixedMoment B raw35005step0 raw35005step0Labels = mixedMoment B raw35005step1 raw35005step1Labels := by
      have ha : raw35005step1 = raw35005step0 := by apply Matrix.ext; unfold raw35005step1 raw35005step0; decide +kernel
      have hl : raw35005step0Labels = labelEmbedding1 ∘ raw35005step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35005step0 raw35005step0Labels raw35005step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3509 node3509Labels := by rfl

def raw35006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw35006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw35006step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35006 raw35006Labels = mixedMoment B node3591 node3591Labels := by
  calc
    mixedMoment B raw35006 raw35006Labels = mixedMoment B raw35006step0 raw35006step0Labels := by
      have hz : ∀ j, raw35006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35006step0 = (fun i j => raw35006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35006step0 raw35006; decide +kernel
      have hl : raw35006step0Labels = raw35006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35006 raw35006Labels permutation346 hz
    mixedMoment B raw35006step0 raw35006step0Labels = mixedMoment B raw35006step1 raw35006step1Labels := by
      have ha : raw35006step1 = (fun i j => raw35006step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35006step1 raw35006step0; decide +kernel
      have hl : raw35006step1Labels = raw35006step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35006step0 raw35006step0Labels permutation151 permutation5
    mixedMoment B raw35006step1 raw35006step1Labels = mixedMoment B raw35006step2 raw35006step2Labels := by
      have ha : raw35006step2 = raw35006step1 := by apply Matrix.ext; unfold raw35006step2 raw35006step1; decide +kernel
      have hl : raw35006step1Labels = labelEmbedding1 ∘ raw35006step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35006step1 raw35006step1Labels raw35006step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3591 node3591Labels := by rfl

def raw35007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35007 raw35007Labels = mixedMoment B node2348 node2348Labels := by
  calc
    mixedMoment B raw35007 raw35007Labels = mixedMoment B raw35007step0 raw35007step0Labels := by
      have ha : raw35007step0 = (fun i j => raw35007 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35007step0 raw35007; decide +kernel
      have hl : raw35007step0Labels = raw35007Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35007 raw35007Labels permutation272 permutation2
    _ = mixedMoment B node2348 node2348Labels := by rfl

def raw35008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35008 raw35008Labels = mixedMoment B node3671 node3671Labels := by
  calc
    mixedMoment B raw35008 raw35008Labels = mixedMoment B raw35008step0 raw35008step0Labels := by
      have ha : raw35008step0 = (fun i j => raw35008 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35008step0 raw35008; decide +kernel
      have hl : raw35008step0Labels = raw35008Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35008 raw35008Labels permutation583 permutation2
    mixedMoment B raw35008step0 raw35008step0Labels = mixedMoment B raw35008step1 raw35008step1Labels := by
      have ha : raw35008step1 = -raw35008step0 := by apply Matrix.ext; change ∀ i j, raw35008step1 i j = -(raw35008step0 i j); unfold raw35008step1 raw35008step0; decide +kernel
      have hl : raw35008step1Labels = raw35008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3671 node3671Labels := by rfl

def raw35009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35009 raw35009Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw35009 raw35009Labels = mixedMoment B raw35009step0 raw35009step0Labels := by
      have ha : raw35009step0 = (fun i j => raw35009 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35009step0 raw35009; decide +kernel
      have hl : raw35009step0Labels = raw35009Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35009 raw35009Labels permutation272 permutation2
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw35010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw35010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35010 raw35010Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw35010 raw35010Labels = mixedMoment B raw35010step0 raw35010step0Labels := by
      have ha : raw35010step0 = (fun i j => raw35010 (permutation585 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35010step0 raw35010; decide +kernel
      have hl : raw35010step0Labels = raw35010Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35010 raw35010Labels permutation585 permutation2
    mixedMoment B raw35010step0 raw35010step0Labels = mixedMoment B raw35010step1 raw35010step1Labels := by
      have ha : raw35010step1 = -raw35010step0 := by apply Matrix.ext; change ∀ i j, raw35010step1 i j = -(raw35010step0 i j); unfold raw35010step1 raw35010step0; decide +kernel
      have hl : raw35010step1Labels = raw35010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3689 node3689Labels := by rfl

def raw35011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35011 raw35011Labels = mixedMoment B node3674 node3674Labels := by
  calc
    mixedMoment B raw35011 raw35011Labels = mixedMoment B raw35011step0 raw35011step0Labels := by
      have ha : raw35011step0 = (fun i j => raw35011 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35011step0 raw35011; decide +kernel
      have hl : raw35011step0Labels = raw35011Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35011 raw35011Labels permutation588 permutation2
    mixedMoment B raw35011step0 raw35011step0Labels = mixedMoment B raw35011step1 raw35011step1Labels := by
      have ha : raw35011step1 = -raw35011step0 := by apply Matrix.ext; change ∀ i j, raw35011step1 i j = -(raw35011step0 i j); unfold raw35011step1 raw35011step0; decide +kernel
      have hl : raw35011step1Labels = raw35011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3674 node3674Labels := by rfl

def raw35012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35012 raw35012Labels = mixedMoment B node2321 node2321Labels := by
  calc
    mixedMoment B raw35012 raw35012Labels = mixedMoment B raw35012step0 raw35012step0Labels := by
      have ha : raw35012step0 = (fun i j => raw35012 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35012step0 raw35012; decide +kernel
      have hl : raw35012step0Labels = raw35012Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35012 raw35012Labels permutation588 permutation2
    mixedMoment B raw35012step0 raw35012step0Labels = mixedMoment B raw35012step1 raw35012step1Labels := by
      have ha : raw35012step1 = -raw35012step0 := by apply Matrix.ext; change ∀ i j, raw35012step1 i j = -(raw35012step0 i j); unfold raw35012step1 raw35012step0; decide +kernel
      have hl : raw35012step1Labels = raw35012step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2321 node2321Labels := by rfl

def raw35013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35013 raw35013Labels = mixedMoment B node2798 node2798Labels := by
  calc
    mixedMoment B raw35013 raw35013Labels = mixedMoment B raw35013step0 raw35013step0Labels := by
      have ha : raw35013step0 = (fun i j => raw35013 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35013step0 raw35013; decide +kernel
      have hl : raw35013step0Labels = raw35013Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35013 raw35013Labels permutation687 permutation2
    mixedMoment B raw35013step0 raw35013step0Labels = mixedMoment B raw35013step1 raw35013step1Labels := by
      have ha : raw35013step1 = -raw35013step0 := by apply Matrix.ext; change ∀ i j, raw35013step1 i j = -(raw35013step0 i j); unfold raw35013step1 raw35013step0; decide +kernel
      have hl : raw35013step1Labels = raw35013step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2798 node2798Labels := by rfl

def raw35014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35014 raw35014Labels = mixedMoment B node2356 node2356Labels := by
  calc
    mixedMoment B raw35014 raw35014Labels = mixedMoment B raw35014step0 raw35014step0Labels := by
      have hz : ∀ j, raw35014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35014step0 = (fun i j => raw35014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35014step0 raw35014; decide +kernel
      have hl : raw35014step0Labels = raw35014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35014 raw35014Labels permutation346 hz
    mixedMoment B raw35014step0 raw35014step0Labels = mixedMoment B raw35014step1 raw35014step1Labels := by
      have ha : raw35014step1 = (fun i j => raw35014step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35014step1 raw35014step0; decide +kernel
      have hl : raw35014step1Labels = raw35014step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35014step0 raw35014step0Labels permutation57 permutation2
    _ = mixedMoment B node2356 node2356Labels := by rfl

def raw35015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35015 raw35015Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw35015 raw35015Labels = mixedMoment B raw35015step0 raw35015step0Labels := by
      have hz : ∀ j, raw35015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35015step0 = (fun i j => raw35015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35015step0 raw35015; decide +kernel
      have hl : raw35015step0Labels = raw35015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35015 raw35015Labels permutation346 hz
    mixedMoment B raw35015step0 raw35015step0Labels = mixedMoment B raw35015step1 raw35015step1Labels := by
      have ha : raw35015step1 = (fun i j => raw35015step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35015step1 raw35015step0; decide +kernel
      have hl : raw35015step1Labels = raw35015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35015step0 raw35015step0Labels permutation57 permutation2
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw35016 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35016step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35016step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35016step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35016step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35016 raw35016Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw35016 raw35016Labels = mixedMoment B raw35016step0 raw35016step0Labels := by
      have hz : ∀ j, raw35016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35016step0 = (fun i j => raw35016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35016step0 raw35016; decide +kernel
      have hl : raw35016step0Labels = raw35016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35016 raw35016Labels permutation346 hz
    mixedMoment B raw35016step0 raw35016step0Labels = mixedMoment B raw35016step1 raw35016step1Labels := by
      have ha : raw35016step1 = (fun i j => raw35016step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35016step1 raw35016step0; decide +kernel
      have hl : raw35016step1Labels = raw35016step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35016step0 raw35016step0Labels permutation126 permutation7
    mixedMoment B raw35016step1 raw35016step1Labels = mixedMoment B raw35016step2 raw35016step2Labels := by
      have ha : raw35016step2 = -raw35016step1 := by apply Matrix.ext; change ∀ i j, raw35016step2 i j = -(raw35016step1 i j); unfold raw35016step2 raw35016step1; decide +kernel
      have hl : raw35016step2Labels = raw35016step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35016step2 raw35016step2Labels = mixedMoment B raw35016step3 raw35016step3Labels := by
      have ha : raw35016step3 = raw35016step2 := by apply Matrix.ext; unfold raw35016step3 raw35016step2; decide +kernel
      have hl : raw35016step2Labels = labelEmbedding10 ∘ raw35016step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35016step2 raw35016step2Labels raw35016step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw35017 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35017step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35017step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35017 raw35017Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw35017 raw35017Labels = mixedMoment B raw35017step0 raw35017step0Labels := by
      have ha : raw35017step0 = (fun i j => raw35017 (permutation272 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35017step0 raw35017; decide +kernel
      have hl : raw35017step0Labels = raw35017Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35017 raw35017Labels permutation272 permutation7
    mixedMoment B raw35017step0 raw35017step0Labels = mixedMoment B raw35017step1 raw35017step1Labels := by
      have ha : raw35017step1 = raw35017step0 := by apply Matrix.ext; unfold raw35017step1 raw35017step0; decide +kernel
      have hl : raw35017step0Labels = labelEmbedding10 ∘ raw35017step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35017step0 raw35017step0Labels raw35017step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw35018 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35018step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35018 raw35018Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw35018 raw35018Labels = mixedMoment B raw35018step0 raw35018step0Labels := by
      have hz : ∀ j, raw35018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35018step0 = (fun i j => raw35018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35018step0 raw35018; decide +kernel
      have hl : raw35018step0Labels = raw35018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35018 raw35018Labels permutation346 hz
    mixedMoment B raw35018step0 raw35018step0Labels = mixedMoment B raw35018step1 raw35018step1Labels := by
      have ha : raw35018step1 = (fun i j => raw35018step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35018step1 raw35018step0; decide +kernel
      have hl : raw35018step1Labels = raw35018step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35018step0 raw35018step0Labels permutation126 permutation2
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw35019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35019step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35019step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35019step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35019step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35019 raw35019Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw35019 raw35019Labels = mixedMoment B raw35019step0 raw35019step0Labels := by
      have hz : ∀ j, raw35019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35019step0 = (fun i j => raw35019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35019step0 raw35019; decide +kernel
      have hl : raw35019step0Labels = raw35019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35019 raw35019Labels permutation346 hz
    mixedMoment B raw35019step0 raw35019step0Labels = mixedMoment B raw35019step1 raw35019step1Labels := by
      have ha : raw35019step1 = (fun i j => raw35019step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35019step1 raw35019step0; decide +kernel
      have hl : raw35019step1Labels = raw35019step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35019step0 raw35019step0Labels permutation126 permutation7
    mixedMoment B raw35019step1 raw35019step1Labels = mixedMoment B raw35019step2 raw35019step2Labels := by
      have ha : raw35019step2 = -raw35019step1 := by apply Matrix.ext; change ∀ i j, raw35019step2 i j = -(raw35019step1 i j); unfold raw35019step2 raw35019step1; decide +kernel
      have hl : raw35019step2Labels = raw35019step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35019step2 raw35019step2Labels = mixedMoment B raw35019step3 raw35019step3Labels := by
      have ha : raw35019step3 = raw35019step2 := by apply Matrix.ext; unfold raw35019step3 raw35019step2; decide +kernel
      have hl : raw35019step2Labels = labelEmbedding10 ∘ raw35019step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35019step2 raw35019step2Labels raw35019step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5327 node5327Labels := by rfl

def raw35020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 3, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw35020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw35020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35020 raw35020Labels = mixedMoment B node5158 node5158Labels := by
  calc
    mixedMoment B raw35020 raw35020Labels = mixedMoment B raw35020step0 raw35020step0Labels := by
      have hz : ∀ j, raw35020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35020step0 = (fun i j => raw35020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35020step0 raw35020; decide +kernel
      have hl : raw35020step0Labels = raw35020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35020 raw35020Labels permutation346 hz
    mixedMoment B raw35020step0 raw35020step0Labels = mixedMoment B raw35020step1 raw35020step1Labels := by
      have ha : raw35020step1 = (fun i j => raw35020step0 (permutation63 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35020step1 raw35020step0; decide +kernel
      have hl : raw35020step1Labels = raw35020step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35020step0 raw35020step0Labels permutation63 permutation2
    mixedMoment B raw35020step1 raw35020step1Labels = mixedMoment B raw35020step2 raw35020step2Labels := by
      have ha : raw35020step2 = -raw35020step1 := by apply Matrix.ext; change ∀ i j, raw35020step2 i j = -(raw35020step1 i j); unfold raw35020step2 raw35020step1; decide +kernel
      have hl : raw35020step2Labels = raw35020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5158 node5158Labels := by rfl

def raw35021 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35021 raw35021Labels = mixedMoment B node5122 node5122Labels := by
  calc
    mixedMoment B raw35021 raw35021Labels = mixedMoment B raw35021step0 raw35021step0Labels := by
      have ha : raw35021step0 = (fun i j => raw35021 (permutation306 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35021step0 raw35021; decide +kernel
      have hl : raw35021step0Labels = raw35021Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35021 raw35021Labels permutation306 permutation2
    mixedMoment B raw35021step0 raw35021step0Labels = mixedMoment B raw35021step1 raw35021step1Labels := by
      have ha : raw35021step1 = -raw35021step0 := by apply Matrix.ext; change ∀ i j, raw35021step1 i j = -(raw35021step0 i j); unfold raw35021step1 raw35021step0; decide +kernel
      have hl : raw35021step1Labels = raw35021step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5122 node5122Labels := by rfl

def raw35022 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw35022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35022 raw35022Labels = mixedMoment B node5006 node5006Labels := by
  calc
    mixedMoment B raw35022 raw35022Labels = mixedMoment B raw35022step0 raw35022step0Labels := by
      have hz : ∀ j, raw35022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35022step0 = (fun i j => raw35022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35022step0 raw35022; decide +kernel
      have hl : raw35022step0Labels = raw35022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35022 raw35022Labels permutation346 hz
    mixedMoment B raw35022step0 raw35022step0Labels = mixedMoment B raw35022step1 raw35022step1Labels := by
      have ha : raw35022step1 = (fun i j => raw35022step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35022step1 raw35022step0; decide +kernel
      have hl : raw35022step1Labels = raw35022step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35022step0 raw35022step0Labels permutation123 permutation2
    _ = mixedMoment B node5006 node5006Labels := by rfl

def raw35023 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-2, 0, 2], ![-2, 0, 2]]
def raw35023step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35023step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35023 raw35023Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw35023 raw35023Labels = mixedMoment B raw35023step0 raw35023step0Labels := by
      have hz : ∀ j, raw35023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35023step0 = (fun i j => raw35023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35023step0 raw35023; decide +kernel
      have hl : raw35023step0Labels = raw35023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35023 raw35023Labels permutation346 hz
    mixedMoment B raw35023step0 raw35023step0Labels = mixedMoment B raw35023step1 raw35023step1Labels := by
      have ha : raw35023step1 = (fun i j => raw35023step0 (permutation62 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35023step1 raw35023step0; decide +kernel
      have hl : raw35023step1Labels = raw35023step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35023step0 raw35023step0Labels permutation62 permutation2
    mixedMoment B raw35023step1 raw35023step1Labels = mixedMoment B raw35023step2 raw35023step2Labels := by
      have ha : raw35023step2 = -raw35023step1 := by apply Matrix.ext; change ∀ i j, raw35023step2 i j = -(raw35023step1 i j); unfold raw35023step2 raw35023step1; decide +kernel
      have hl : raw35023step2Labels = raw35023step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5125 node5125Labels := by rfl

def raw35024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw35024step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35024step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw35024step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35024step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw35024step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35024 raw35024Labels = mixedMoment B node5230 node5230Labels := by
  calc
    mixedMoment B raw35024 raw35024Labels = mixedMoment B raw35024step0 raw35024step0Labels := by
      have ha : raw35024step0 = (fun i j => raw35024 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35024step0 raw35024; decide +kernel
      have hl : raw35024step0Labels = raw35024Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35024 raw35024Labels permutation164 permutation4
    mixedMoment B raw35024step0 raw35024step0Labels = mixedMoment B raw35024step1 raw35024step1Labels := by
      have ha : raw35024step1 = -raw35024step0 := by apply Matrix.ext; change ∀ i j, raw35024step1 i j = -(raw35024step0 i j); unfold raw35024step1 raw35024step0; decide +kernel
      have hl : raw35024step1Labels = raw35024step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35024step1 raw35024step1Labels = mixedMoment B raw35024step2 raw35024step2Labels := by
      have ha : raw35024step2 = raw35024step1 := by apply Matrix.ext; unfold raw35024step2 raw35024step1; decide +kernel
      have hl : raw35024step1Labels = labelEmbedding7 ∘ raw35024step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35024step1 raw35024step1Labels raw35024step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5230 node5230Labels := by rfl

def raw35025 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35025step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35025 raw35025Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw35025 raw35025Labels = mixedMoment B raw35025step0 raw35025step0Labels := by
      have ha : raw35025step0 = (fun i j => raw35025 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35025step0 raw35025; decide +kernel
      have hl : raw35025step0Labels = raw35025Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35025 raw35025Labels permutation152 permutation6
    mixedMoment B raw35025step0 raw35025step0Labels = mixedMoment B raw35025step1 raw35025step1Labels := by
      have ha : raw35025step1 = raw35025step0 := by apply Matrix.ext; unfold raw35025step1 raw35025step0; decide +kernel
      have hl : raw35025step0Labels = labelEmbedding9 ∘ raw35025step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35025step0 raw35025step0Labels raw35025step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5348 node5348Labels := by rfl

def raw35026 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35026 raw35026Labels = mixedMoment B node5004 node5004Labels := by
  calc
    mixedMoment B raw35026 raw35026Labels = mixedMoment B raw35026step0 raw35026step0Labels := by
      have ha : raw35026step0 = (fun i j => raw35026 (permutation572 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35026step0 raw35026; decide +kernel
      have hl : raw35026step0Labels = raw35026Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35026 raw35026Labels permutation572 permutation2
    _ = mixedMoment B node5004 node5004Labels := by rfl

def raw35027 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35027step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35027step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35027step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35027 raw35027Labels = mixedMoment B node5320 node5320Labels := by
  calc
    mixedMoment B raw35027 raw35027Labels = mixedMoment B raw35027step0 raw35027step0Labels := by
      have ha : raw35027step0 = (fun i j => raw35027 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35027step0 raw35027; decide +kernel
      have hl : raw35027step0Labels = raw35027Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35027 raw35027Labels permutation583 permutation7
    mixedMoment B raw35027step0 raw35027step0Labels = mixedMoment B raw35027step1 raw35027step1Labels := by
      have ha : raw35027step1 = -raw35027step0 := by apply Matrix.ext; change ∀ i j, raw35027step1 i j = -(raw35027step0 i j); unfold raw35027step1 raw35027step0; decide +kernel
      have hl : raw35027step1Labels = raw35027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35027step1 raw35027step1Labels = mixedMoment B raw35027step2 raw35027step2Labels := by
      have ha : raw35027step2 = raw35027step1 := by apply Matrix.ext; unfold raw35027step2 raw35027step1; decide +kernel
      have hl : raw35027step1Labels = labelEmbedding10 ∘ raw35027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35027step1 raw35027step1Labels raw35027step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5320 node5320Labels := by rfl

def raw35028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw35028step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw35028step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35028step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw35028step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35028 raw35028Labels = mixedMoment B node5234 node5234Labels := by
  calc
    mixedMoment B raw35028 raw35028Labels = mixedMoment B raw35028step0 raw35028step0Labels := by
      have hz : ∀ j, raw35028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35028step0 = (fun i j => raw35028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35028step0 raw35028; decide +kernel
      have hl : raw35028step0Labels = raw35028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35028 raw35028Labels permutation346 hz
    mixedMoment B raw35028step0 raw35028step0Labels = mixedMoment B raw35028step1 raw35028step1Labels := by
      have ha : raw35028step1 = (fun i j => raw35028step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35028step1 raw35028step0; decide +kernel
      have hl : raw35028step1Labels = raw35028step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35028step0 raw35028step0Labels permutation35 permutation4
    mixedMoment B raw35028step1 raw35028step1Labels = mixedMoment B raw35028step2 raw35028step2Labels := by
      have ha : raw35028step2 = -raw35028step1 := by apply Matrix.ext; change ∀ i j, raw35028step2 i j = -(raw35028step1 i j); unfold raw35028step2 raw35028step1; decide +kernel
      have hl : raw35028step2Labels = raw35028step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35028step2 raw35028step2Labels = mixedMoment B raw35028step3 raw35028step3Labels := by
      have ha : raw35028step3 = raw35028step2 := by apply Matrix.ext; unfold raw35028step3 raw35028step2; decide +kernel
      have hl : raw35028step2Labels = labelEmbedding7 ∘ raw35028step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35028step2 raw35028step2Labels raw35028step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5234 node5234Labels := by rfl

def raw35029 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35029step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35029 raw35029Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw35029 raw35029Labels = mixedMoment B raw35029step0 raw35029step0Labels := by
      have hz : ∀ j, raw35029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35029step0 = (fun i j => raw35029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35029step0 raw35029; decide +kernel
      have hl : raw35029step0Labels = raw35029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35029 raw35029Labels permutation346 hz
    mixedMoment B raw35029step0 raw35029step0Labels = mixedMoment B raw35029step1 raw35029step1Labels := by
      have ha : raw35029step1 = (fun i j => raw35029step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35029step1 raw35029step0; decide +kernel
      have hl : raw35029step1Labels = raw35029step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35029step0 raw35029step0Labels permutation32 permutation6
    mixedMoment B raw35029step1 raw35029step1Labels = mixedMoment B raw35029step2 raw35029step2Labels := by
      have ha : raw35029step2 = raw35029step1 := by apply Matrix.ext; unfold raw35029step2 raw35029step1; decide +kernel
      have hl : raw35029step1Labels = labelEmbedding9 ∘ raw35029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35029step1 raw35029step1Labels raw35029step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5361 node5361Labels := by rfl

def raw35030 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35030step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35030step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35030step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35030step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35030 raw35030Labels = mixedMoment B node5342 node5342Labels := by
  calc
    mixedMoment B raw35030 raw35030Labels = mixedMoment B raw35030step0 raw35030step0Labels := by
      have ha : raw35030step0 = (fun i j => raw35030 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35030step0 raw35030; decide +kernel
      have hl : raw35030step0Labels = raw35030Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35030 raw35030Labels permutation583 permutation7
    mixedMoment B raw35030step0 raw35030step0Labels = mixedMoment B raw35030step1 raw35030step1Labels := by
      have ha : raw35030step1 = -raw35030step0 := by apply Matrix.ext; change ∀ i j, raw35030step1 i j = -(raw35030step0 i j); unfold raw35030step1 raw35030step0; decide +kernel
      have hl : raw35030step1Labels = raw35030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35030step1 raw35030step1Labels = mixedMoment B raw35030step2 raw35030step2Labels := by
      have ha : raw35030step2 = raw35030step1 := by apply Matrix.ext; unfold raw35030step2 raw35030step1; decide +kernel
      have hl : raw35030step1Labels = labelEmbedding10 ∘ raw35030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35030step1 raw35030step1Labels raw35030step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5342 node5342Labels := by rfl

def raw35031 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35031 raw35031Labels = mixedMoment B node5009 node5009Labels := by
  calc
    mixedMoment B raw35031 raw35031Labels = mixedMoment B raw35031step0 raw35031step0Labels := by
      have hz : ∀ j, raw35031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35031step0 = (fun i j => raw35031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35031step0 raw35031; decide +kernel
      have hl : raw35031step0Labels = raw35031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35031 raw35031Labels permutation346 hz
    mixedMoment B raw35031step0 raw35031step0Labels = mixedMoment B raw35031step1 raw35031step1Labels := by
      have ha : raw35031step1 = (fun i j => raw35031step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35031step1 raw35031step0; decide +kernel
      have hl : raw35031step1Labels = raw35031step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35031step0 raw35031step0Labels permutation123 permutation2
    _ = mixedMoment B node5009 node5009Labels := by rfl

def raw35032 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35032 raw35032Labels = mixedMoment B node5329 node5329Labels := by
  calc
    mixedMoment B raw35032 raw35032Labels = mixedMoment B raw35032step0 raw35032step0Labels := by
      have hz : ∀ j, raw35032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35032step0 = (fun i j => raw35032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35032step0 raw35032; decide +kernel
      have hl : raw35032step0Labels = raw35032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35032 raw35032Labels permutation346 hz
    mixedMoment B raw35032step0 raw35032step0Labels = mixedMoment B raw35032step1 raw35032step1Labels := by
      have ha : raw35032step1 = (fun i j => raw35032step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35032step1 raw35032step0; decide +kernel
      have hl : raw35032step1Labels = raw35032step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35032step0 raw35032step0Labels permutation123 permutation2
    _ = mixedMoment B node5329 node5329Labels := by rfl

def raw35033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35033step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35033step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35033step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35033step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35033step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35033 raw35033Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw35033 raw35033Labels = mixedMoment B raw35033step0 raw35033step0Labels := by
      have hz : ∀ j, raw35033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35033step0 = (fun i j => raw35033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35033step0 raw35033; decide +kernel
      have hl : raw35033step0Labels = raw35033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35033 raw35033Labels permutation346 hz
    mixedMoment B raw35033step0 raw35033step0Labels = mixedMoment B raw35033step1 raw35033step1Labels := by
      have ha : raw35033step1 = (fun i j => raw35033step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35033step1 raw35033step0; decide +kernel
      have hl : raw35033step1Labels = raw35033step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35033step0 raw35033step0Labels permutation126 permutation7
    mixedMoment B raw35033step1 raw35033step1Labels = mixedMoment B raw35033step2 raw35033step2Labels := by
      have ha : raw35033step2 = -raw35033step1 := by apply Matrix.ext; change ∀ i j, raw35033step2 i j = -(raw35033step1 i j); unfold raw35033step2 raw35033step1; decide +kernel
      have hl : raw35033step2Labels = raw35033step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35033step2 raw35033step2Labels = mixedMoment B raw35033step3 raw35033step3Labels := by
      have ha : raw35033step3 = raw35033step2 := by apply Matrix.ext; unfold raw35033step3 raw35033step2; decide +kernel
      have hl : raw35033step2Labels = labelEmbedding1 ∘ raw35033step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35033step2 raw35033step2Labels raw35033step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw35034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35034step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35034 raw35034Labels = mixedMoment B node3678 node3678Labels := by
  calc
    mixedMoment B raw35034 raw35034Labels = mixedMoment B raw35034step0 raw35034step0Labels := by
      have ha : raw35034step0 = (fun i j => raw35034 (permutation272 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35034step0 raw35034; decide +kernel
      have hl : raw35034step0Labels = raw35034Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35034 raw35034Labels permutation272 permutation7
    mixedMoment B raw35034step0 raw35034step0Labels = mixedMoment B raw35034step1 raw35034step1Labels := by
      have ha : raw35034step1 = raw35034step0 := by apply Matrix.ext; unfold raw35034step1 raw35034step0; decide +kernel
      have hl : raw35034step0Labels = labelEmbedding1 ∘ raw35034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35034step0 raw35034step0Labels raw35034step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3678 node3678Labels := by rfl

def raw35035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35035step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, 0, 2], ![-1, -1, 2]]
def raw35035step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35035step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35035step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35035step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35035 raw35035Labels = mixedMoment B node3707 node3707Labels := by
  calc
    mixedMoment B raw35035 raw35035Labels = mixedMoment B raw35035step0 raw35035step0Labels := by
      have hz : ∀ j, raw35035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35035step0 = (fun i j => raw35035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35035step0 raw35035; decide +kernel
      have hl : raw35035step0Labels = raw35035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35035 raw35035Labels permutation434 hz
    mixedMoment B raw35035step0 raw35035step0Labels = mixedMoment B raw35035step1 raw35035step1Labels := by
      have hz : ∀ j, raw35035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35035step1 = (fun i j => raw35035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35035step1 raw35035step0; decide +kernel
      have hl : raw35035step1Labels = raw35035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35035step0 raw35035step0Labels permutation80 hz
    mixedMoment B raw35035step1 raw35035step1Labels = mixedMoment B raw35035step2 raw35035step2Labels := by
      have ha : raw35035step2 = (fun i j => raw35035step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35035step2 raw35035step1; decide +kernel
      have hl : raw35035step2Labels = raw35035step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35035step1 raw35035step1Labels permutation15 permutation7
    mixedMoment B raw35035step2 raw35035step2Labels = mixedMoment B raw35035step3 raw35035step3Labels := by
      have ha : raw35035step3 = raw35035step2 := by apply Matrix.ext; unfold raw35035step3 raw35035step2; decide +kernel
      have hl : raw35035step2Labels = labelEmbedding1 ∘ raw35035step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35035step2 raw35035step2Labels raw35035step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3707 node3707Labels := by rfl

def raw35036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35036step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35036step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35036step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35036step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35036 raw35036Labels = mixedMoment B node3344 node3344Labels := by
  calc
    mixedMoment B raw35036 raw35036Labels = mixedMoment B raw35036step0 raw35036step0Labels := by
      have hz : ∀ j, raw35036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35036step0 = (fun i j => raw35036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35036step0 raw35036; decide +kernel
      have hl : raw35036step0Labels = raw35036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35036 raw35036Labels permutation346 hz
    mixedMoment B raw35036step0 raw35036step0Labels = mixedMoment B raw35036step1 raw35036step1Labels := by
      have ha : raw35036step1 = (fun i j => raw35036step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35036step1 raw35036step0; decide +kernel
      have hl : raw35036step1Labels = raw35036step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35036step0 raw35036step0Labels permutation126 permutation7
    mixedMoment B raw35036step1 raw35036step1Labels = mixedMoment B raw35036step2 raw35036step2Labels := by
      have ha : raw35036step2 = -raw35036step1 := by apply Matrix.ext; change ∀ i j, raw35036step2 i j = -(raw35036step1 i j); unfold raw35036step2 raw35036step1; decide +kernel
      have hl : raw35036step2Labels = raw35036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35036step2 raw35036step2Labels = mixedMoment B raw35036step3 raw35036step3Labels := by
      have ha : raw35036step3 = raw35036step2 := by apply Matrix.ext; unfold raw35036step3 raw35036step2; decide +kernel
      have hl : raw35036step2Labels = labelEmbedding1 ∘ raw35036step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35036step2 raw35036step2Labels raw35036step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3344 node3344Labels := by rfl

def raw35037 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35037step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35037step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35037step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35037step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35037step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35037 raw35037Labels = mixedMoment B node3654 node3654Labels := by
  calc
    mixedMoment B raw35037 raw35037Labels = mixedMoment B raw35037step0 raw35037step0Labels := by
      have hz : ∀ j, raw35037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35037step0 = (fun i j => raw35037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35037step0 raw35037; decide +kernel
      have hl : raw35037step0Labels = raw35037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35037 raw35037Labels permutation346 hz
    mixedMoment B raw35037step0 raw35037step0Labels = mixedMoment B raw35037step1 raw35037step1Labels := by
      have ha : raw35037step1 = (fun i j => raw35037step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35037step1 raw35037step0; decide +kernel
      have hl : raw35037step1Labels = raw35037step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35037step0 raw35037step0Labels permutation126 permutation7
    mixedMoment B raw35037step1 raw35037step1Labels = mixedMoment B raw35037step2 raw35037step2Labels := by
      have ha : raw35037step2 = -raw35037step1 := by apply Matrix.ext; change ∀ i j, raw35037step2 i j = -(raw35037step1 i j); unfold raw35037step2 raw35037step1; decide +kernel
      have hl : raw35037step2Labels = raw35037step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35037step2 raw35037step2Labels = mixedMoment B raw35037step3 raw35037step3Labels := by
      have ha : raw35037step3 = raw35037step2 := by apply Matrix.ext; unfold raw35037step3 raw35037step2; decide +kernel
      have hl : raw35037step2Labels = labelEmbedding1 ∘ raw35037step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35037step2 raw35037step2Labels raw35037step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3654 node3654Labels := by rfl

def raw35038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35038Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35038step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw35038step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw35038step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35038step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw35038step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35038 raw35038Labels = mixedMoment B node3047 node3047Labels := by
  calc
    mixedMoment B raw35038 raw35038Labels = mixedMoment B raw35038step0 raw35038step0Labels := by
      have hz : ∀ j, raw35038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35038step0 = (fun i j => raw35038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35038step0 raw35038; decide +kernel
      have hl : raw35038step0Labels = raw35038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35038 raw35038Labels permutation346 hz
    mixedMoment B raw35038step0 raw35038step0Labels = mixedMoment B raw35038step1 raw35038step1Labels := by
      have ha : raw35038step1 = (fun i j => raw35038step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35038step1 raw35038step0; decide +kernel
      have hl : raw35038step1Labels = raw35038step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35038step0 raw35038step0Labels permutation49 permutation5
    mixedMoment B raw35038step1 raw35038step1Labels = mixedMoment B raw35038step2 raw35038step2Labels := by
      have ha : raw35038step2 = -raw35038step1 := by apply Matrix.ext; change ∀ i j, raw35038step2 i j = -(raw35038step1 i j); unfold raw35038step2 raw35038step1; decide +kernel
      have hl : raw35038step2Labels = raw35038step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35038step2 raw35038step2Labels = mixedMoment B raw35038step3 raw35038step3Labels := by
      have ha : raw35038step3 = raw35038step2 := by apply Matrix.ext; unfold raw35038step3 raw35038step2; decide +kernel
      have hl : raw35038step2Labels = labelEmbedding1 ∘ raw35038step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35038step2 raw35038step2Labels raw35038step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3047 node3047Labels := by rfl

def raw35039 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35039Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35039step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35039 raw35039Labels = mixedMoment B node3367 node3367Labels := by
  calc
    mixedMoment B raw35039 raw35039Labels = mixedMoment B raw35039step0 raw35039step0Labels := by
      have ha : raw35039step0 = (fun i j => raw35039 (permutation272 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35039step0 raw35039; decide +kernel
      have hl : raw35039step0Labels = raw35039Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35039 raw35039Labels permutation272 permutation7
    mixedMoment B raw35039step0 raw35039step0Labels = mixedMoment B raw35039step1 raw35039step1Labels := by
      have ha : raw35039step1 = raw35039step0 := by apply Matrix.ext; unfold raw35039step1 raw35039step0; decide +kernel
      have hl : raw35039step0Labels = labelEmbedding1 ∘ raw35039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35039step0 raw35039step0Labels raw35039step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3367 node3367Labels := by rfl

def raw35040 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35040Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35040step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35040step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-2, 0, 2], ![-1, -1, 2]]
def raw35040step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35040step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35040step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35040step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35040step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35040 raw35040Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw35040 raw35040Labels = mixedMoment B raw35040step0 raw35040step0Labels := by
      have hz : ∀ j, raw35040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35040step0 = (fun i j => raw35040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35040step0 raw35040; decide +kernel
      have hl : raw35040step0Labels = raw35040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35040 raw35040Labels permutation434 hz
    mixedMoment B raw35040step0 raw35040step0Labels = mixedMoment B raw35040step1 raw35040step1Labels := by
      have hz : ∀ j, raw35040step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35040step1 = (fun i j => raw35040step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35040step1 raw35040step0; decide +kernel
      have hl : raw35040step1Labels = raw35040step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35040step0 raw35040step0Labels permutation80 hz
    mixedMoment B raw35040step1 raw35040step1Labels = mixedMoment B raw35040step2 raw35040step2Labels := by
      have ha : raw35040step2 = (fun i j => raw35040step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35040step2 raw35040step1; decide +kernel
      have hl : raw35040step2Labels = raw35040step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35040step1 raw35040step1Labels permutation15 permutation7
    mixedMoment B raw35040step2 raw35040step2Labels = mixedMoment B raw35040step3 raw35040step3Labels := by
      have ha : raw35040step3 = raw35040step2 := by apply Matrix.ext; unfold raw35040step3 raw35040step2; decide +kernel
      have hl : raw35040step2Labels = labelEmbedding1 ∘ raw35040step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35040step2 raw35040step2Labels raw35040step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw35041 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35041Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35041step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw35041step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35041step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35041step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw35041step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35041 raw35041Labels = mixedMoment B node3343 node3343Labels := by
  calc
    mixedMoment B raw35041 raw35041Labels = mixedMoment B raw35041step0 raw35041step0Labels := by
      have hz : ∀ j, raw35041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35041step0 = (fun i j => raw35041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35041step0 raw35041; decide +kernel
      have hl : raw35041step0Labels = raw35041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35041 raw35041Labels permutation346 hz
    mixedMoment B raw35041step0 raw35041step0Labels = mixedMoment B raw35041step1 raw35041step1Labels := by
      have ha : raw35041step1 = (fun i j => raw35041step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35041step1 raw35041step0; decide +kernel
      have hl : raw35041step1Labels = raw35041step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35041step0 raw35041step0Labels permutation126 permutation7
    mixedMoment B raw35041step1 raw35041step1Labels = mixedMoment B raw35041step2 raw35041step2Labels := by
      have ha : raw35041step2 = -raw35041step1 := by apply Matrix.ext; change ∀ i j, raw35041step2 i j = -(raw35041step1 i j); unfold raw35041step2 raw35041step1; decide +kernel
      have hl : raw35041step2Labels = raw35041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35041step2 raw35041step2Labels = mixedMoment B raw35041step3 raw35041step3Labels := by
      have ha : raw35041step3 = raw35041step2 := by apply Matrix.ext; unfold raw35041step3 raw35041step2; decide +kernel
      have hl : raw35041step2Labels = labelEmbedding1 ∘ raw35041step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35041step2 raw35041step2Labels raw35041step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3343 node3343Labels := by rfl

def raw35042 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35042step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35042step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35042 raw35042Labels = mixedMoment B node3372 node3372Labels := by
  calc
    mixedMoment B raw35042 raw35042Labels = mixedMoment B raw35042step0 raw35042step0Labels := by
      have hz : ∀ j, raw35042 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35042step0 = (fun i j => raw35042 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35042step0 raw35042; decide +kernel
      have hl : raw35042step0Labels = raw35042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35042 raw35042Labels permutation346 hz
    mixedMoment B raw35042step0 raw35042step0Labels = mixedMoment B raw35042step1 raw35042step1Labels := by
      have ha : raw35042step1 = (fun i j => raw35042step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35042step1 raw35042step0; decide +kernel
      have hl : raw35042step1Labels = raw35042step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35042step0 raw35042step0Labels permutation56 permutation7
    mixedMoment B raw35042step1 raw35042step1Labels = mixedMoment B raw35042step2 raw35042step2Labels := by
      have ha : raw35042step2 = raw35042step1 := by apply Matrix.ext; unfold raw35042step2 raw35042step1; decide +kernel
      have hl : raw35042step1Labels = labelEmbedding1 ∘ raw35042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35042step1 raw35042step1Labels raw35042step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3372 node3372Labels := by rfl

def raw35043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw35043step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw35043step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35043step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw35043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35043 raw35043Labels = mixedMoment B node3041 node3041Labels := by
  calc
    mixedMoment B raw35043 raw35043Labels = mixedMoment B raw35043step0 raw35043step0Labels := by
      have ha : raw35043step0 = (fun i j => raw35043 (permutation228 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35043step0 raw35043; decide +kernel
      have hl : raw35043step0Labels = raw35043Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35043 raw35043Labels permutation228 permutation5
    mixedMoment B raw35043step0 raw35043step0Labels = mixedMoment B raw35043step1 raw35043step1Labels := by
      have ha : raw35043step1 = -raw35043step0 := by apply Matrix.ext; change ∀ i j, raw35043step1 i j = -(raw35043step0 i j); unfold raw35043step1 raw35043step0; decide +kernel
      have hl : raw35043step1Labels = raw35043step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35043step1 raw35043step1Labels = mixedMoment B raw35043step2 raw35043step2Labels := by
      have ha : raw35043step2 = raw35043step1 := by apply Matrix.ext; unfold raw35043step2 raw35043step1; decide +kernel
      have hl : raw35043step1Labels = labelEmbedding1 ∘ raw35043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35043step1 raw35043step1Labels raw35043step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3041 node3041Labels := by rfl

def raw35044 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw35044step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35044 raw35044Labels = mixedMoment B node3685 node3685Labels := by
  calc
    mixedMoment B raw35044 raw35044Labels = mixedMoment B raw35044step0 raw35044step0Labels := by
      have ha : raw35044step0 = (fun i j => raw35044 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35044step0 raw35044; decide +kernel
      have hl : raw35044step0Labels = raw35044Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35044 raw35044Labels permutation583 permutation7
    mixedMoment B raw35044step0 raw35044step0Labels = mixedMoment B raw35044step1 raw35044step1Labels := by
      have ha : raw35044step1 = -raw35044step0 := by apply Matrix.ext; change ∀ i j, raw35044step1 i j = -(raw35044step0 i j); unfold raw35044step1 raw35044step0; decide +kernel
      have hl : raw35044step1Labels = raw35044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35044step1 raw35044step1Labels = mixedMoment B raw35044step2 raw35044step2Labels := by
      have ha : raw35044step2 = raw35044step1 := by apply Matrix.ext; unfold raw35044step2 raw35044step1; decide +kernel
      have hl : raw35044step1Labels = labelEmbedding1 ∘ raw35044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35044step1 raw35044step1Labels raw35044step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3685 node3685Labels := by rfl

def raw35045 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35045step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35045step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35045step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35045 raw35045Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw35045 raw35045Labels = mixedMoment B raw35045step0 raw35045step0Labels := by
      have hz : ∀ j, raw35045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35045step0 = (fun i j => raw35045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35045step0 raw35045; decide +kernel
      have hl : raw35045step0Labels = raw35045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35045 raw35045Labels permutation434 hz
    mixedMoment B raw35045step0 raw35045step0Labels = mixedMoment B raw35045step1 raw35045step1Labels := by
      have ha : raw35045step1 = (fun i j => raw35045step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35045step1 raw35045step0; decide +kernel
      have hl : raw35045step1Labels = raw35045step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35045step0 raw35045step0Labels permutation126 permutation7
    mixedMoment B raw35045step1 raw35045step1Labels = mixedMoment B raw35045step2 raw35045step2Labels := by
      have ha : raw35045step2 = -raw35045step1 := by apply Matrix.ext; change ∀ i j, raw35045step2 i j = -(raw35045step1 i j); unfold raw35045step2 raw35045step1; decide +kernel
      have hl : raw35045step2Labels = raw35045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35045step2 raw35045step2Labels = mixedMoment B raw35045step3 raw35045step3Labels := by
      have ha : raw35045step3 = raw35045step2 := by apply Matrix.ext; unfold raw35045step3 raw35045step2; decide +kernel
      have hl : raw35045step2Labels = labelEmbedding1 ∘ raw35045step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35045step2 raw35045step2Labels raw35045step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw35046 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35046step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35046step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35046 raw35046Labels = mixedMoment B node3337 node3337Labels := by
  calc
    mixedMoment B raw35046 raw35046Labels = mixedMoment B raw35046step0 raw35046step0Labels := by
      have ha : raw35046step0 = (fun i j => raw35046 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35046step0 raw35046; decide +kernel
      have hl : raw35046step0Labels = raw35046Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35046 raw35046Labels permutation583 permutation7
    mixedMoment B raw35046step0 raw35046step0Labels = mixedMoment B raw35046step1 raw35046step1Labels := by
      have ha : raw35046step1 = -raw35046step0 := by apply Matrix.ext; change ∀ i j, raw35046step1 i j = -(raw35046step0 i j); unfold raw35046step1 raw35046step0; decide +kernel
      have hl : raw35046step1Labels = raw35046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35046step1 raw35046step1Labels = mixedMoment B raw35046step2 raw35046step2Labels := by
      have ha : raw35046step2 = raw35046step1 := by apply Matrix.ext; unfold raw35046step2 raw35046step1; decide +kernel
      have hl : raw35046step1Labels = labelEmbedding1 ∘ raw35046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35046step1 raw35046step1Labels raw35046step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3337 node3337Labels := by rfl

def raw35047 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35047step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35047step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35047step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35047 raw35047Labels = mixedMoment B node3646 node3646Labels := by
  calc
    mixedMoment B raw35047 raw35047Labels = mixedMoment B raw35047step0 raw35047step0Labels := by
      have ha : raw35047step0 = (fun i j => raw35047 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35047step0 raw35047; decide +kernel
      have hl : raw35047step0Labels = raw35047Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35047 raw35047Labels permutation583 permutation7
    mixedMoment B raw35047step0 raw35047step0Labels = mixedMoment B raw35047step1 raw35047step1Labels := by
      have ha : raw35047step1 = -raw35047step0 := by apply Matrix.ext; change ∀ i j, raw35047step1 i j = -(raw35047step0 i j); unfold raw35047step1 raw35047step0; decide +kernel
      have hl : raw35047step1Labels = raw35047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35047step1 raw35047step1Labels = mixedMoment B raw35047step2 raw35047step2Labels := by
      have ha : raw35047step2 = raw35047step1 := by apply Matrix.ext; unfold raw35047step2 raw35047step1; decide +kernel
      have hl : raw35047step1Labels = labelEmbedding1 ∘ raw35047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35047step1 raw35047step1Labels raw35047step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3646 node3646Labels := by rfl

def raw35048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw35048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35048step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35048step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35048 raw35048Labels = mixedMoment B node3042 node3042Labels := by
  calc
    mixedMoment B raw35048 raw35048Labels = mixedMoment B raw35048step0 raw35048step0Labels := by
      have hz : ∀ j, raw35048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35048step0 = (fun i j => raw35048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35048step0 raw35048; decide +kernel
      have hl : raw35048step0Labels = raw35048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35048 raw35048Labels permutation346 hz
    mixedMoment B raw35048step0 raw35048step0Labels = mixedMoment B raw35048step1 raw35048step1Labels := by
      have ha : raw35048step1 = (fun i j => raw35048step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35048step1 raw35048step0; decide +kernel
      have hl : raw35048step1Labels = raw35048step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35048step0 raw35048step0Labels permutation45 permutation5
    mixedMoment B raw35048step1 raw35048step1Labels = mixedMoment B raw35048step2 raw35048step2Labels := by
      have ha : raw35048step2 = -raw35048step1 := by apply Matrix.ext; change ∀ i j, raw35048step2 i j = -(raw35048step1 i j); unfold raw35048step2 raw35048step1; decide +kernel
      have hl : raw35048step2Labels = raw35048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35048step2 raw35048step2Labels = mixedMoment B raw35048step3 raw35048step3Labels := by
      have ha : raw35048step3 = raw35048step2 := by apply Matrix.ext; unfold raw35048step3 raw35048step2; decide +kernel
      have hl : raw35048step2Labels = labelEmbedding1 ∘ raw35048step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35048step2 raw35048step2Labels raw35048step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3042 node3042Labels := by rfl

def raw35049 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35049step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw35049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35049step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35049step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35049step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35049 raw35049Labels = mixedMoment B node3699 node3699Labels := by
  calc
    mixedMoment B raw35049 raw35049Labels = mixedMoment B raw35049step0 raw35049step0Labels := by
      have hz : ∀ j, raw35049 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35049step0 = (fun i j => raw35049 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35049step0 raw35049; decide +kernel
      have hl : raw35049step0Labels = raw35049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35049 raw35049Labels permutation346 hz
    mixedMoment B raw35049step0 raw35049step0Labels = mixedMoment B raw35049step1 raw35049step1Labels := by
      have ha : raw35049step1 = (fun i j => raw35049step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35049step1 raw35049step0; decide +kernel
      have hl : raw35049step1Labels = raw35049step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35049step0 raw35049step0Labels permutation126 permutation7
    mixedMoment B raw35049step1 raw35049step1Labels = mixedMoment B raw35049step2 raw35049step2Labels := by
      have ha : raw35049step2 = -raw35049step1 := by apply Matrix.ext; change ∀ i j, raw35049step2 i j = -(raw35049step1 i j); unfold raw35049step2 raw35049step1; decide +kernel
      have hl : raw35049step2Labels = raw35049step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35049step2 raw35049step2Labels = mixedMoment B raw35049step3 raw35049step3Labels := by
      have ha : raw35049step3 = raw35049step2 := by apply Matrix.ext; unfold raw35049step3 raw35049step2; decide +kernel
      have hl : raw35049step2Labels = labelEmbedding1 ∘ raw35049step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35049step2 raw35049step2Labels raw35049step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3699 node3699Labels := by rfl

def raw35050 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw35050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35050step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35050step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35050 raw35050Labels = mixedMoment B node3679 node3679Labels := by
  calc
    mixedMoment B raw35050 raw35050Labels = mixedMoment B raw35050step0 raw35050step0Labels := by
      have ha : raw35050step0 = (fun i j => raw35050 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35050step0 raw35050; decide +kernel
      have hl : raw35050step0Labels = raw35050Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35050 raw35050Labels permutation583 permutation7
    mixedMoment B raw35050step0 raw35050step0Labels = mixedMoment B raw35050step1 raw35050step1Labels := by
      have ha : raw35050step1 = -raw35050step0 := by apply Matrix.ext; change ∀ i j, raw35050step1 i j = -(raw35050step0 i j); unfold raw35050step1 raw35050step0; decide +kernel
      have hl : raw35050step1Labels = raw35050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35050step1 raw35050step1Labels = mixedMoment B raw35050step2 raw35050step2Labels := by
      have ha : raw35050step2 = raw35050step1 := by apply Matrix.ext; unfold raw35050step2 raw35050step1; decide +kernel
      have hl : raw35050step1Labels = labelEmbedding1 ∘ raw35050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35050step1 raw35050step1Labels raw35050step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3679 node3679Labels := by rfl

def raw35051 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw35051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35051 raw35051Labels = mixedMoment B node3348 node3348Labels := by
  calc
    mixedMoment B raw35051 raw35051Labels = mixedMoment B raw35051step0 raw35051step0Labels := by
      have hz : ∀ j, raw35051 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35051step0 = (fun i j => raw35051 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35051step0 raw35051; decide +kernel
      have hl : raw35051step0Labels = raw35051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35051 raw35051Labels permutation346 hz
    mixedMoment B raw35051step0 raw35051step0Labels = mixedMoment B raw35051step1 raw35051step1Labels := by
      have ha : raw35051step1 = (fun i j => raw35051step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35051step1 raw35051step0; decide +kernel
      have hl : raw35051step1Labels = raw35051step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35051step0 raw35051step0Labels permutation126 permutation7
    mixedMoment B raw35051step1 raw35051step1Labels = mixedMoment B raw35051step2 raw35051step2Labels := by
      have ha : raw35051step2 = -raw35051step1 := by apply Matrix.ext; change ∀ i j, raw35051step2 i j = -(raw35051step1 i j); unfold raw35051step2 raw35051step1; decide +kernel
      have hl : raw35051step2Labels = raw35051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35051step2 raw35051step2Labels = mixedMoment B raw35051step3 raw35051step3Labels := by
      have ha : raw35051step3 = raw35051step2 := by apply Matrix.ext; unfold raw35051step3 raw35051step2; decide +kernel
      have hl : raw35051step2Labels = labelEmbedding1 ∘ raw35051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35051step2 raw35051step2Labels raw35051step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3348 node3348Labels := by rfl

def raw35052 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw35052step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35052step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35052step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35052 raw35052Labels = mixedMoment B node3660 node3660Labels := by
  calc
    mixedMoment B raw35052 raw35052Labels = mixedMoment B raw35052step0 raw35052step0Labels := by
      have hz : ∀ j, raw35052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35052step0 = (fun i j => raw35052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35052step0 raw35052; decide +kernel
      have hl : raw35052step0Labels = raw35052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35052 raw35052Labels permutation346 hz
    mixedMoment B raw35052step0 raw35052step0Labels = mixedMoment B raw35052step1 raw35052step1Labels := by
      have ha : raw35052step1 = (fun i j => raw35052step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35052step1 raw35052step0; decide +kernel
      have hl : raw35052step1Labels = raw35052step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35052step0 raw35052step0Labels permutation126 permutation7
    mixedMoment B raw35052step1 raw35052step1Labels = mixedMoment B raw35052step2 raw35052step2Labels := by
      have ha : raw35052step2 = -raw35052step1 := by apply Matrix.ext; change ∀ i j, raw35052step2 i j = -(raw35052step1 i j); unfold raw35052step2 raw35052step1; decide +kernel
      have hl : raw35052step2Labels = raw35052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35052step2 raw35052step2Labels = mixedMoment B raw35052step3 raw35052step3Labels := by
      have ha : raw35052step3 = raw35052step2 := by apply Matrix.ext; unfold raw35052step3 raw35052step2; decide +kernel
      have hl : raw35052step2Labels = labelEmbedding1 ∘ raw35052step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35052step2 raw35052step2Labels raw35052step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3660 node3660Labels := by rfl

def raw35053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35053step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 2, -1], ![-1, 0, 1]]
def raw35053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw35053step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35053step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw35053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35053 raw35053Labels = mixedMoment B node3115 node3115Labels := by
  calc
    mixedMoment B raw35053 raw35053Labels = mixedMoment B raw35053step0 raw35053step0Labels := by
      have hz : ∀ j, raw35053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35053step0 = (fun i j => raw35053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35053step0 raw35053; decide +kernel
      have hl : raw35053step0Labels = raw35053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35053 raw35053Labels permutation346 hz
    mixedMoment B raw35053step0 raw35053step0Labels = mixedMoment B raw35053step1 raw35053step1Labels := by
      have ha : raw35053step1 = (fun i j => raw35053step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35053step1 raw35053step0; decide +kernel
      have hl : raw35053step1Labels = raw35053step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35053step0 raw35053step0Labels permutation35 permutation5
    mixedMoment B raw35053step1 raw35053step1Labels = mixedMoment B raw35053step2 raw35053step2Labels := by
      have ha : raw35053step2 = -raw35053step1 := by apply Matrix.ext; change ∀ i j, raw35053step2 i j = -(raw35053step1 i j); unfold raw35053step2 raw35053step1; decide +kernel
      have hl : raw35053step2Labels = raw35053step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35053step2 raw35053step2Labels = mixedMoment B raw35053step3 raw35053step3Labels := by
      have ha : raw35053step3 = raw35053step2 := by apply Matrix.ext; unfold raw35053step3 raw35053step2; decide +kernel
      have hl : raw35053step2Labels = labelEmbedding1 ∘ raw35053step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35053step2 raw35053step2Labels raw35053step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3115 node3115Labels := by rfl

def raw35054 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35054step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw35054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35054step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35054step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35054 raw35054Labels = mixedMoment B node3926 node3926Labels := by
  calc
    mixedMoment B raw35054 raw35054Labels = mixedMoment B raw35054step0 raw35054step0Labels := by
      have hz : ∀ j, raw35054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35054step0 = (fun i j => raw35054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35054step0 raw35054; decide +kernel
      have hl : raw35054step0Labels = raw35054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35054 raw35054Labels permutation346 hz
    mixedMoment B raw35054step0 raw35054step0Labels = mixedMoment B raw35054step1 raw35054step1Labels := by
      have ha : raw35054step1 = (fun i j => raw35054step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35054step1 raw35054step0; decide +kernel
      have hl : raw35054step1Labels = raw35054step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35054step0 raw35054step0Labels permutation126 permutation7
    mixedMoment B raw35054step1 raw35054step1Labels = mixedMoment B raw35054step2 raw35054step2Labels := by
      have ha : raw35054step2 = -raw35054step1 := by apply Matrix.ext; change ∀ i j, raw35054step2 i j = -(raw35054step1 i j); unfold raw35054step2 raw35054step1; decide +kernel
      have hl : raw35054step2Labels = raw35054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35054step2 raw35054step2Labels = mixedMoment B raw35054step3 raw35054step3Labels := by
      have ha : raw35054step3 = raw35054step2 := by apply Matrix.ext; unfold raw35054step3 raw35054step2; decide +kernel
      have hl : raw35054step2Labels = labelEmbedding1 ∘ raw35054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35054step2 raw35054step2Labels raw35054step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3926 node3926Labels := by rfl

def raw35055 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35055step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35055 raw35055Labels = mixedMoment B node3716 node3716Labels := by
  calc
    mixedMoment B raw35055 raw35055Labels = mixedMoment B raw35055step0 raw35055step0Labels := by
      have ha : raw35055step0 = (fun i j => raw35055 (permutation271 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35055step0 raw35055; decide +kernel
      have hl : raw35055step0Labels = raw35055Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35055 raw35055Labels permutation271 permutation7
    mixedMoment B raw35055step0 raw35055step0Labels = mixedMoment B raw35055step1 raw35055step1Labels := by
      have ha : raw35055step1 = raw35055step0 := by apply Matrix.ext; unfold raw35055step1 raw35055step0; decide +kernel
      have hl : raw35055step0Labels = labelEmbedding1 ∘ raw35055step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35055step0 raw35055step0Labels raw35055step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3716 node3716Labels := by rfl

def raw35056 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw35056step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw35056step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35056step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35056step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35056step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35056step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35056 raw35056Labels = mixedMoment B node3741 node3741Labels := by
  calc
    mixedMoment B raw35056 raw35056Labels = mixedMoment B raw35056step0 raw35056step0Labels := by
      have hz : ∀ j, raw35056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35056step0 = (fun i j => raw35056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35056step0 raw35056; decide +kernel
      have hl : raw35056step0Labels = raw35056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35056 raw35056Labels permutation434 hz
    mixedMoment B raw35056step0 raw35056step0Labels = mixedMoment B raw35056step1 raw35056step1Labels := by
      have hz : ∀ j, raw35056step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35056step1 = (fun i j => raw35056step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35056step1 raw35056step0; decide +kernel
      have hl : raw35056step1Labels = raw35056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35056step0 raw35056step0Labels permutation80 hz
    mixedMoment B raw35056step1 raw35056step1Labels = mixedMoment B raw35056step2 raw35056step2Labels := by
      have ha : raw35056step2 = (fun i j => raw35056step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35056step2 raw35056step1; decide +kernel
      have hl : raw35056step2Labels = raw35056step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35056step1 raw35056step1Labels permutation14 permutation7
    mixedMoment B raw35056step2 raw35056step2Labels = mixedMoment B raw35056step3 raw35056step3Labels := by
      have ha : raw35056step3 = raw35056step2 := by apply Matrix.ext; unfold raw35056step3 raw35056step2; decide +kernel
      have hl : raw35056step2Labels = labelEmbedding1 ∘ raw35056step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35056step2 raw35056step2Labels raw35056step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3741 node3741Labels := by rfl

def raw35057 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35057step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35057step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35057step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35057 raw35057Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw35057 raw35057Labels = mixedMoment B raw35057step0 raw35057step0Labels := by
      have hz : ∀ j, raw35057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35057step0 = (fun i j => raw35057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35057step0 raw35057; decide +kernel
      have hl : raw35057step0Labels = raw35057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35057 raw35057Labels permutation346 hz
    mixedMoment B raw35057step0 raw35057step0Labels = mixedMoment B raw35057step1 raw35057step1Labels := by
      have ha : raw35057step1 = (fun i j => raw35057step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35057step1 raw35057step0; decide +kernel
      have hl : raw35057step1Labels = raw35057step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35057step0 raw35057step0Labels permutation150 permutation7
    mixedMoment B raw35057step1 raw35057step1Labels = mixedMoment B raw35057step2 raw35057step2Labels := by
      have ha : raw35057step2 = -raw35057step1 := by apply Matrix.ext; change ∀ i j, raw35057step2 i j = -(raw35057step1 i j); unfold raw35057step2 raw35057step1; decide +kernel
      have hl : raw35057step2Labels = raw35057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35057step2 raw35057step2Labels = mixedMoment B raw35057step3 raw35057step3Labels := by
      have ha : raw35057step3 = raw35057step2 := by apply Matrix.ext; unfold raw35057step3 raw35057step2; decide +kernel
      have hl : raw35057step2Labels = labelEmbedding1 ∘ raw35057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35057step2 raw35057step2Labels raw35057step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw35058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw35058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw35058step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw35058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35058step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw35058step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35058step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw35058step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35058 raw35058Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw35058 raw35058Labels = mixedMoment B raw35058step0 raw35058step0Labels := by
      have hz : ∀ j, raw35058 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35058step0 = (fun i j => raw35058 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35058step0 raw35058; decide +kernel
      have hl : raw35058step0Labels = raw35058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35058 raw35058Labels permutation346 hz
    mixedMoment B raw35058step0 raw35058step0Labels = mixedMoment B raw35058step1 raw35058step1Labels := by
      have ha : raw35058step1 = (fun i j => raw35058step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35058step1 raw35058step0; decide +kernel
      have hl : raw35058step1Labels = raw35058step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35058step0 raw35058step0Labels permutation44 permutation5
    mixedMoment B raw35058step1 raw35058step1Labels = mixedMoment B raw35058step2 raw35058step2Labels := by
      have ha : raw35058step2 = -raw35058step1 := by apply Matrix.ext; change ∀ i j, raw35058step2 i j = -(raw35058step1 i j); unfold raw35058step2 raw35058step1; decide +kernel
      have hl : raw35058step2Labels = raw35058step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35058step2 raw35058step2Labels = mixedMoment B raw35058step3 raw35058step3Labels := by
      have ha : raw35058step3 = raw35058step2 := by apply Matrix.ext; unfold raw35058step3 raw35058step2; decide +kernel
      have hl : raw35058step2Labels = labelEmbedding1 ∘ raw35058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35058step2 raw35058step2Labels raw35058step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3045 node3045Labels := by rfl

def raw35059 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw35059Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw35059step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw35059step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35059step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35059step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35059step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35059 raw35059Labels = mixedMoment B node3728 node3728Labels := by
  calc
    mixedMoment B raw35059 raw35059Labels = mixedMoment B raw35059step0 raw35059step0Labels := by
      have hz : ∀ j, raw35059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35059step0 = (fun i j => raw35059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35059step0 raw35059; decide +kernel
      have hl : raw35059step0Labels = raw35059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35059 raw35059Labels permutation346 hz
    mixedMoment B raw35059step0 raw35059step0Labels = mixedMoment B raw35059step1 raw35059step1Labels := by
      have ha : raw35059step1 = (fun i j => raw35059step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35059step1 raw35059step0; decide +kernel
      have hl : raw35059step1Labels = raw35059step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35059step0 raw35059step0Labels permutation126 permutation7
    mixedMoment B raw35059step1 raw35059step1Labels = mixedMoment B raw35059step2 raw35059step2Labels := by
      have ha : raw35059step2 = -raw35059step1 := by apply Matrix.ext; change ∀ i j, raw35059step2 i j = -(raw35059step1 i j); unfold raw35059step2 raw35059step1; decide +kernel
      have hl : raw35059step2Labels = raw35059step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35059step2 raw35059step2Labels = mixedMoment B raw35059step3 raw35059step3Labels := by
      have ha : raw35059step3 = raw35059step2 := by apply Matrix.ext; unfold raw35059step3 raw35059step2; decide +kernel
      have hl : raw35059step2Labels = labelEmbedding1 ∘ raw35059step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35059step2 raw35059step2Labels raw35059step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3728 node3728Labels := by rfl

def raw35060 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw35060Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35060 raw35060Labels = mixedMoment B node3715 node3715Labels := by
  calc
    mixedMoment B raw35060 raw35060Labels = mixedMoment B raw35060step0 raw35060step0Labels := by
      have ha : raw35060step0 = (fun i j => raw35060 (permutation272 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35060step0 raw35060; decide +kernel
      have hl : raw35060step0Labels = raw35060Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35060 raw35060Labels permutation272 permutation7
    mixedMoment B raw35060step0 raw35060step0Labels = mixedMoment B raw35060step1 raw35060step1Labels := by
      have ha : raw35060step1 = raw35060step0 := by apply Matrix.ext; unfold raw35060step1 raw35060step0; decide +kernel
      have hl : raw35060step0Labels = labelEmbedding1 ∘ raw35060step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35060step0 raw35060step0Labels raw35060step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3715 node3715Labels := by rfl

def raw35061 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw35061Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw35061step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, 0, 2], ![0, -2, 2]]
def raw35061step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35061step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35061step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35061step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35061step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35061 raw35061Labels = mixedMoment B node3740 node3740Labels := by
  calc
    mixedMoment B raw35061 raw35061Labels = mixedMoment B raw35061step0 raw35061step0Labels := by
      have hz : ∀ j, raw35061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35061step0 = (fun i j => raw35061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35061step0 raw35061; decide +kernel
      have hl : raw35061step0Labels = raw35061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35061 raw35061Labels permutation434 hz
    mixedMoment B raw35061step0 raw35061step0Labels = mixedMoment B raw35061step1 raw35061step1Labels := by
      have hz : ∀ j, raw35061step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35061step1 = (fun i j => raw35061step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35061step1 raw35061step0; decide +kernel
      have hl : raw35061step1Labels = raw35061step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35061step0 raw35061step0Labels permutation80 hz
    mixedMoment B raw35061step1 raw35061step1Labels = mixedMoment B raw35061step2 raw35061step2Labels := by
      have ha : raw35061step2 = (fun i j => raw35061step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35061step2 raw35061step1; decide +kernel
      have hl : raw35061step2Labels = raw35061step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35061step1 raw35061step1Labels permutation15 permutation7
    mixedMoment B raw35061step2 raw35061step2Labels = mixedMoment B raw35061step3 raw35061step3Labels := by
      have ha : raw35061step3 = raw35061step2 := by apply Matrix.ext; unfold raw35061step3 raw35061step2; decide +kernel
      have hl : raw35061step2Labels = labelEmbedding1 ∘ raw35061step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35061step2 raw35061step2Labels raw35061step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3740 node3740Labels := by rfl

def raw35062 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw35062Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw35062step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35062step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35062step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35062step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35062 raw35062Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw35062 raw35062Labels = mixedMoment B raw35062step0 raw35062step0Labels := by
      have hz : ∀ j, raw35062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35062step0 = (fun i j => raw35062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35062step0 raw35062; decide +kernel
      have hl : raw35062step0Labels = raw35062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35062 raw35062Labels permutation346 hz
    mixedMoment B raw35062step0 raw35062step0Labels = mixedMoment B raw35062step1 raw35062step1Labels := by
      have ha : raw35062step1 = (fun i j => raw35062step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35062step1 raw35062step0; decide +kernel
      have hl : raw35062step1Labels = raw35062step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35062step0 raw35062step0Labels permutation126 permutation7
    mixedMoment B raw35062step1 raw35062step1Labels = mixedMoment B raw35062step2 raw35062step2Labels := by
      have ha : raw35062step2 = -raw35062step1 := by apply Matrix.ext; change ∀ i j, raw35062step2 i j = -(raw35062step1 i j); unfold raw35062step2 raw35062step1; decide +kernel
      have hl : raw35062step2Labels = raw35062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35062step2 raw35062step2Labels = mixedMoment B raw35062step3 raw35062step3Labels := by
      have ha : raw35062step3 = raw35062step2 := by apply Matrix.ext; unfold raw35062step3 raw35062step2; decide +kernel
      have hl : raw35062step2Labels = labelEmbedding1 ∘ raw35062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35062step2 raw35062step2Labels raw35062step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3379 node3379Labels := by rfl

def raw35063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw35063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35063 raw35063Labels = mixedMoment B node3664 node3664Labels := by
  calc
    mixedMoment B raw35063 raw35063Labels = mixedMoment B raw35063step0 raw35063step0Labels := by
      have hz : ∀ j, raw35063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35063step0 = (fun i j => raw35063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35063step0 raw35063; decide +kernel
      have hl : raw35063step0Labels = raw35063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35063 raw35063Labels permutation346 hz
    mixedMoment B raw35063step0 raw35063step0Labels = mixedMoment B raw35063step1 raw35063step1Labels := by
      have ha : raw35063step1 = (fun i j => raw35063step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35063step1 raw35063step0; decide +kernel
      have hl : raw35063step1Labels = raw35063step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35063step0 raw35063step0Labels permutation123 permutation2
    mixedMoment B raw35063step1 raw35063step1Labels = mixedMoment B raw35063step2 raw35063step2Labels := by
      have ha : raw35063step2 = -raw35063step1 := by apply Matrix.ext; change ∀ i j, raw35063step2 i j = -(raw35063step1 i j); unfold raw35063step2 raw35063step1; decide +kernel
      have hl : raw35063step2Labels = raw35063step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3664 node3664Labels := by rfl

def raw35064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35064 raw35064Labels = mixedMoment B node3638 node3638Labels := by
  calc
    mixedMoment B raw35064 raw35064Labels = mixedMoment B raw35064step0 raw35064step0Labels := by
      have ha : raw35064step0 = (fun i j => raw35064 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35064step0 raw35064; decide +kernel
      have hl : raw35064step0Labels = raw35064Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35064 raw35064Labels permutation583 permutation2
    mixedMoment B raw35064step0 raw35064step0Labels = mixedMoment B raw35064step1 raw35064step1Labels := by
      have ha : raw35064step1 = -raw35064step0 := by apply Matrix.ext; change ∀ i j, raw35064step1 i j = -(raw35064step0 i j); unfold raw35064step1 raw35064step0; decide +kernel
      have hl : raw35064step1Labels = raw35064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3638 node3638Labels := by rfl

def raw35065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw35065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw35065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35065step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35065 raw35065Labels = mixedMoment B node2313 node2313Labels := by
  calc
    mixedMoment B raw35065 raw35065Labels = mixedMoment B raw35065step0 raw35065step0Labels := by
      have hz : ∀ j, raw35065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35065step0 = (fun i j => raw35065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35065step0 raw35065; decide +kernel
      have hl : raw35065step0Labels = raw35065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35065 raw35065Labels permutation346 hz
    mixedMoment B raw35065step0 raw35065step0Labels = mixedMoment B raw35065step1 raw35065step1Labels := by
      have ha : raw35065step1 = (fun i j => raw35065step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35065step1 raw35065step0; decide +kernel
      have hl : raw35065step1Labels = raw35065step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35065step0 raw35065step0Labels permutation126 permutation2
    mixedMoment B raw35065step1 raw35065step1Labels = mixedMoment B raw35065step2 raw35065step2Labels := by
      have ha : raw35065step2 = -raw35065step1 := by apply Matrix.ext; change ∀ i j, raw35065step2 i j = -(raw35065step1 i j); unfold raw35065step2 raw35065step1; decide +kernel
      have hl : raw35065step2Labels = raw35065step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2313 node2313Labels := by rfl

def raw35066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw35066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw35066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35066 raw35066Labels = mixedMoment B node2313 node2313Labels := by
  calc
    mixedMoment B raw35066 raw35066Labels = mixedMoment B raw35066step0 raw35066step0Labels := by
      have hz : ∀ j, raw35066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35066step0 = (fun i j => raw35066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35066step0 raw35066; decide +kernel
      have hl : raw35066step0Labels = raw35066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35066 raw35066Labels permutation346 hz
    mixedMoment B raw35066step0 raw35066step0Labels = mixedMoment B raw35066step1 raw35066step1Labels := by
      have ha : raw35066step1 = (fun i j => raw35066step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35066step1 raw35066step0; decide +kernel
      have hl : raw35066step1Labels = raw35066step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35066step0 raw35066step0Labels permutation150 permutation2
    mixedMoment B raw35066step1 raw35066step1Labels = mixedMoment B raw35066step2 raw35066step2Labels := by
      have ha : raw35066step2 = -raw35066step1 := by apply Matrix.ext; change ∀ i j, raw35066step2 i j = -(raw35066step1 i j); unfold raw35066step2 raw35066step1; decide +kernel
      have hl : raw35066step2Labels = raw35066step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2313 node2313Labels := by rfl

def raw35067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw35067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35067 raw35067Labels = mixedMoment B node3650 node3650Labels := by
  calc
    mixedMoment B raw35067 raw35067Labels = mixedMoment B raw35067step0 raw35067step0Labels := by
      have ha : raw35067step0 = (fun i j => raw35067 (permutation585 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35067step0 raw35067; decide +kernel
      have hl : raw35067step0Labels = raw35067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35067 raw35067Labels permutation585 permutation2
    mixedMoment B raw35067step0 raw35067step0Labels = mixedMoment B raw35067step1 raw35067step1Labels := by
      have ha : raw35067step1 = -raw35067step0 := by apply Matrix.ext; change ∀ i j, raw35067step1 i j = -(raw35067step0 i j); unfold raw35067step1 raw35067step0; decide +kernel
      have hl : raw35067step1Labels = raw35067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3650 node3650Labels := by rfl

def raw35068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw35068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35068 raw35068Labels = mixedMoment B node3653 node3653Labels := by
  calc
    mixedMoment B raw35068 raw35068Labels = mixedMoment B raw35068step0 raw35068step0Labels := by
      have ha : raw35068step0 = (fun i j => raw35068 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35068step0 raw35068; decide +kernel
      have hl : raw35068step0Labels = raw35068Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35068 raw35068Labels permutation589 permutation2
    mixedMoment B raw35068step0 raw35068step0Labels = mixedMoment B raw35068step1 raw35068step1Labels := by
      have ha : raw35068step1 = -raw35068step0 := by apply Matrix.ext; change ∀ i j, raw35068step1 i j = -(raw35068step0 i j); unfold raw35068step1 raw35068step0; decide +kernel
      have hl : raw35068step1Labels = raw35068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3653 node3653Labels := by rfl

def raw35069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35069 raw35069Labels = mixedMoment B node3646 node3646Labels := by
  calc
    mixedMoment B raw35069 raw35069Labels = mixedMoment B raw35069step0 raw35069step0Labels := by
      have ha : raw35069step0 = (fun i j => raw35069 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35069step0 raw35069; decide +kernel
      have hl : raw35069step0Labels = raw35069Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35069 raw35069Labels permutation583 permutation2
    mixedMoment B raw35069step0 raw35069step0Labels = mixedMoment B raw35069step1 raw35069step1Labels := by
      have ha : raw35069step1 = -raw35069step0 := by apply Matrix.ext; change ∀ i j, raw35069step1 i j = -(raw35069step0 i j); unfold raw35069step1 raw35069step0; decide +kernel
      have hl : raw35069step1Labels = raw35069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3646 node3646Labels := by rfl

def raw35070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35070 raw35070Labels = mixedMoment B node3641 node3641Labels := by
  calc
    mixedMoment B raw35070 raw35070Labels = mixedMoment B raw35070step0 raw35070step0Labels := by
      have ha : raw35070step0 = (fun i j => raw35070 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35070step0 raw35070; decide +kernel
      have hl : raw35070step0Labels = raw35070Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35070 raw35070Labels permutation588 permutation2
    mixedMoment B raw35070step0 raw35070step0Labels = mixedMoment B raw35070step1 raw35070step1Labels := by
      have ha : raw35070step1 = -raw35070step0 := by apply Matrix.ext; change ∀ i j, raw35070step1 i j = -(raw35070step0 i j); unfold raw35070step1 raw35070step0; decide +kernel
      have hl : raw35070step1Labels = raw35070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3641 node3641Labels := by rfl

def raw35071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35071 raw35071Labels = mixedMoment B node2298 node2298Labels := by
  calc
    mixedMoment B raw35071 raw35071Labels = mixedMoment B raw35071step0 raw35071step0Labels := by
      have ha : raw35071step0 = (fun i j => raw35071 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35071step0 raw35071; decide +kernel
      have hl : raw35071step0Labels = raw35071Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35071 raw35071Labels permutation588 permutation2
    mixedMoment B raw35071step0 raw35071step0Labels = mixedMoment B raw35071step1 raw35071step1Labels := by
      have ha : raw35071step1 = -raw35071step0 := by apply Matrix.ext; change ∀ i j, raw35071step1 i j = -(raw35071step0 i j); unfold raw35071step1 raw35071step0; decide +kernel
      have hl : raw35071step1Labels = raw35071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2298 node2298Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
