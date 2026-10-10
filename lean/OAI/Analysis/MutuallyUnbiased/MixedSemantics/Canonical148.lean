import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18944 raw18944Labels = mixedMoment B node5463 node5463Labels := by
  calc
    mixedMoment B raw18944 raw18944Labels = mixedMoment B raw18944step0 raw18944step0Labels := by
      have hz : ∀ j, raw18944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18944step0 = (fun i j => raw18944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18944step0 raw18944; decide +kernel
      have hl : raw18944step0Labels = raw18944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18944 raw18944Labels permutation346 hz
    mixedMoment B raw18944step0 raw18944step0Labels = mixedMoment B raw18944step1 raw18944step1Labels := by
      have ha : raw18944step1 = (fun i j => raw18944step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18944step1 raw18944step0; decide +kernel
      have hl : raw18944step1Labels = raw18944step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18944step0 raw18944step0Labels permutation36 permutation2
    _ = mixedMoment B node5463 node5463Labels := by rfl

def raw18945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw18945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18945 raw18945Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw18945 raw18945Labels = mixedMoment B raw18945step0 raw18945step0Labels := by
      have ha : raw18945step0 = (fun i j => raw18945 (permutation568 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18945step0 raw18945; decide +kernel
      have hl : raw18945step0Labels = raw18945Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18945 raw18945Labels permutation568 permutation2
    mixedMoment B raw18945step0 raw18945step0Labels = mixedMoment B raw18945step1 raw18945step1Labels := by
      have ha : raw18945step1 = -raw18945step0 := by apply Matrix.ext; change ∀ i j, raw18945step1 i j = -(raw18945step0 i j); unfold raw18945step1 raw18945step0; decide +kernel
      have hl : raw18945step1Labels = raw18945step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw18946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18946step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18946step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18946step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18946step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18946 raw18946Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw18946 raw18946Labels = mixedMoment B raw18946step0 raw18946step0Labels := by
      have hz : ∀ j, raw18946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18946step0 = (fun i j => raw18946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18946step0 raw18946; decide +kernel
      have hl : raw18946step0Labels = raw18946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18946 raw18946Labels permutation346 hz
    mixedMoment B raw18946step0 raw18946step0Labels = mixedMoment B raw18946step1 raw18946step1Labels := by
      have ha : raw18946step1 = (fun i j => raw18946step0 (permutation80 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18946step1 raw18946step0; decide +kernel
      have hl : raw18946step1Labels = raw18946step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18946step0 raw18946step0Labels permutation80 permutation4
    mixedMoment B raw18946step1 raw18946step1Labels = mixedMoment B raw18946step2 raw18946step2Labels := by
      have ha : raw18946step2 = -raw18946step1 := by apply Matrix.ext; change ∀ i j, raw18946step2 i j = -(raw18946step1 i j); unfold raw18946step2 raw18946step1; decide +kernel
      have hl : raw18946step2Labels = raw18946step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18946step2 raw18946step2Labels = mixedMoment B raw18946step3 raw18946step3Labels := by
      have ha : raw18946step3 = raw18946step2 := by apply Matrix.ext; unfold raw18946step3 raw18946step2; decide +kernel
      have hl : raw18946step2Labels = labelEmbedding7 ∘ raw18946step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18946step2 raw18946step2Labels raw18946step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw18947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw18947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw18947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18947step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18947 raw18947Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18947 raw18947Labels = mixedMoment B raw18947step0 raw18947step0Labels := by
      have hz : ∀ j, raw18947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18947step0 = (fun i j => raw18947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18947step0 raw18947; decide +kernel
      have hl : raw18947step0Labels = raw18947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18947 raw18947Labels permutation346 hz
    mixedMoment B raw18947step0 raw18947step0Labels = mixedMoment B raw18947step1 raw18947step1Labels := by
      have ha : raw18947step1 = (fun i j => raw18947step0 (permutation121 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18947step1 raw18947step0; decide +kernel
      have hl : raw18947step1Labels = raw18947step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18947step0 raw18947step0Labels permutation121 permutation2
    mixedMoment B raw18947step1 raw18947step1Labels = mixedMoment B raw18947step2 raw18947step2Labels := by
      have ha : raw18947step2 = -raw18947step1 := by apply Matrix.ext; change ∀ i j, raw18947step2 i j = -(raw18947step1 i j); unfold raw18947step2 raw18947step1; decide +kernel
      have hl : raw18947step2Labels = raw18947step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18948step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18948step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw18948step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18948 raw18948Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw18948 raw18948Labels = mixedMoment B raw18948step0 raw18948step0Labels := by
      have hz : ∀ j, raw18948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18948step0 = (fun i j => raw18948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18948step0 raw18948; decide +kernel
      have hl : raw18948step0Labels = raw18948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18948 raw18948Labels permutation346 hz
    mixedMoment B raw18948step0 raw18948step0Labels = mixedMoment B raw18948step1 raw18948step1Labels := by
      have ha : raw18948step1 = (fun i j => raw18948step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18948step1 raw18948step0; decide +kernel
      have hl : raw18948step1Labels = raw18948step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18948step0 raw18948step0Labels permutation32 permutation3
    mixedMoment B raw18948step1 raw18948step1Labels = mixedMoment B raw18948step2 raw18948step2Labels := by
      have ha : raw18948step2 = raw18948step1 := by apply Matrix.ext; unfold raw18948step2 raw18948step1; decide +kernel
      have hl : raw18948step1Labels = labelEmbedding6 ∘ raw18948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18948step1 raw18948step1Labels raw18948step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw18949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18949step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18949step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18949 raw18949Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw18949 raw18949Labels = mixedMoment B raw18949step0 raw18949step0Labels := by
      have hz : ∀ j, raw18949 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18949step0 = (fun i j => raw18949 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18949step0 raw18949; decide +kernel
      have hl : raw18949step0Labels = raw18949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18949 raw18949Labels permutation346 hz
    mixedMoment B raw18949step0 raw18949step0Labels = mixedMoment B raw18949step1 raw18949step1Labels := by
      have ha : raw18949step1 = (fun i j => raw18949step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18949step1 raw18949step0; decide +kernel
      have hl : raw18949step1Labels = raw18949step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18949step0 raw18949step0Labels permutation150 permutation5
    mixedMoment B raw18949step1 raw18949step1Labels = mixedMoment B raw18949step2 raw18949step2Labels := by
      have ha : raw18949step2 = raw18949step1 := by apply Matrix.ext; unfold raw18949step2 raw18949step1; decide +kernel
      have hl : raw18949step1Labels = labelEmbedding8 ∘ raw18949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18949step1 raw18949step1Labels raw18949step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw18950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18950step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18950step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18950 raw18950Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw18950 raw18950Labels = mixedMoment B raw18950step0 raw18950step0Labels := by
      have ha : raw18950step0 = (fun i j => raw18950 (permutation676 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18950step0 raw18950; decide +kernel
      have hl : raw18950step0Labels = raw18950Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18950 raw18950Labels permutation676 permutation5
    mixedMoment B raw18950step0 raw18950step0Labels = mixedMoment B raw18950step1 raw18950step1Labels := by
      have ha : raw18950step1 = raw18950step0 := by apply Matrix.ext; unfold raw18950step1 raw18950step0; decide +kernel
      have hl : raw18950step0Labels = labelEmbedding8 ∘ raw18950step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18950step0 raw18950step0Labels raw18950step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw18951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18951step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18951 raw18951Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw18951 raw18951Labels = mixedMoment B raw18951step0 raw18951step0Labels := by
      have hz : ∀ j, raw18951 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18951step0 = (fun i j => raw18951 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18951step0 raw18951; decide +kernel
      have hl : raw18951step0Labels = raw18951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18951 raw18951Labels permutation346 hz
    mixedMoment B raw18951step0 raw18951step0Labels = mixedMoment B raw18951step1 raw18951step1Labels := by
      have ha : raw18951step1 = (fun i j => raw18951step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18951step1 raw18951step0; decide +kernel
      have hl : raw18951step1Labels = raw18951step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18951step0 raw18951step0Labels permutation148 permutation5
    mixedMoment B raw18951step1 raw18951step1Labels = mixedMoment B raw18951step2 raw18951step2Labels := by
      have ha : raw18951step2 = raw18951step1 := by apply Matrix.ext; unfold raw18951step2 raw18951step1; decide +kernel
      have hl : raw18951step1Labels = labelEmbedding8 ∘ raw18951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18951step1 raw18951step1Labels raw18951step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw18952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw18952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw18952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18952step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18952step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18952 raw18952Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw18952 raw18952Labels = mixedMoment B raw18952step0 raw18952step0Labels := by
      have hz : ∀ j, raw18952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18952step0 = (fun i j => raw18952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18952step0 raw18952; decide +kernel
      have hl : raw18952step0Labels = raw18952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18952 raw18952Labels permutation346 hz
    mixedMoment B raw18952step0 raw18952step0Labels = mixedMoment B raw18952step1 raw18952step1Labels := by
      have ha : raw18952step1 = (fun i j => raw18952step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18952step1 raw18952step0; decide +kernel
      have hl : raw18952step1Labels = raw18952step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18952step0 raw18952step0Labels permutation137 permutation5
    mixedMoment B raw18952step1 raw18952step1Labels = mixedMoment B raw18952step2 raw18952step2Labels := by
      have ha : raw18952step2 = raw18952step1 := by apply Matrix.ext; unfold raw18952step2 raw18952step1; decide +kernel
      have hl : raw18952step1Labels = labelEmbedding8 ∘ raw18952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18952step1 raw18952step1Labels raw18952step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw18953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18953 raw18953Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw18953 raw18953Labels = mixedMoment B raw18953step0 raw18953step0Labels := by
      have hz : ∀ j, raw18953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18953step0 = (fun i j => raw18953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18953step0 raw18953; decide +kernel
      have hl : raw18953step0Labels = raw18953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18953 raw18953Labels permutation346 hz
    mixedMoment B raw18953step0 raw18953step0Labels = mixedMoment B raw18953step1 raw18953step1Labels := by
      have ha : raw18953step1 = (fun i j => raw18953step0 (permutation96 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18953step1 raw18953step0; decide +kernel
      have hl : raw18953step1Labels = raw18953step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18953step0 raw18953step0Labels permutation96 permutation7
    mixedMoment B raw18953step1 raw18953step1Labels = mixedMoment B raw18953step2 raw18953step2Labels := by
      have ha : raw18953step2 = raw18953step1 := by apply Matrix.ext; unfold raw18953step2 raw18953step1; decide +kernel
      have hl : raw18953step1Labels = labelEmbedding1 ∘ raw18953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18953step1 raw18953step1Labels raw18953step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw18954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18954 raw18954Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw18954 raw18954Labels = mixedMoment B raw18954step0 raw18954step0Labels := by
      have ha : raw18954step0 = (fun i j => raw18954 (permutation497 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18954step0 raw18954; decide +kernel
      have hl : raw18954step0Labels = raw18954Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18954 raw18954Labels permutation497 permutation7
    mixedMoment B raw18954step0 raw18954step0Labels = mixedMoment B raw18954step1 raw18954step1Labels := by
      have ha : raw18954step1 = raw18954step0 := by apply Matrix.ext; unfold raw18954step1 raw18954step0; decide +kernel
      have hl : raw18954step0Labels = labelEmbedding1 ∘ raw18954step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18954step0 raw18954step0Labels raw18954step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw18955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18955step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18955 raw18955Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw18955 raw18955Labels = mixedMoment B raw18955step0 raw18955step0Labels := by
      have hz : ∀ j, raw18955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18955step0 = (fun i j => raw18955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18955step0 raw18955; decide +kernel
      have hl : raw18955step0Labels = raw18955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18955 raw18955Labels permutation346 hz
    mixedMoment B raw18955step0 raw18955step0Labels = mixedMoment B raw18955step1 raw18955step1Labels := by
      have ha : raw18955step1 = (fun i j => raw18955step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18955step1 raw18955step0; decide +kernel
      have hl : raw18955step1Labels = raw18955step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18955step0 raw18955step0Labels permutation146 permutation5
    mixedMoment B raw18955step1 raw18955step1Labels = mixedMoment B raw18955step2 raw18955step2Labels := by
      have ha : raw18955step2 = raw18955step1 := by apply Matrix.ext; unfold raw18955step2 raw18955step1; decide +kernel
      have hl : raw18955step1Labels = labelEmbedding1 ∘ raw18955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18955step1 raw18955step1Labels raw18955step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw18956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18956 raw18956Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw18956 raw18956Labels = mixedMoment B raw18956step0 raw18956step0Labels := by
      have hz : ∀ j, raw18956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18956step0 = (fun i j => raw18956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18956step0 raw18956; decide +kernel
      have hl : raw18956step0Labels = raw18956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18956 raw18956Labels permutation346 hz
    mixedMoment B raw18956step0 raw18956step0Labels = mixedMoment B raw18956step1 raw18956step1Labels := by
      have ha : raw18956step1 = (fun i j => raw18956step0 (permutation96 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18956step1 raw18956step0; decide +kernel
      have hl : raw18956step1Labels = raw18956step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18956step0 raw18956step0Labels permutation96 permutation7
    mixedMoment B raw18956step1 raw18956step1Labels = mixedMoment B raw18956step2 raw18956step2Labels := by
      have ha : raw18956step2 = raw18956step1 := by apply Matrix.ext; unfold raw18956step2 raw18956step1; decide +kernel
      have hl : raw18956step1Labels = labelEmbedding1 ∘ raw18956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18956step1 raw18956step1Labels raw18956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw18957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18957 raw18957Labels = mixedMoment B node3985 node3985Labels := by
  calc
    mixedMoment B raw18957 raw18957Labels = mixedMoment B raw18957step0 raw18957step0Labels := by
      have hz : ∀ j, raw18957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18957step0 = (fun i j => raw18957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18957step0 raw18957; decide +kernel
      have hl : raw18957step0Labels = raw18957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18957 raw18957Labels permutation346 hz
    mixedMoment B raw18957step0 raw18957step0Labels = mixedMoment B raw18957step1 raw18957step1Labels := by
      have ha : raw18957step1 = (fun i j => raw18957step0 (permutation96 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18957step1 raw18957step0; decide +kernel
      have hl : raw18957step1Labels = raw18957step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18957step0 raw18957step0Labels permutation96 permutation7
    mixedMoment B raw18957step1 raw18957step1Labels = mixedMoment B raw18957step2 raw18957step2Labels := by
      have ha : raw18957step2 = raw18957step1 := by apply Matrix.ext; unfold raw18957step2 raw18957step1; decide +kernel
      have hl : raw18957step1Labels = labelEmbedding1 ∘ raw18957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18957step1 raw18957step1Labels raw18957step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3985 node3985Labels := by rfl

def raw18958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18958step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18958step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18958 raw18958Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw18958 raw18958Labels = mixedMoment B raw18958step0 raw18958step0Labels := by
      have hz : ∀ j, raw18958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18958step0 = (fun i j => raw18958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18958step0 raw18958; decide +kernel
      have hl : raw18958step0Labels = raw18958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18958 raw18958Labels permutation346 hz
    mixedMoment B raw18958step0 raw18958step0Labels = mixedMoment B raw18958step1 raw18958step1Labels := by
      have ha : raw18958step1 = (fun i j => raw18958step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18958step1 raw18958step0; decide +kernel
      have hl : raw18958step1Labels = raw18958step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18958step0 raw18958step0Labels permutation40 permutation5
    mixedMoment B raw18958step1 raw18958step1Labels = mixedMoment B raw18958step2 raw18958step2Labels := by
      have ha : raw18958step2 = -raw18958step1 := by apply Matrix.ext; change ∀ i j, raw18958step2 i j = -(raw18958step1 i j); unfold raw18958step2 raw18958step1; decide +kernel
      have hl : raw18958step2Labels = raw18958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18958step2 raw18958step2Labels = mixedMoment B raw18958step3 raw18958step3Labels := by
      have ha : raw18958step3 = raw18958step2 := by apply Matrix.ext; unfold raw18958step3 raw18958step2; decide +kernel
      have hl : raw18958step2Labels = labelEmbedding1 ∘ raw18958step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18958step2 raw18958step2Labels raw18958step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw18959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18959 raw18959Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw18959 raw18959Labels = mixedMoment B raw18959step0 raw18959step0Labels := by
      have ha : raw18959step0 = (fun i j => raw18959 (permutation498 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18959step0 raw18959; decide +kernel
      have hl : raw18959step0Labels = raw18959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18959 raw18959Labels permutation498 permutation7
    mixedMoment B raw18959step0 raw18959step0Labels = mixedMoment B raw18959step1 raw18959step1Labels := by
      have ha : raw18959step1 = raw18959step0 := by apply Matrix.ext; unfold raw18959step1 raw18959step0; decide +kernel
      have hl : raw18959step0Labels = labelEmbedding1 ∘ raw18959step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18959step0 raw18959step0Labels raw18959step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw18960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw18960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18960 raw18960Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw18960 raw18960Labels = mixedMoment B raw18960step0 raw18960step0Labels := by
      have hz : ∀ j, raw18960 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18960step0 = (fun i j => raw18960 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18960step0 raw18960; decide +kernel
      have hl : raw18960step0Labels = raw18960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18960 raw18960Labels permutation346 hz
    mixedMoment B raw18960step0 raw18960step0Labels = mixedMoment B raw18960step1 raw18960step1Labels := by
      have ha : raw18960step1 = (fun i j => raw18960step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18960step1 raw18960step0; decide +kernel
      have hl : raw18960step1Labels = raw18960step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18960step0 raw18960step0Labels permutation138 permutation5
    mixedMoment B raw18960step1 raw18960step1Labels = mixedMoment B raw18960step2 raw18960step2Labels := by
      have ha : raw18960step2 = raw18960step1 := by apply Matrix.ext; unfold raw18960step2 raw18960step1; decide +kernel
      have hl : raw18960step1Labels = labelEmbedding1 ∘ raw18960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18960step1 raw18960step1Labels raw18960step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw18961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18961 raw18961Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw18961 raw18961Labels = mixedMoment B raw18961step0 raw18961step0Labels := by
      have hz : ∀ j, raw18961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18961step0 = (fun i j => raw18961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18961step0 raw18961; decide +kernel
      have hl : raw18961step0Labels = raw18961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18961 raw18961Labels permutation346 hz
    mixedMoment B raw18961step0 raw18961step0Labels = mixedMoment B raw18961step1 raw18961step1Labels := by
      have ha : raw18961step1 = (fun i j => raw18961step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18961step1 raw18961step0; decide +kernel
      have hl : raw18961step1Labels = raw18961step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18961step0 raw18961step0Labels permutation137 permutation5
    mixedMoment B raw18961step1 raw18961step1Labels = mixedMoment B raw18961step2 raw18961step2Labels := by
      have ha : raw18961step2 = raw18961step1 := by apply Matrix.ext; unfold raw18961step2 raw18961step1; decide +kernel
      have hl : raw18961step1Labels = labelEmbedding1 ∘ raw18961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18961step1 raw18961step1Labels raw18961step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw18962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18962 raw18962Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw18962 raw18962Labels = mixedMoment B raw18962step0 raw18962step0Labels := by
      have hz : ∀ j, raw18962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18962step0 = (fun i j => raw18962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18962step0 raw18962; decide +kernel
      have hl : raw18962step0Labels = raw18962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18962 raw18962Labels permutation346 hz
    mixedMoment B raw18962step0 raw18962step0Labels = mixedMoment B raw18962step1 raw18962step1Labels := by
      have ha : raw18962step1 = (fun i j => raw18962step0 (permutation95 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18962step1 raw18962step0; decide +kernel
      have hl : raw18962step1Labels = raw18962step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18962step0 raw18962step0Labels permutation95 permutation7
    mixedMoment B raw18962step1 raw18962step1Labels = mixedMoment B raw18962step2 raw18962step2Labels := by
      have ha : raw18962step2 = raw18962step1 := by apply Matrix.ext; unfold raw18962step2 raw18962step1; decide +kernel
      have hl : raw18962step1Labels = labelEmbedding1 ∘ raw18962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18962step1 raw18962step1Labels raw18962step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw18963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18963step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18963step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18963step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18963 raw18963Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw18963 raw18963Labels = mixedMoment B raw18963step0 raw18963step0Labels := by
      have ha : raw18963step0 = (fun i j => raw18963 (permutation202 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18963step0 raw18963; decide +kernel
      have hl : raw18963step0Labels = raw18963Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18963 raw18963Labels permutation202 permutation5
    mixedMoment B raw18963step0 raw18963step0Labels = mixedMoment B raw18963step1 raw18963step1Labels := by
      have ha : raw18963step1 = -raw18963step0 := by apply Matrix.ext; change ∀ i j, raw18963step1 i j = -(raw18963step0 i j); unfold raw18963step1 raw18963step0; decide +kernel
      have hl : raw18963step1Labels = raw18963step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18963step1 raw18963step1Labels = mixedMoment B raw18963step2 raw18963step2Labels := by
      have ha : raw18963step2 = raw18963step1 := by apply Matrix.ext; unfold raw18963step2 raw18963step1; decide +kernel
      have hl : raw18963step1Labels = labelEmbedding1 ∘ raw18963step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18963step1 raw18963step1Labels raw18963step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw18964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18964 raw18964Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw18964 raw18964Labels = mixedMoment B raw18964step0 raw18964step0Labels := by
      have ha : raw18964step0 = (fun i j => raw18964 (permutation645 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18964step0 raw18964; decide +kernel
      have hl : raw18964step0Labels = raw18964Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18964 raw18964Labels permutation645 permutation5
    mixedMoment B raw18964step0 raw18964step0Labels = mixedMoment B raw18964step1 raw18964step1Labels := by
      have ha : raw18964step1 = raw18964step0 := by apply Matrix.ext; unfold raw18964step1 raw18964step0; decide +kernel
      have hl : raw18964step0Labels = labelEmbedding1 ∘ raw18964step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18964step0 raw18964step0Labels raw18964step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3973 node3973Labels := by rfl

def raw18965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18965step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18965 raw18965Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw18965 raw18965Labels = mixedMoment B raw18965step0 raw18965step0Labels := by
      have ha : raw18965step0 = (fun i j => raw18965 (permutation643 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18965step0 raw18965; decide +kernel
      have hl : raw18965step0Labels = raw18965Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18965 raw18965Labels permutation643 permutation5
    mixedMoment B raw18965step0 raw18965step0Labels = mixedMoment B raw18965step1 raw18965step1Labels := by
      have ha : raw18965step1 = raw18965step0 := by apply Matrix.ext; unfold raw18965step1 raw18965step0; decide +kernel
      have hl : raw18965step0Labels = labelEmbedding1 ∘ raw18965step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18965step0 raw18965step0Labels raw18965step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw18966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18966Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18966step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18966step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18966 raw18966Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw18966 raw18966Labels = mixedMoment B raw18966step0 raw18966step0Labels := by
      have ha : raw18966step0 = (fun i j => raw18966 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18966step0 raw18966; decide +kernel
      have hl : raw18966step0Labels = raw18966Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18966 raw18966Labels permutation632 permutation5
    mixedMoment B raw18966step0 raw18966step0Labels = mixedMoment B raw18966step1 raw18966step1Labels := by
      have ha : raw18966step1 = raw18966step0 := by apply Matrix.ext; unfold raw18966step1 raw18966step0; decide +kernel
      have hl : raw18966step0Labels = labelEmbedding1 ∘ raw18966step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18966step0 raw18966step0Labels raw18966step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw18967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18967Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18967step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18967 raw18967Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw18967 raw18967Labels = mixedMoment B raw18967step0 raw18967step0Labels := by
      have ha : raw18967step0 = (fun i j => raw18967 (permutation498 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18967step0 raw18967; decide +kernel
      have hl : raw18967step0Labels = raw18967Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18967 raw18967Labels permutation498 permutation7
    mixedMoment B raw18967step0 raw18967step0Labels = mixedMoment B raw18967step1 raw18967step1Labels := by
      have ha : raw18967step1 = raw18967step0 := by apply Matrix.ext; unfold raw18967step1 raw18967step0; decide +kernel
      have hl : raw18967step0Labels = labelEmbedding1 ∘ raw18967step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18967step0 raw18967step0Labels raw18967step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw18968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18968Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18968step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw18968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw18968step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18968step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw18968step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18968 raw18968Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw18968 raw18968Labels = mixedMoment B raw18968step0 raw18968step0Labels := by
      have hz : ∀ j, raw18968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18968step0 = (fun i j => raw18968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18968step0 raw18968; decide +kernel
      have hl : raw18968step0Labels = raw18968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18968 raw18968Labels permutation346 hz
    mixedMoment B raw18968step0 raw18968step0Labels = mixedMoment B raw18968step1 raw18968step1Labels := by
      have ha : raw18968step1 = (fun i j => raw18968step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18968step1 raw18968step0; decide +kernel
      have hl : raw18968step1Labels = raw18968step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18968step0 raw18968step0Labels permutation34 permutation5
    mixedMoment B raw18968step1 raw18968step1Labels = mixedMoment B raw18968step2 raw18968step2Labels := by
      have ha : raw18968step2 = -raw18968step1 := by apply Matrix.ext; change ∀ i j, raw18968step2 i j = -(raw18968step1 i j); unfold raw18968step2 raw18968step1; decide +kernel
      have hl : raw18968step2Labels = raw18968step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18968step2 raw18968step2Labels = mixedMoment B raw18968step3 raw18968step3Labels := by
      have ha : raw18968step3 = raw18968step2 := by apply Matrix.ext; unfold raw18968step3 raw18968step2; decide +kernel
      have hl : raw18968step2Labels = labelEmbedding1 ∘ raw18968step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18968step2 raw18968step2Labels raw18968step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw18969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18969Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18969step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18969step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18969 raw18969Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw18969 raw18969Labels = mixedMoment B raw18969step0 raw18969step0Labels := by
      have hz : ∀ j, raw18969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18969step0 = (fun i j => raw18969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18969step0 raw18969; decide +kernel
      have hl : raw18969step0Labels = raw18969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18969 raw18969Labels permutation346 hz
    mixedMoment B raw18969step0 raw18969step0Labels = mixedMoment B raw18969step1 raw18969step1Labels := by
      have ha : raw18969step1 = (fun i j => raw18969step0 (permutation96 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18969step1 raw18969step0; decide +kernel
      have hl : raw18969step1Labels = raw18969step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18969step0 raw18969step0Labels permutation96 permutation7
    mixedMoment B raw18969step1 raw18969step1Labels = mixedMoment B raw18969step2 raw18969step2Labels := by
      have ha : raw18969step2 = raw18969step1 := by apply Matrix.ext; unfold raw18969step2 raw18969step1; decide +kernel
      have hl : raw18969step1Labels = labelEmbedding1 ∘ raw18969step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18969step1 raw18969step1Labels raw18969step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

def raw18970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw18970Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18970step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18970 raw18970Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw18970 raw18970Labels = mixedMoment B raw18970step0 raw18970step0Labels := by
      have ha : raw18970step0 = (fun i j => raw18970 (permutation498 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18970step0 raw18970; decide +kernel
      have hl : raw18970step0Labels = raw18970Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18970 raw18970Labels permutation498 permutation7
    mixedMoment B raw18970step0 raw18970step0Labels = mixedMoment B raw18970step1 raw18970step1Labels := by
      have ha : raw18970step1 = raw18970step0 := by apply Matrix.ext; unfold raw18970step1 raw18970step0; decide +kernel
      have hl : raw18970step0Labels = labelEmbedding1 ∘ raw18970step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18970step0 raw18970step0Labels raw18970step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw18971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18971Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw18971step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18971step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18971 raw18971Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw18971 raw18971Labels = mixedMoment B raw18971step0 raw18971step0Labels := by
      have hz : ∀ j, raw18971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18971step0 = (fun i j => raw18971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18971step0 raw18971; decide +kernel
      have hl : raw18971step0Labels = raw18971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18971 raw18971Labels permutation346 hz
    mixedMoment B raw18971step0 raw18971step0Labels = mixedMoment B raw18971step1 raw18971step1Labels := by
      have ha : raw18971step1 = (fun i j => raw18971step0 (permutation97 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18971step1 raw18971step0; decide +kernel
      have hl : raw18971step1Labels = raw18971step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18971step0 raw18971step0Labels permutation97 permutation7
    mixedMoment B raw18971step1 raw18971step1Labels = mixedMoment B raw18971step2 raw18971step2Labels := by
      have ha : raw18971step2 = raw18971step1 := by apply Matrix.ext; unfold raw18971step2 raw18971step1; decide +kernel
      have hl : raw18971step1Labels = labelEmbedding1 ∘ raw18971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18971step1 raw18971step1Labels raw18971step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw18972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18972Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw18972step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18972step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18972 raw18972Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw18972 raw18972Labels = mixedMoment B raw18972step0 raw18972step0Labels := by
      have hz : ∀ j, raw18972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18972step0 = (fun i j => raw18972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18972step0 raw18972; decide +kernel
      have hl : raw18972step0Labels = raw18972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18972 raw18972Labels permutation346 hz
    mixedMoment B raw18972step0 raw18972step0Labels = mixedMoment B raw18972step1 raw18972step1Labels := by
      have ha : raw18972step1 = (fun i j => raw18972step0 (permutation97 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18972step1 raw18972step0; decide +kernel
      have hl : raw18972step1Labels = raw18972step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18972step0 raw18972step0Labels permutation97 permutation7
    mixedMoment B raw18972step1 raw18972step1Labels = mixedMoment B raw18972step2 raw18972step2Labels := by
      have ha : raw18972step2 = raw18972step1 := by apply Matrix.ext; unfold raw18972step2 raw18972step1; decide +kernel
      have hl : raw18972step1Labels = labelEmbedding1 ∘ raw18972step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18972step1 raw18972step1Labels raw18972step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw18973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18973step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18973step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18973step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18973step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18973step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18973step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18973 raw18973Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw18973 raw18973Labels = mixedMoment B raw18973step0 raw18973step0Labels := by
      have hz : ∀ j, raw18973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18973step0 = (fun i j => raw18973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18973step0 raw18973; decide +kernel
      have hl : raw18973step0Labels = raw18973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18973 raw18973Labels permutation346 hz
    mixedMoment B raw18973step0 raw18973step0Labels = mixedMoment B raw18973step1 raw18973step1Labels := by
      have ha : raw18973step1 = (fun i j => raw18973step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18973step1 raw18973step0; decide +kernel
      have hl : raw18973step1Labels = raw18973step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18973step0 raw18973step0Labels permutation38 permutation5
    mixedMoment B raw18973step1 raw18973step1Labels = mixedMoment B raw18973step2 raw18973step2Labels := by
      have ha : raw18973step2 = -raw18973step1 := by apply Matrix.ext; change ∀ i j, raw18973step2 i j = -(raw18973step1 i j); unfold raw18973step2 raw18973step1; decide +kernel
      have hl : raw18973step2Labels = raw18973step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18973step2 raw18973step2Labels = mixedMoment B raw18973step3 raw18973step3Labels := by
      have ha : raw18973step3 = raw18973step2 := by apply Matrix.ext; unfold raw18973step3 raw18973step2; decide +kernel
      have hl : raw18973step2Labels = labelEmbedding1 ∘ raw18973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18973step2 raw18973step2Labels raw18973step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw18974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18974 raw18974Labels = mixedMoment B node3960 node3960Labels := by
  calc
    mixedMoment B raw18974 raw18974Labels = mixedMoment B raw18974step0 raw18974step0Labels := by
      have hz : ∀ j, raw18974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18974step0 = (fun i j => raw18974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18974step0 raw18974; decide +kernel
      have hl : raw18974step0Labels = raw18974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18974 raw18974Labels permutation346 hz
    mixedMoment B raw18974step0 raw18974step0Labels = mixedMoment B raw18974step1 raw18974step1Labels := by
      have ha : raw18974step1 = (fun i j => raw18974step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18974step1 raw18974step0; decide +kernel
      have hl : raw18974step1Labels = raw18974step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18974step0 raw18974step0Labels permutation150 permutation5
    mixedMoment B raw18974step1 raw18974step1Labels = mixedMoment B raw18974step2 raw18974step2Labels := by
      have ha : raw18974step2 = raw18974step1 := by apply Matrix.ext; unfold raw18974step2 raw18974step1; decide +kernel
      have hl : raw18974step1Labels = labelEmbedding1 ∘ raw18974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18974step1 raw18974step1Labels raw18974step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3960 node3960Labels := by rfl

def raw18975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18975step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18975step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18975 raw18975Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw18975 raw18975Labels = mixedMoment B raw18975step0 raw18975step0Labels := by
      have ha : raw18975step0 = (fun i j => raw18975 (permutation676 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18975step0 raw18975; decide +kernel
      have hl : raw18975step0Labels = raw18975Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18975 raw18975Labels permutation676 permutation5
    mixedMoment B raw18975step0 raw18975step0Labels = mixedMoment B raw18975step1 raw18975step1Labels := by
      have ha : raw18975step1 = raw18975step0 := by apply Matrix.ext; unfold raw18975step1 raw18975step0; decide +kernel
      have hl : raw18975step0Labels = labelEmbedding1 ∘ raw18975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18975step0 raw18975step0Labels raw18975step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw18976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw18976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18976step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18976 raw18976Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw18976 raw18976Labels = mixedMoment B raw18976step0 raw18976step0Labels := by
      have hz : ∀ j, raw18976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18976step0 = (fun i j => raw18976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18976step0 raw18976; decide +kernel
      have hl : raw18976step0Labels = raw18976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18976 raw18976Labels permutation346 hz
    mixedMoment B raw18976step0 raw18976step0Labels = mixedMoment B raw18976step1 raw18976step1Labels := by
      have ha : raw18976step1 = (fun i j => raw18976step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18976step1 raw18976step0; decide +kernel
      have hl : raw18976step1Labels = raw18976step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18976step0 raw18976step0Labels permutation148 permutation5
    mixedMoment B raw18976step1 raw18976step1Labels = mixedMoment B raw18976step2 raw18976step2Labels := by
      have ha : raw18976step2 = raw18976step1 := by apply Matrix.ext; unfold raw18976step2 raw18976step1; decide +kernel
      have hl : raw18976step1Labels = labelEmbedding1 ∘ raw18976step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18976step1 raw18976step1Labels raw18976step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw18977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw18977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw18977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw18977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18977 raw18977Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw18977 raw18977Labels = mixedMoment B raw18977step0 raw18977step0Labels := by
      have hz : ∀ j, raw18977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18977step0 = (fun i j => raw18977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18977step0 raw18977; decide +kernel
      have hl : raw18977step0Labels = raw18977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18977 raw18977Labels permutation346 hz
    mixedMoment B raw18977step0 raw18977step0Labels = mixedMoment B raw18977step1 raw18977step1Labels := by
      have ha : raw18977step1 = (fun i j => raw18977step0 (permutation97 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18977step1 raw18977step0; decide +kernel
      have hl : raw18977step1Labels = raw18977step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18977step0 raw18977step0Labels permutation97 permutation7
    mixedMoment B raw18977step1 raw18977step1Labels = mixedMoment B raw18977step2 raw18977step2Labels := by
      have ha : raw18977step2 = raw18977step1 := by apply Matrix.ext; unfold raw18977step2 raw18977step1; decide +kernel
      have hl : raw18977step1Labels = labelEmbedding1 ∘ raw18977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18977step1 raw18977step1Labels raw18977step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw18978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18978step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw18978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw18978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18978 raw18978Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw18978 raw18978Labels = mixedMoment B raw18978step0 raw18978step0Labels := by
      have hz : ∀ j, raw18978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18978step0 = (fun i j => raw18978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18978step0 raw18978; decide +kernel
      have hl : raw18978step0Labels = raw18978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18978 raw18978Labels permutation346 hz
    mixedMoment B raw18978step0 raw18978step0Labels = mixedMoment B raw18978step1 raw18978step1Labels := by
      have ha : raw18978step1 = (fun i j => raw18978step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18978step1 raw18978step0; decide +kernel
      have hl : raw18978step1Labels = raw18978step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18978step0 raw18978step0Labels permutation149 permutation5
    mixedMoment B raw18978step1 raw18978step1Labels = mixedMoment B raw18978step2 raw18978step2Labels := by
      have ha : raw18978step2 = raw18978step1 := by apply Matrix.ext; unfold raw18978step2 raw18978step1; decide +kernel
      have hl : raw18978step1Labels = labelEmbedding1 ∘ raw18978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18978step1 raw18978step1Labels raw18978step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw18979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18979 raw18979Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw18979 raw18979Labels = mixedMoment B raw18979step0 raw18979step0Labels := by
      have hz : ∀ j, raw18979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18979step0 = (fun i j => raw18979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18979step0 raw18979; decide +kernel
      have hl : raw18979step0Labels = raw18979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18979 raw18979Labels permutation346 hz
    mixedMoment B raw18979step0 raw18979step0Labels = mixedMoment B raw18979step1 raw18979step1Labels := by
      have ha : raw18979step1 = (fun i j => raw18979step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18979step1 raw18979step0; decide +kernel
      have hl : raw18979step1Labels = raw18979step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18979step0 raw18979step0Labels permutation150 permutation5
    mixedMoment B raw18979step1 raw18979step1Labels = mixedMoment B raw18979step2 raw18979step2Labels := by
      have ha : raw18979step2 = raw18979step1 := by apply Matrix.ext; unfold raw18979step2 raw18979step1; decide +kernel
      have hl : raw18979step1Labels = labelEmbedding1 ∘ raw18979step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18979step1 raw18979step1Labels raw18979step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw18980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18980step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18980 raw18980Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw18980 raw18980Labels = mixedMoment B raw18980step0 raw18980step0Labels := by
      have ha : raw18980step0 = (fun i j => raw18980 (permutation676 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18980step0 raw18980; decide +kernel
      have hl : raw18980step0Labels = raw18980Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18980 raw18980Labels permutation676 permutation5
    mixedMoment B raw18980step0 raw18980step0Labels = mixedMoment B raw18980step1 raw18980step1Labels := by
      have ha : raw18980step1 = raw18980step0 := by apply Matrix.ext; unfold raw18980step1 raw18980step0; decide +kernel
      have hl : raw18980step0Labels = labelEmbedding1 ∘ raw18980step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18980step0 raw18980step0Labels raw18980step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw18981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw18981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18981step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18981 raw18981Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw18981 raw18981Labels = mixedMoment B raw18981step0 raw18981step0Labels := by
      have hz : ∀ j, raw18981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18981step0 = (fun i j => raw18981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18981step0 raw18981; decide +kernel
      have hl : raw18981step0Labels = raw18981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18981 raw18981Labels permutation346 hz
    mixedMoment B raw18981step0 raw18981step0Labels = mixedMoment B raw18981step1 raw18981step1Labels := by
      have ha : raw18981step1 = (fun i j => raw18981step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18981step1 raw18981step0; decide +kernel
      have hl : raw18981step1Labels = raw18981step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18981step0 raw18981step0Labels permutation148 permutation5
    mixedMoment B raw18981step1 raw18981step1Labels = mixedMoment B raw18981step2 raw18981step2Labels := by
      have ha : raw18981step2 = raw18981step1 := by apply Matrix.ext; unfold raw18981step2 raw18981step1; decide +kernel
      have hl : raw18981step1Labels = labelEmbedding1 ∘ raw18981step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18981step1 raw18981step1Labels raw18981step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw18982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw18982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw18982step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18982 raw18982Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw18982 raw18982Labels = mixedMoment B raw18982step0 raw18982step0Labels := by
      have hz : ∀ j, raw18982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18982step0 = (fun i j => raw18982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18982step0 raw18982; decide +kernel
      have hl : raw18982step0Labels = raw18982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18982 raw18982Labels permutation346 hz
    mixedMoment B raw18982step0 raw18982step0Labels = mixedMoment B raw18982step1 raw18982step1Labels := by
      have ha : raw18982step1 = (fun i j => raw18982step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18982step1 raw18982step0; decide +kernel
      have hl : raw18982step1Labels = raw18982step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18982step0 raw18982step0Labels permutation137 permutation5
    mixedMoment B raw18982step1 raw18982step1Labels = mixedMoment B raw18982step2 raw18982step2Labels := by
      have ha : raw18982step2 = raw18982step1 := by apply Matrix.ext; unfold raw18982step2 raw18982step1; decide +kernel
      have hl : raw18982step1Labels = labelEmbedding1 ∘ raw18982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18982step1 raw18982step1Labels raw18982step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw18983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18983step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18983step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18983 raw18983Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18983 raw18983Labels = mixedMoment B raw18983step0 raw18983step0Labels := by
      have hz : ∀ j, raw18983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18983step0 = (fun i j => raw18983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18983step0 raw18983; decide +kernel
      have hl : raw18983step0Labels = raw18983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18983 raw18983Labels permutation346 hz
    mixedMoment B raw18983step0 raw18983step0Labels = mixedMoment B raw18983step1 raw18983step1Labels := by
      have ha : raw18983step1 = (fun i j => raw18983step0 (permutation61 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18983step1 raw18983step0; decide +kernel
      have hl : raw18983step1Labels = raw18983step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18983step0 raw18983step0Labels permutation61 permutation3
    mixedMoment B raw18983step1 raw18983step1Labels = mixedMoment B raw18983step2 raw18983step2Labels := by
      have ha : raw18983step2 = raw18983step1 := by apply Matrix.ext; unfold raw18983step2 raw18983step1; decide +kernel
      have hl : raw18983step1Labels = labelEmbedding6 ∘ raw18983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18983step1 raw18983step1Labels raw18983step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw18984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18984step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18984 raw18984Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw18984 raw18984Labels = mixedMoment B raw18984step0 raw18984step0Labels := by
      have ha : raw18984step0 = (fun i j => raw18984 (permutation487 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18984step0 raw18984; decide +kernel
      have hl : raw18984step0Labels = raw18984Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18984 raw18984Labels permutation487 permutation5
    mixedMoment B raw18984step0 raw18984step0Labels = mixedMoment B raw18984step1 raw18984step1Labels := by
      have ha : raw18984step1 = raw18984step0 := by apply Matrix.ext; unfold raw18984step1 raw18984step0; decide +kernel
      have hl : raw18984step0Labels = labelEmbedding8 ∘ raw18984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18984step0 raw18984step0Labels raw18984step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw18985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18985step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18985step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18985 raw18985Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18985 raw18985Labels = mixedMoment B raw18985step0 raw18985step0Labels := by
      have hz : ∀ j, raw18985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18985step0 = (fun i j => raw18985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18985step0 raw18985; decide +kernel
      have hl : raw18985step0Labels = raw18985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18985 raw18985Labels permutation346 hz
    mixedMoment B raw18985step0 raw18985step0Labels = mixedMoment B raw18985step1 raw18985step1Labels := by
      have ha : raw18985step1 = (fun i j => raw18985step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18985step1 raw18985step0; decide +kernel
      have hl : raw18985step1Labels = raw18985step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18985step0 raw18985step0Labels permutation138 permutation6
    mixedMoment B raw18985step1 raw18985step1Labels = mixedMoment B raw18985step2 raw18985step2Labels := by
      have ha : raw18985step2 = raw18985step1 := by apply Matrix.ext; unfold raw18985step2 raw18985step1; decide +kernel
      have hl : raw18985step1Labels = labelEmbedding9 ∘ raw18985step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18985step1 raw18985step1Labels raw18985step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw18986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18986step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18986step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18986step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18986 raw18986Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw18986 raw18986Labels = mixedMoment B raw18986step0 raw18986step0Labels := by
      have hz : ∀ j, raw18986 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18986step0 = (fun i j => raw18986 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18986step0 raw18986; decide +kernel
      have hl : raw18986step0Labels = raw18986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18986 raw18986Labels permutation520 hz
    mixedMoment B raw18986step0 raw18986step0Labels = mixedMoment B raw18986step1 raw18986step1Labels := by
      have hz : ∀ j, raw18986step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18986step1 = (fun i j => raw18986step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18986step1 raw18986step0; decide +kernel
      have hl : raw18986step1Labels = raw18986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18986step0 raw18986step0Labels permutation80 hz
    mixedMoment B raw18986step1 raw18986step1Labels = mixedMoment B raw18986step2 raw18986step2Labels := by
      have ha : raw18986step2 = (fun i j => raw18986step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18986step2 raw18986step1; decide +kernel
      have hl : raw18986step2Labels = raw18986step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18986step1 raw18986step1Labels permutation20 permutation4
    mixedMoment B raw18986step2 raw18986step2Labels = mixedMoment B raw18986step3 raw18986step3Labels := by
      have ha : raw18986step3 = raw18986step2 := by apply Matrix.ext; unfold raw18986step3 raw18986step2; decide +kernel
      have hl : raw18986step2Labels = labelEmbedding7 ∘ raw18986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18986step2 raw18986step2Labels raw18986step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw18987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw18987step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18987step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18987step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18987 raw18987Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18987 raw18987Labels = mixedMoment B raw18987step0 raw18987step0Labels := by
      have hz : ∀ j, raw18987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18987step0 = (fun i j => raw18987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18987step0 raw18987; decide +kernel
      have hl : raw18987step0Labels = raw18987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18987 raw18987Labels permutation346 hz
    mixedMoment B raw18987step0 raw18987step0Labels = mixedMoment B raw18987step1 raw18987step1Labels := by
      have ha : raw18987step1 = (fun i j => raw18987step0 (permutation135 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18987step1 raw18987step0; decide +kernel
      have hl : raw18987step1Labels = raw18987step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18987step0 raw18987step0Labels permutation135 permutation4
    mixedMoment B raw18987step1 raw18987step1Labels = mixedMoment B raw18987step2 raw18987step2Labels := by
      have ha : raw18987step2 = -raw18987step1 := by apply Matrix.ext; change ∀ i j, raw18987step2 i j = -(raw18987step1 i j); unfold raw18987step2 raw18987step1; decide +kernel
      have hl : raw18987step2Labels = raw18987step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18987step2 raw18987step2Labels = mixedMoment B raw18987step3 raw18987step3Labels := by
      have ha : raw18987step3 = raw18987step2 := by apply Matrix.ext; unfold raw18987step3 raw18987step2; decide +kernel
      have hl : raw18987step2Labels = labelEmbedding7 ∘ raw18987step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18987step2 raw18987step2Labels raw18987step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw18988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18988step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18988step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18988 raw18988Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw18988 raw18988Labels = mixedMoment B raw18988step0 raw18988step0Labels := by
      have ha : raw18988step0 = (fun i j => raw18988 (permutation284 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18988step0 raw18988; decide +kernel
      have hl : raw18988step0Labels = raw18988Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18988 raw18988Labels permutation284 permutation3
    mixedMoment B raw18988step0 raw18988step0Labels = mixedMoment B raw18988step1 raw18988step1Labels := by
      have ha : raw18988step1 = raw18988step0 := by apply Matrix.ext; unfold raw18988step1 raw18988step0; decide +kernel
      have hl : raw18988step0Labels = labelEmbedding6 ∘ raw18988step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18988step0 raw18988step0Labels raw18988step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

def raw18989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18989step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18989 raw18989Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw18989 raw18989Labels = mixedMoment B raw18989step0 raw18989step0Labels := by
      have ha : raw18989step0 = (fun i j => raw18989 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18989step0 raw18989; decide +kernel
      have hl : raw18989step0Labels = raw18989Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18989 raw18989Labels permutation162 permutation3
    mixedMoment B raw18989step0 raw18989step0Labels = mixedMoment B raw18989step1 raw18989step1Labels := by
      have ha : raw18989step1 = raw18989step0 := by apply Matrix.ext; unfold raw18989step1 raw18989step0; decide +kernel
      have hl : raw18989step0Labels = labelEmbedding6 ∘ raw18989step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18989step0 raw18989step0Labels raw18989step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw18990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18990step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18990step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18990 raw18990Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw18990 raw18990Labels = mixedMoment B raw18990step0 raw18990step0Labels := by
      have hz : ∀ j, raw18990 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18990step0 = (fun i j => raw18990 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18990step0 raw18990; decide +kernel
      have hl : raw18990step0Labels = raw18990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18990 raw18990Labels permutation520 hz
    mixedMoment B raw18990step0 raw18990step0Labels = mixedMoment B raw18990step1 raw18990step1Labels := by
      have ha : raw18990step1 = (fun i j => raw18990step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18990step1 raw18990step0; decide +kernel
      have hl : raw18990step1Labels = raw18990step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18990step0 raw18990step0Labels permutation36 permutation3
    mixedMoment B raw18990step1 raw18990step1Labels = mixedMoment B raw18990step2 raw18990step2Labels := by
      have ha : raw18990step2 = raw18990step1 := by apply Matrix.ext; unfold raw18990step2 raw18990step1; decide +kernel
      have hl : raw18990step1Labels = labelEmbedding6 ∘ raw18990step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18990step1 raw18990step1Labels raw18990step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw18991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw18991step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18991step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18991step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18991 raw18991Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18991 raw18991Labels = mixedMoment B raw18991step0 raw18991step0Labels := by
      have ha : raw18991step0 = (fun i j => raw18991 (permutation603 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18991step0 raw18991; decide +kernel
      have hl : raw18991step0Labels = raw18991Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18991 raw18991Labels permutation603 permutation4
    mixedMoment B raw18991step0 raw18991step0Labels = mixedMoment B raw18991step1 raw18991step1Labels := by
      have ha : raw18991step1 = -raw18991step0 := by apply Matrix.ext; change ∀ i j, raw18991step1 i j = -(raw18991step0 i j); unfold raw18991step1 raw18991step0; decide +kernel
      have hl : raw18991step1Labels = raw18991step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18991step1 raw18991step1Labels = mixedMoment B raw18991step2 raw18991step2Labels := by
      have ha : raw18991step2 = raw18991step1 := by apply Matrix.ext; unfold raw18991step2 raw18991step1; decide +kernel
      have hl : raw18991step1Labels = labelEmbedding7 ∘ raw18991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18991step1 raw18991step1Labels raw18991step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw18992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18992step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18992step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18992 raw18992Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw18992 raw18992Labels = mixedMoment B raw18992step0 raw18992step0Labels := by
      have hz : ∀ j, raw18992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18992step0 = (fun i j => raw18992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18992step0 raw18992; decide +kernel
      have hl : raw18992step0Labels = raw18992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18992 raw18992Labels permutation346 hz
    mixedMoment B raw18992step0 raw18992step0Labels = mixedMoment B raw18992step1 raw18992step1Labels := by
      have ha : raw18992step1 = (fun i j => raw18992step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18992step1 raw18992step0; decide +kernel
      have hl : raw18992step1Labels = raw18992step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18992step0 raw18992step0Labels permutation96 permutation5
    mixedMoment B raw18992step1 raw18992step1Labels = mixedMoment B raw18992step2 raw18992step2Labels := by
      have ha : raw18992step2 = raw18992step1 := by apply Matrix.ext; unfold raw18992step2 raw18992step1; decide +kernel
      have hl : raw18992step1Labels = labelEmbedding8 ∘ raw18992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18992step1 raw18992step1Labels raw18992step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw18993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18993step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18993 raw18993Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw18993 raw18993Labels = mixedMoment B raw18993step0 raw18993step0Labels := by
      have ha : raw18993step0 = (fun i j => raw18993 (permutation502 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18993step0 raw18993; decide +kernel
      have hl : raw18993step0Labels = raw18993Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18993 raw18993Labels permutation502 permutation5
    mixedMoment B raw18993step0 raw18993step0Labels = mixedMoment B raw18993step1 raw18993step1Labels := by
      have ha : raw18993step1 = raw18993step0 := by apply Matrix.ext; unfold raw18993step1 raw18993step0; decide +kernel
      have hl : raw18993step0Labels = labelEmbedding8 ∘ raw18993step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18993step0 raw18993step0Labels raw18993step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

def raw18994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw18994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18994step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18994step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18994 raw18994Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw18994 raw18994Labels = mixedMoment B raw18994step0 raw18994step0Labels := by
      have hz : ∀ j, raw18994 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18994step0 = (fun i j => raw18994 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18994step0 raw18994; decide +kernel
      have hl : raw18994step0Labels = raw18994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18994 raw18994Labels permutation520 hz
    mixedMoment B raw18994step0 raw18994step0Labels = mixedMoment B raw18994step1 raw18994step1Labels := by
      have hz : ∀ j, raw18994step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18994step1 = (fun i j => raw18994step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18994step1 raw18994step0; decide +kernel
      have hl : raw18994step1Labels = raw18994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18994step0 raw18994step0Labels permutation80 hz
    mixedMoment B raw18994step1 raw18994step1Labels = mixedMoment B raw18994step2 raw18994step2Labels := by
      have ha : raw18994step2 = (fun i j => raw18994step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18994step2 raw18994step1; decide +kernel
      have hl : raw18994step2Labels = raw18994step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18994step1 raw18994step1Labels permutation25 permutation5
    mixedMoment B raw18994step2 raw18994step2Labels = mixedMoment B raw18994step3 raw18994step3Labels := by
      have ha : raw18994step3 = raw18994step2 := by apply Matrix.ext; unfold raw18994step3 raw18994step2; decide +kernel
      have hl : raw18994step2Labels = labelEmbedding8 ∘ raw18994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18994step2 raw18994step2Labels raw18994step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw18995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw18995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18995step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18995 raw18995Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw18995 raw18995Labels = mixedMoment B raw18995step0 raw18995step0Labels := by
      have hz : ∀ j, raw18995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18995step0 = (fun i j => raw18995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18995step0 raw18995; decide +kernel
      have hl : raw18995step0Labels = raw18995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18995 raw18995Labels permutation346 hz
    mixedMoment B raw18995step0 raw18995step0Labels = mixedMoment B raw18995step1 raw18995step1Labels := by
      have ha : raw18995step1 = (fun i j => raw18995step0 (permutation94 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18995step1 raw18995step0; decide +kernel
      have hl : raw18995step1Labels = raw18995step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18995step0 raw18995step0Labels permutation94 permutation5
    mixedMoment B raw18995step1 raw18995step1Labels = mixedMoment B raw18995step2 raw18995step2Labels := by
      have ha : raw18995step2 = raw18995step1 := by apply Matrix.ext; unfold raw18995step2 raw18995step1; decide +kernel
      have hl : raw18995step1Labels = labelEmbedding8 ∘ raw18995step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18995step1 raw18995step1Labels raw18995step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw18996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18996step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18996step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18996 raw18996Labels = mixedMoment B node5364 node5364Labels := by
  calc
    mixedMoment B raw18996 raw18996Labels = mixedMoment B raw18996step0 raw18996step0Labels := by
      have hz : ∀ j, raw18996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18996step0 = (fun i j => raw18996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18996step0 raw18996; decide +kernel
      have hl : raw18996step0Labels = raw18996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18996 raw18996Labels permutation346 hz
    mixedMoment B raw18996step0 raw18996step0Labels = mixedMoment B raw18996step1 raw18996step1Labels := by
      have ha : raw18996step1 = (fun i j => raw18996step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18996step1 raw18996step0; decide +kernel
      have hl : raw18996step1Labels = raw18996step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18996step0 raw18996step0Labels permutation60 permutation3
    mixedMoment B raw18996step1 raw18996step1Labels = mixedMoment B raw18996step2 raw18996step2Labels := by
      have ha : raw18996step2 = raw18996step1 := by apply Matrix.ext; unfold raw18996step2 raw18996step1; decide +kernel
      have hl : raw18996step1Labels = labelEmbedding6 ∘ raw18996step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18996step1 raw18996step1Labels raw18996step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5364 node5364Labels := by rfl

def raw18997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18997step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw18997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18997 raw18997Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw18997 raw18997Labels = mixedMoment B raw18997step0 raw18997step0Labels := by
      have ha : raw18997step0 = (fun i j => raw18997 (permutation566 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18997step0 raw18997; decide +kernel
      have hl : raw18997step0Labels = raw18997Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18997 raw18997Labels permutation566 permutation5
    mixedMoment B raw18997step0 raw18997step0Labels = mixedMoment B raw18997step1 raw18997step1Labels := by
      have ha : raw18997step1 = raw18997step0 := by apply Matrix.ext; unfold raw18997step1 raw18997step0; decide +kernel
      have hl : raw18997step0Labels = labelEmbedding8 ∘ raw18997step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18997step0 raw18997step0Labels raw18997step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

def raw18998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18998step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18998step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18998 raw18998Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18998 raw18998Labels = mixedMoment B raw18998step0 raw18998step0Labels := by
      have hz : ∀ j, raw18998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18998step0 = (fun i j => raw18998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18998step0 raw18998; decide +kernel
      have hl : raw18998step0Labels = raw18998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18998 raw18998Labels permutation346 hz
    mixedMoment B raw18998step0 raw18998step0Labels = mixedMoment B raw18998step1 raw18998step1Labels := by
      have ha : raw18998step1 = (fun i j => raw18998step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18998step1 raw18998step0; decide +kernel
      have hl : raw18998step1Labels = raw18998step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18998step0 raw18998step0Labels permutation121 permutation5
    mixedMoment B raw18998step1 raw18998step1Labels = mixedMoment B raw18998step2 raw18998step2Labels := by
      have ha : raw18998step2 = raw18998step1 := by apply Matrix.ext; unfold raw18998step2 raw18998step1; decide +kernel
      have hl : raw18998step1Labels = labelEmbedding8 ∘ raw18998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18998step1 raw18998step1Labels raw18998step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw18999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw18999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw18999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18999step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18999 raw18999Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw18999 raw18999Labels = mixedMoment B raw18999step0 raw18999step0Labels := by
      have hz : ∀ j, raw18999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18999step0 = (fun i j => raw18999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18999step0 raw18999; decide +kernel
      have hl : raw18999step0Labels = raw18999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18999 raw18999Labels permutation346 hz
    mixedMoment B raw18999step0 raw18999step0Labels = mixedMoment B raw18999step1 raw18999step1Labels := by
      have ha : raw18999step1 = (fun i j => raw18999step0 (permutation118 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18999step1 raw18999step0; decide +kernel
      have hl : raw18999step1Labels = raw18999step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18999step0 raw18999step0Labels permutation118 permutation5
    mixedMoment B raw18999step1 raw18999step1Labels = mixedMoment B raw18999step2 raw18999step2Labels := by
      have ha : raw18999step2 = raw18999step1 := by apply Matrix.ext; unfold raw18999step2 raw18999step1; decide +kernel
      have hl : raw18999step1Labels = labelEmbedding8 ∘ raw18999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18999step1 raw18999step1Labels raw18999step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw19000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw19000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw19000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19000step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19000 raw19000Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw19000 raw19000Labels = mixedMoment B raw19000step0 raw19000step0Labels := by
      have hz : ∀ j, raw19000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19000step0 = (fun i j => raw19000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19000step0 raw19000; decide +kernel
      have hl : raw19000step0Labels = raw19000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19000 raw19000Labels permutation346 hz
    mixedMoment B raw19000step0 raw19000step0Labels = mixedMoment B raw19000step1 raw19000step1Labels := by
      have ha : raw19000step1 = (fun i j => raw19000step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19000step1 raw19000step0; decide +kernel
      have hl : raw19000step1Labels = raw19000step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19000step0 raw19000step0Labels permutation58 permutation3
    mixedMoment B raw19000step1 raw19000step1Labels = mixedMoment B raw19000step2 raw19000step2Labels := by
      have ha : raw19000step2 = raw19000step1 := by apply Matrix.ext; unfold raw19000step2 raw19000step1; decide +kernel
      have hl : raw19000step1Labels = labelEmbedding6 ∘ raw19000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19000step1 raw19000step1Labels raw19000step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw19001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw19001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw19001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19001 raw19001Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw19001 raw19001Labels = mixedMoment B raw19001step0 raw19001step0Labels := by
      have ha : raw19001step0 = (fun i j => raw19001 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19001step0 raw19001; decide +kernel
      have hl : raw19001step0Labels = raw19001Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19001 raw19001Labels permutation686 permutation2
    mixedMoment B raw19001step0 raw19001step0Labels = mixedMoment B raw19001step1 raw19001step1Labels := by
      have ha : raw19001step1 = -raw19001step0 := by apply Matrix.ext; change ∀ i j, raw19001step1 i j = -(raw19001step0 i j); unfold raw19001step1 raw19001step0; decide +kernel
      have hl : raw19001step1Labels = raw19001step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw19002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw19002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw19002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw19002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw19002step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19002step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19002 raw19002Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw19002 raw19002Labels = mixedMoment B raw19002step0 raw19002step0Labels := by
      have hz : ∀ j, raw19002 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19002step0 = (fun i j => raw19002 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19002step0 raw19002; decide +kernel
      have hl : raw19002step0Labels = raw19002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19002 raw19002Labels permutation520 hz
    mixedMoment B raw19002step0 raw19002step0Labels = mixedMoment B raw19002step1 raw19002step1Labels := by
      have hz : ∀ j, raw19002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19002step1 = (fun i j => raw19002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19002step1 raw19002step0; decide +kernel
      have hl : raw19002step1Labels = raw19002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19002step0 raw19002step0Labels permutation80 hz
    mixedMoment B raw19002step1 raw19002step1Labels = mixedMoment B raw19002step2 raw19002step2Labels := by
      have ha : raw19002step2 = (fun i j => raw19002step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19002step2 raw19002step1; decide +kernel
      have hl : raw19002step2Labels = raw19002step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19002step1 raw19002step1Labels permutation31 permutation2
    mixedMoment B raw19002step2 raw19002step2Labels = mixedMoment B raw19002step3 raw19002step3Labels := by
      have ha : raw19002step3 = -raw19002step2 := by apply Matrix.ext; change ∀ i j, raw19002step3 i j = -(raw19002step2 i j); unfold raw19002step3 raw19002step2; decide +kernel
      have hl : raw19002step3Labels = raw19002step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw19003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19003 raw19003Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw19003 raw19003Labels = mixedMoment B raw19003step0 raw19003step0Labels := by
      have hz : ∀ j, raw19003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19003step0 = (fun i j => raw19003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19003step0 raw19003; decide +kernel
      have hl : raw19003step0Labels = raw19003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19003 raw19003Labels permutation346 hz
    mixedMoment B raw19003step0 raw19003step0Labels = mixedMoment B raw19003step1 raw19003step1Labels := by
      have ha : raw19003step1 = (fun i j => raw19003step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19003step1 raw19003step0; decide +kernel
      have hl : raw19003step1Labels = raw19003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19003step0 raw19003step0Labels permutation60 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw19004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19004 raw19004Labels = mixedMoment B node5497 node5497Labels := by
  calc
    mixedMoment B raw19004 raw19004Labels = mixedMoment B raw19004step0 raw19004step0Labels := by
      have ha : raw19004step0 = (fun i j => raw19004 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19004step0 raw19004; decide +kernel
      have hl : raw19004step0Labels = raw19004Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19004 raw19004Labels permutation156 permutation2
    _ = mixedMoment B node5497 node5497Labels := by rfl

def raw19005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19005 raw19005Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw19005 raw19005Labels = mixedMoment B raw19005step0 raw19005step0Labels := by
      have hz : ∀ j, raw19005 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19005step0 = (fun i j => raw19005 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19005step0 raw19005; decide +kernel
      have hl : raw19005step0Labels = raw19005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19005 raw19005Labels permutation346 hz
    mixedMoment B raw19005step0 raw19005step0Labels = mixedMoment B raw19005step1 raw19005step1Labels := by
      have ha : raw19005step1 = (fun i j => raw19005step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19005step1 raw19005step0; decide +kernel
      have hl : raw19005step1Labels = raw19005step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19005step0 raw19005step0Labels permutation33 permutation2
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw19006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19006 raw19006Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw19006 raw19006Labels = mixedMoment B raw19006step0 raw19006step0Labels := by
      have hz : ∀ j, raw19006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19006step0 = (fun i j => raw19006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19006step0 raw19006; decide +kernel
      have hl : raw19006step0Labels = raw19006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19006 raw19006Labels permutation346 hz
    mixedMoment B raw19006step0 raw19006step0Labels = mixedMoment B raw19006step1 raw19006step1Labels := by
      have ha : raw19006step1 = (fun i j => raw19006step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19006step1 raw19006step0; decide +kernel
      have hl : raw19006step1Labels = raw19006step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19006step0 raw19006step0Labels permutation35 permutation2
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw19007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19007step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19007step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw19007step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw19007step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19007 raw19007Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw19007 raw19007Labels = mixedMoment B raw19007step0 raw19007step0Labels := by
      have hz : ∀ j, raw19007 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19007step0 = (fun i j => raw19007 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19007step0 raw19007; decide +kernel
      have hl : raw19007step0Labels = raw19007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19007 raw19007Labels permutation590 hz
    mixedMoment B raw19007step0 raw19007step0Labels = mixedMoment B raw19007step1 raw19007step1Labels := by
      have hz : ∀ j, raw19007step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19007step1 = (fun i j => raw19007step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19007step1 raw19007step0; decide +kernel
      have hl : raw19007step1Labels = raw19007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19007step0 raw19007step0Labels permutation80 hz
    mixedMoment B raw19007step1 raw19007step1Labels = mixedMoment B raw19007step2 raw19007step2Labels := by
      have hz : ∀ i, raw19007step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw19007step2 = (fun i j => raw19007step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw19007step2 raw19007step1; decide +kernel
      have hl : raw19007step2Labels = (fun j => raw19007step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19007step1 raw19007step1Labels permutation4 hz
    mixedMoment B raw19007step2 raw19007step2Labels = mixedMoment B raw19007step3 raw19007step3Labels := by
      have ha : raw19007step3 = raw19007step2 := by apply Matrix.ext; unfold raw19007step3 raw19007step2; decide +kernel
      have hl : raw19007step2Labels = labelEmbedding2 ∘ raw19007step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19007step2 raw19007step2Labels raw19007step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw19008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19008step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19008 raw19008Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19008 raw19008Labels = mixedMoment B raw19008step0 raw19008step0Labels := by
      have ha : raw19008step0 = (fun i j => raw19008 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19008step0 raw19008; decide +kernel
      have hl : raw19008step0Labels = raw19008Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19008 raw19008Labels permutation176 permutation3
    mixedMoment B raw19008step0 raw19008step0Labels = mixedMoment B raw19008step1 raw19008step1Labels := by
      have ha : raw19008step1 = raw19008step0 := by apply Matrix.ext; unfold raw19008step1 raw19008step0; decide +kernel
      have hl : raw19008step0Labels = labelEmbedding6 ∘ raw19008step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19008step0 raw19008step0Labels raw19008step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19009step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19009 raw19009Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19009 raw19009Labels = mixedMoment B raw19009step0 raw19009step0Labels := by
      have hz : ∀ j, raw19009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19009step0 = (fun i j => raw19009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19009step0 raw19009; decide +kernel
      have hl : raw19009step0Labels = raw19009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19009 raw19009Labels permutation346 hz
    mixedMoment B raw19009step0 raw19009step0Labels = mixedMoment B raw19009step1 raw19009step1Labels := by
      have ha : raw19009step1 = (fun i j => raw19009step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19009step1 raw19009step0; decide +kernel
      have hl : raw19009step1Labels = raw19009step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19009step0 raw19009step0Labels permutation35 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw19010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19010step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19010 raw19010Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw19010 raw19010Labels = mixedMoment B raw19010step0 raw19010step0Labels := by
      have hz : ∀ j, raw19010 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19010step0 = (fun i j => raw19010 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19010step0 raw19010; decide +kernel
      have hl : raw19010step0Labels = raw19010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19010 raw19010Labels permutation590 hz
    mixedMoment B raw19010step0 raw19010step0Labels = mixedMoment B raw19010step1 raw19010step1Labels := by
      have hz : ∀ j, raw19010step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19010step1 = (fun i j => raw19010step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19010step1 raw19010step0; decide +kernel
      have hl : raw19010step1Labels = raw19010step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19010step0 raw19010step0Labels permutation80 hz
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw19011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19011step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19011step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19011 raw19011Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw19011 raw19011Labels = mixedMoment B raw19011step0 raw19011step0Labels := by
      have ha : raw19011step0 = (fun i j => raw19011 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19011step0 raw19011; decide +kernel
      have hl : raw19011step0Labels = raw19011Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19011 raw19011Labels permutation160 permutation3
    mixedMoment B raw19011step0 raw19011step0Labels = mixedMoment B raw19011step1 raw19011step1Labels := by
      have ha : raw19011step1 = raw19011step0 := by apply Matrix.ext; unfold raw19011step1 raw19011step0; decide +kernel
      have hl : raw19011step0Labels = labelEmbedding6 ∘ raw19011step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19011step0 raw19011step0Labels raw19011step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw19012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19012 raw19012Labels = mixedMoment B node5464 node5464Labels := by
  calc
    mixedMoment B raw19012 raw19012Labels = mixedMoment B raw19012step0 raw19012step0Labels := by
      have ha : raw19012step0 = (fun i j => raw19012 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19012step0 raw19012; decide +kernel
      have hl : raw19012step0Labels = raw19012Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19012 raw19012Labels permutation156 permutation2
    _ = mixedMoment B node5464 node5464Labels := by rfl

def raw19013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19013 raw19013Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19013 raw19013Labels = mixedMoment B raw19013step0 raw19013step0Labels := by
      have ha : raw19013step0 = (fun i j => raw19013 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19013step0 raw19013; decide +kernel
      have hl : raw19013step0Labels = raw19013Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19013 raw19013Labels permutation159 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19014 raw19014Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19014 raw19014Labels = mixedMoment B raw19014step0 raw19014step0Labels := by
      have ha : raw19014step0 = (fun i j => raw19014 (permutation165 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19014step0 raw19014; decide +kernel
      have hl : raw19014step0Labels = raw19014Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19014 raw19014Labels permutation165 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19015 raw19015Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw19015 raw19015Labels = mixedMoment B raw19015step0 raw19015step0Labels := by
      have hz : ∀ j, raw19015 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19015step0 = (fun i j => raw19015 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19015step0 raw19015; decide +kernel
      have hl : raw19015step0Labels = raw19015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19015 raw19015Labels permutation590 hz
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw19016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19016 raw19016Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw19016 raw19016Labels = mixedMoment B raw19016step0 raw19016step0Labels := by
      have hz : ∀ j, raw19016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19016step0 = (fun i j => raw19016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19016step0 raw19016; decide +kernel
      have hl : raw19016step0Labels = raw19016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19016 raw19016Labels permutation346 hz
    mixedMoment B raw19016step0 raw19016step0Labels = mixedMoment B raw19016step1 raw19016step1Labels := by
      have ha : raw19016step1 = (fun i j => raw19016step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19016step1 raw19016step0; decide +kernel
      have hl : raw19016step1Labels = raw19016step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19016step0 raw19016step0Labels permutation35 permutation3
    mixedMoment B raw19016step1 raw19016step1Labels = mixedMoment B raw19016step2 raw19016step2Labels := by
      have ha : raw19016step2 = raw19016step1 := by apply Matrix.ext; unfold raw19016step2 raw19016step1; decide +kernel
      have hl : raw19016step1Labels = labelEmbedding6 ∘ raw19016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19016step1 raw19016step1Labels raw19016step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw19017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19017 raw19017Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw19017 raw19017Labels = mixedMoment B raw19017step0 raw19017step0Labels := by
      have hz : ∀ j, raw19017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19017step0 = (fun i j => raw19017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19017step0 raw19017; decide +kernel
      have hl : raw19017step0Labels = raw19017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19017 raw19017Labels permutation346 hz
    mixedMoment B raw19017step0 raw19017step0Labels = mixedMoment B raw19017step1 raw19017step1Labels := by
      have ha : raw19017step1 = (fun i j => raw19017step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19017step1 raw19017step0; decide +kernel
      have hl : raw19017step1Labels = raw19017step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19017step0 raw19017step0Labels permutation37 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw19018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19018 raw19018Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw19018 raw19018Labels = mixedMoment B raw19018step0 raw19018step0Labels := by
      have ha : raw19018step0 = (fun i j => raw19018 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19018step0 raw19018; decide +kernel
      have hl : raw19018step0Labels = raw19018Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19018 raw19018Labels permutation157 permutation2
    _ = mixedMoment B node5476 node5476Labels := by rfl

def raw19019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19019 raw19019Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw19019 raw19019Labels = mixedMoment B raw19019step0 raw19019step0Labels := by
      have hz : ∀ j, raw19019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19019step0 = (fun i j => raw19019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19019step0 raw19019; decide +kernel
      have hl : raw19019step0Labels = raw19019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19019 raw19019Labels permutation346 hz
    mixedMoment B raw19019step0 raw19019step0Labels = mixedMoment B raw19019step1 raw19019step1Labels := by
      have ha : raw19019step1 = (fun i j => raw19019step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19019step1 raw19019step0; decide +kernel
      have hl : raw19019step1Labels = raw19019step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19019step0 raw19019step0Labels permutation35 permutation2
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw19020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw19020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw19020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19020step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19020 raw19020Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw19020 raw19020Labels = mixedMoment B raw19020step0 raw19020step0Labels := by
      have hz : ∀ j, raw19020 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19020step0 = (fun i j => raw19020 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19020step0 raw19020; decide +kernel
      have hl : raw19020step0Labels = raw19020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19020 raw19020Labels permutation590 hz
    mixedMoment B raw19020step0 raw19020step0Labels = mixedMoment B raw19020step1 raw19020step1Labels := by
      have hz : ∀ j, raw19020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19020step1 = (fun i j => raw19020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19020step1 raw19020step0; decide +kernel
      have hl : raw19020step1Labels = raw19020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19020step0 raw19020step0Labels permutation80 hz
    mixedMoment B raw19020step1 raw19020step1Labels = mixedMoment B raw19020step2 raw19020step2Labels := by
      have ha : raw19020step2 = (fun i j => raw19020step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19020step2 raw19020step1; decide +kernel
      have hl : raw19020step2Labels = raw19020step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19020step1 raw19020step1Labels permutation9 permutation2
    _ = mixedMoment B node5487 node5487Labels := by rfl

def raw19021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19021step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19021step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19021step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19021 raw19021Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw19021 raw19021Labels = mixedMoment B raw19021step0 raw19021step0Labels := by
      have hz : ∀ j, raw19021 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19021step0 = (fun i j => raw19021 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19021step0 raw19021; decide +kernel
      have hl : raw19021step0Labels = raw19021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19021 raw19021Labels permutation346 hz
    mixedMoment B raw19021step0 raw19021step0Labels = mixedMoment B raw19021step1 raw19021step1Labels := by
      have ha : raw19021step1 = (fun i j => raw19021step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19021step1 raw19021step0; decide +kernel
      have hl : raw19021step1Labels = raw19021step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19021step0 raw19021step0Labels permutation33 permutation3
    mixedMoment B raw19021step1 raw19021step1Labels = mixedMoment B raw19021step2 raw19021step2Labels := by
      have ha : raw19021step2 = raw19021step1 := by apply Matrix.ext; unfold raw19021step2 raw19021step1; decide +kernel
      have hl : raw19021step1Labels = labelEmbedding6 ∘ raw19021step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19021step1 raw19021step1Labels raw19021step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw19022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19022step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19022 raw19022Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw19022 raw19022Labels = mixedMoment B raw19022step0 raw19022step0Labels := by
      have hz : ∀ j, raw19022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19022step0 = (fun i j => raw19022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19022step0 raw19022; decide +kernel
      have hl : raw19022step0Labels = raw19022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19022 raw19022Labels permutation346 hz
    mixedMoment B raw19022step0 raw19022step0Labels = mixedMoment B raw19022step1 raw19022step1Labels := by
      have ha : raw19022step1 = (fun i j => raw19022step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19022step1 raw19022step0; decide +kernel
      have hl : raw19022step1Labels = raw19022step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19022step0 raw19022step0Labels permutation36 permutation2
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw19023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19023 raw19023Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw19023 raw19023Labels = mixedMoment B raw19023step0 raw19023step0Labels := by
      have ha : raw19023step0 = (fun i j => raw19023 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19023step0 raw19023; decide +kernel
      have hl : raw19023step0Labels = raw19023Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19023 raw19023Labels permutation156 permutation2
    _ = mixedMoment B node5476 node5476Labels := by rfl

def raw19024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19024 raw19024Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw19024 raw19024Labels = mixedMoment B raw19024step0 raw19024step0Labels := by
      have hz : ∀ j, raw19024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19024step0 = (fun i j => raw19024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19024step0 raw19024; decide +kernel
      have hl : raw19024step0Labels = raw19024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19024 raw19024Labels permutation346 hz
    mixedMoment B raw19024step0 raw19024step0Labels = mixedMoment B raw19024step1 raw19024step1Labels := by
      have ha : raw19024step1 = (fun i j => raw19024step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19024step1 raw19024step0; decide +kernel
      have hl : raw19024step1Labels = raw19024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19024step0 raw19024step0Labels permutation33 permutation2
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw19025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19025 raw19025Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw19025 raw19025Labels = mixedMoment B raw19025step0 raw19025step0Labels := by
      have hz : ∀ j, raw19025 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19025step0 = (fun i j => raw19025 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19025step0 raw19025; decide +kernel
      have hl : raw19025step0Labels = raw19025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19025 raw19025Labels permutation590 hz
    mixedMoment B raw19025step0 raw19025step0Labels = mixedMoment B raw19025step1 raw19025step1Labels := by
      have hz : ∀ j, raw19025step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19025step1 = (fun i j => raw19025step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19025step1 raw19025step0; decide +kernel
      have hl : raw19025step1Labels = raw19025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19025step0 raw19025step0Labels permutation80 hz
    _ = mixedMoment B node5487 node5487Labels := by rfl

def raw19026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw19026step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw19026step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19026step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw19026step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19026 raw19026Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw19026 raw19026Labels = mixedMoment B raw19026step0 raw19026step0Labels := by
      have hz : ∀ j, raw19026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19026step0 = (fun i j => raw19026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19026step0 raw19026; decide +kernel
      have hl : raw19026step0Labels = raw19026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19026 raw19026Labels permutation346 hz
    mixedMoment B raw19026step0 raw19026step0Labels = mixedMoment B raw19026step1 raw19026step1Labels := by
      have ha : raw19026step1 = (fun i j => raw19026step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19026step1 raw19026step0; decide +kernel
      have hl : raw19026step1Labels = raw19026step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19026step0 raw19026step0Labels permutation144 permutation3
    mixedMoment B raw19026step1 raw19026step1Labels = mixedMoment B raw19026step2 raw19026step2Labels := by
      have ha : raw19026step2 = -raw19026step1 := by apply Matrix.ext; change ∀ i j, raw19026step2 i j = -(raw19026step1 i j); unfold raw19026step2 raw19026step1; decide +kernel
      have hl : raw19026step2Labels = raw19026step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19026step2 raw19026step2Labels = mixedMoment B raw19026step3 raw19026step3Labels := by
      have ha : raw19026step3 = raw19026step2 := by apply Matrix.ext; unfold raw19026step3 raw19026step2; decide +kernel
      have hl : raw19026step2Labels = labelEmbedding6 ∘ raw19026step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19026step2 raw19026step2Labels raw19026step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw19027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw19027step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19027step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19027step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19027 raw19027Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw19027 raw19027Labels = mixedMoment B raw19027step0 raw19027step0Labels := by
      have ha : raw19027step0 = (fun i j => raw19027 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19027step0 raw19027; decide +kernel
      have hl : raw19027step0Labels = raw19027Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19027 raw19027Labels permutation662 permutation3
    mixedMoment B raw19027step0 raw19027step0Labels = mixedMoment B raw19027step1 raw19027step1Labels := by
      have ha : raw19027step1 = -raw19027step0 := by apply Matrix.ext; change ∀ i j, raw19027step1 i j = -(raw19027step0 i j); unfold raw19027step1 raw19027step0; decide +kernel
      have hl : raw19027step1Labels = raw19027step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19027step1 raw19027step1Labels = mixedMoment B raw19027step2 raw19027step2Labels := by
      have ha : raw19027step2 = raw19027step1 := by apply Matrix.ext; unfold raw19027step2 raw19027step1; decide +kernel
      have hl : raw19027step1Labels = labelEmbedding6 ∘ raw19027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19027step1 raw19027step1Labels raw19027step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw19028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw19028step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19028step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19028step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19028step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19028 raw19028Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw19028 raw19028Labels = mixedMoment B raw19028step0 raw19028step0Labels := by
      have hz : ∀ j, raw19028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19028step0 = (fun i j => raw19028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19028step0 raw19028; decide +kernel
      have hl : raw19028step0Labels = raw19028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19028 raw19028Labels permutation346 hz
    mixedMoment B raw19028step0 raw19028step0Labels = mixedMoment B raw19028step1 raw19028step1Labels := by
      have ha : raw19028step1 = (fun i j => raw19028step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19028step1 raw19028step0; decide +kernel
      have hl : raw19028step1Labels = raw19028step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19028step0 raw19028step0Labels permutation145 permutation3
    mixedMoment B raw19028step1 raw19028step1Labels = mixedMoment B raw19028step2 raw19028step2Labels := by
      have ha : raw19028step2 = -raw19028step1 := by apply Matrix.ext; change ∀ i j, raw19028step2 i j = -(raw19028step1 i j); unfold raw19028step2 raw19028step1; decide +kernel
      have hl : raw19028step2Labels = raw19028step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19028step2 raw19028step2Labels = mixedMoment B raw19028step3 raw19028step3Labels := by
      have ha : raw19028step3 = raw19028step2 := by apply Matrix.ext; unfold raw19028step3 raw19028step2; decide +kernel
      have hl : raw19028step2Labels = labelEmbedding6 ∘ raw19028step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19028step2 raw19028step2Labels raw19028step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw19029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19029step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19029step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19029step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19029 raw19029Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw19029 raw19029Labels = mixedMoment B raw19029step0 raw19029step0Labels := by
      have ha : raw19029step0 = (fun i j => raw19029 (permutation294 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19029step0 raw19029; decide +kernel
      have hl : raw19029step0Labels = raw19029Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19029 raw19029Labels permutation294 permutation5
    mixedMoment B raw19029step0 raw19029step0Labels = mixedMoment B raw19029step1 raw19029step1Labels := by
      have ha : raw19029step1 = -raw19029step0 := by apply Matrix.ext; change ∀ i j, raw19029step1 i j = -(raw19029step0 i j); unfold raw19029step1 raw19029step0; decide +kernel
      have hl : raw19029step1Labels = raw19029step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19029step1 raw19029step1Labels = mixedMoment B raw19029step2 raw19029step2Labels := by
      have ha : raw19029step2 = raw19029step1 := by apply Matrix.ext; unfold raw19029step2 raw19029step1; decide +kernel
      have hl : raw19029step1Labels = labelEmbedding8 ∘ raw19029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19029step1 raw19029step1Labels raw19029step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw19030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19030step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19030 raw19030Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw19030 raw19030Labels = mixedMoment B raw19030step0 raw19030step0Labels := by
      have ha : raw19030step0 = (fun i j => raw19030 (permutation499 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19030step0 raw19030; decide +kernel
      have hl : raw19030step0Labels = raw19030Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19030 raw19030Labels permutation499 permutation5
    mixedMoment B raw19030step0 raw19030step0Labels = mixedMoment B raw19030step1 raw19030step1Labels := by
      have ha : raw19030step1 = raw19030step0 := by apply Matrix.ext; unfold raw19030step1 raw19030step0; decide +kernel
      have hl : raw19030step0Labels = labelEmbedding8 ∘ raw19030step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19030step0 raw19030step0Labels raw19030step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw19031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19031step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19031 raw19031Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw19031 raw19031Labels = mixedMoment B raw19031step0 raw19031step0Labels := by
      have ha : raw19031step0 = (fun i j => raw19031 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19031step0 raw19031; decide +kernel
      have hl : raw19031step0Labels = raw19031Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19031 raw19031Labels permutation158 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

def raw19032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw19032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw19032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19032step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19032 raw19032Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19032 raw19032Labels = mixedMoment B raw19032step0 raw19032step0Labels := by
      have hz : ∀ j, raw19032 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19032step0 = (fun i j => raw19032 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19032step0 raw19032; decide +kernel
      have hl : raw19032step0Labels = raw19032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19032 raw19032Labels permutation520 hz
    mixedMoment B raw19032step0 raw19032step0Labels = mixedMoment B raw19032step1 raw19032step1Labels := by
      have ha : raw19032step1 = (fun i j => raw19032step0 (permutation108 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19032step1 raw19032step0; decide +kernel
      have hl : raw19032step1Labels = raw19032step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19032step0 raw19032step0Labels permutation108 permutation4
    mixedMoment B raw19032step1 raw19032step1Labels = mixedMoment B raw19032step2 raw19032step2Labels := by
      have ha : raw19032step2 = raw19032step1 := by apply Matrix.ext; unfold raw19032step2 raw19032step1; decide +kernel
      have hl : raw19032step1Labels = labelEmbedding7 ∘ raw19032step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19032step1 raw19032step1Labels raw19032step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw19033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw19033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19033step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19033 raw19033Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19033 raw19033Labels = mixedMoment B raw19033step0 raw19033step0Labels := by
      have ha : raw19033step0 = (fun i j => raw19033 (permutation486 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19033step0 raw19033; decide +kernel
      have hl : raw19033step0Labels = raw19033Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19033 raw19033Labels permutation486 permutation5
    mixedMoment B raw19033step0 raw19033step0Labels = mixedMoment B raw19033step1 raw19033step1Labels := by
      have ha : raw19033step1 = raw19033step0 := by apply Matrix.ext; unfold raw19033step1 raw19033step0; decide +kernel
      have hl : raw19033step0Labels = labelEmbedding8 ∘ raw19033step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19033step0 raw19033step0Labels raw19033step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19034step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19034step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19034step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19034 raw19034Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw19034 raw19034Labels = mixedMoment B raw19034step0 raw19034step0Labels := by
      have hz : ∀ j, raw19034 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw19034step0 = (fun i j => raw19034 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw19034step0 raw19034; decide +kernel
      have hl : raw19034step0Labels = raw19034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19034 raw19034Labels permutation265 hz
    mixedMoment B raw19034step0 raw19034step0Labels = mixedMoment B raw19034step1 raw19034step1Labels := by
      have ha : raw19034step1 = (fun i j => raw19034step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19034step1 raw19034step0; decide +kernel
      have hl : raw19034step1Labels = raw19034step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19034step0 raw19034step0Labels permutation37 permutation3
    mixedMoment B raw19034step1 raw19034step1Labels = mixedMoment B raw19034step2 raw19034step2Labels := by
      have ha : raw19034step2 = raw19034step1 := by apply Matrix.ext; unfold raw19034step2 raw19034step1; decide +kernel
      have hl : raw19034step1Labels = labelEmbedding6 ∘ raw19034step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19034step1 raw19034step1Labels raw19034step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw19035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19035step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19035 raw19035Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw19035 raw19035Labels = mixedMoment B raw19035step0 raw19035step0Labels := by
      have ha : raw19035step0 = (fun i j => raw19035 (permutation270 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19035step0 raw19035; decide +kernel
      have hl : raw19035step0Labels = raw19035Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19035 raw19035Labels permutation270 permutation3
    mixedMoment B raw19035step0 raw19035step0Labels = mixedMoment B raw19035step1 raw19035step1Labels := by
      have ha : raw19035step1 = raw19035step0 := by apply Matrix.ext; unfold raw19035step1 raw19035step0; decide +kernel
      have hl : raw19035step0Labels = labelEmbedding6 ∘ raw19035step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19035step0 raw19035step0Labels raw19035step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw19036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19036step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19036step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19036 raw19036Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19036 raw19036Labels = mixedMoment B raw19036step0 raw19036step0Labels := by
      have ha : raw19036step0 = (fun i j => raw19036 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19036step0 raw19036; decide +kernel
      have hl : raw19036step0Labels = raw19036Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19036 raw19036Labels permutation159 permutation3
    mixedMoment B raw19036step0 raw19036step0Labels = mixedMoment B raw19036step1 raw19036step1Labels := by
      have ha : raw19036step1 = raw19036step0 := by apply Matrix.ext; unfold raw19036step1 raw19036step0; decide +kernel
      have hl : raw19036step0Labels = labelEmbedding6 ∘ raw19036step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19036step0 raw19036step0Labels raw19036step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw19037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw19037step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19037step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19037 raw19037Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw19037 raw19037Labels = mixedMoment B raw19037step0 raw19037step0Labels := by
      have hz : ∀ j, raw19037 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19037step0 = (fun i j => raw19037 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19037step0 raw19037; decide +kernel
      have hl : raw19037step0Labels = raw19037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19037 raw19037Labels permutation520 hz
    mixedMoment B raw19037step0 raw19037step0Labels = mixedMoment B raw19037step1 raw19037step1Labels := by
      have ha : raw19037step1 = (fun i j => raw19037step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19037step1 raw19037step0; decide +kernel
      have hl : raw19037step1Labels = raw19037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19037step0 raw19037step0Labels permutation33 permutation3
    mixedMoment B raw19037step1 raw19037step1Labels = mixedMoment B raw19037step2 raw19037step2Labels := by
      have ha : raw19037step2 = raw19037step1 := by apply Matrix.ext; unfold raw19037step2 raw19037step1; decide +kernel
      have hl : raw19037step1Labels = labelEmbedding6 ∘ raw19037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19037step1 raw19037step1Labels raw19037step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw19038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw19038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19038step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19038 raw19038Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19038 raw19038Labels = mixedMoment B raw19038step0 raw19038step0Labels := by
      have ha : raw19038step0 = (fun i j => raw19038 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19038step0 raw19038; decide +kernel
      have hl : raw19038step0Labels = raw19038Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19038 raw19038Labels permutation171 permutation3
    mixedMoment B raw19038step0 raw19038step0Labels = mixedMoment B raw19038step1 raw19038step1Labels := by
      have ha : raw19038step1 = raw19038step0 := by apply Matrix.ext; unfold raw19038step1 raw19038step0; decide +kernel
      have hl : raw19038step0Labels = labelEmbedding6 ∘ raw19038step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19038step0 raw19038step0Labels raw19038step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw19039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw19039step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw19039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19039 raw19039Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw19039 raw19039Labels = mixedMoment B raw19039step0 raw19039step0Labels := by
      have ha : raw19039step0 = (fun i j => raw19039 (permutation503 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19039step0 raw19039; decide +kernel
      have hl : raw19039step0Labels = raw19039Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19039 raw19039Labels permutation503 permutation5
    mixedMoment B raw19039step0 raw19039step0Labels = mixedMoment B raw19039step1 raw19039step1Labels := by
      have ha : raw19039step1 = raw19039step0 := by apply Matrix.ext; unfold raw19039step1 raw19039step0; decide +kernel
      have hl : raw19039step0Labels = labelEmbedding8 ∘ raw19039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19039step0 raw19039step0Labels raw19039step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw19040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19040step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19040step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19040 raw19040Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw19040 raw19040Labels = mixedMoment B raw19040step0 raw19040step0Labels := by
      have ha : raw19040step0 = (fun i j => raw19040 (permutation501 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19040step0 raw19040; decide +kernel
      have hl : raw19040step0Labels = raw19040Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19040 raw19040Labels permutation501 permutation5
    mixedMoment B raw19040step0 raw19040step0Labels = mixedMoment B raw19040step1 raw19040step1Labels := by
      have ha : raw19040step1 = raw19040step0 := by apply Matrix.ext; unfold raw19040step1 raw19040step0; decide +kernel
      have hl : raw19040step0Labels = labelEmbedding8 ∘ raw19040step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19040step0 raw19040step0Labels raw19040step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw19041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw19041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw19041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19041step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19041step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19041 raw19041Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw19041 raw19041Labels = mixedMoment B raw19041step0 raw19041step0Labels := by
      have hz : ∀ j, raw19041 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19041step0 = (fun i j => raw19041 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19041step0 raw19041; decide +kernel
      have hl : raw19041step0Labels = raw19041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19041 raw19041Labels permutation520 hz
    mixedMoment B raw19041step0 raw19041step0Labels = mixedMoment B raw19041step1 raw19041step1Labels := by
      have ha : raw19041step1 = (fun i j => raw19041step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19041step1 raw19041step0; decide +kernel
      have hl : raw19041step1Labels = raw19041step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19041step0 raw19041step0Labels permutation127 permutation5
    mixedMoment B raw19041step1 raw19041step1Labels = mixedMoment B raw19041step2 raw19041step2Labels := by
      have ha : raw19041step2 = raw19041step1 := by apply Matrix.ext; unfold raw19041step2 raw19041step1; decide +kernel
      have hl : raw19041step1Labels = labelEmbedding8 ∘ raw19041step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19041step1 raw19041step1Labels raw19041step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw19042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw19042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19042step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19042step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19042 raw19042Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw19042 raw19042Labels = mixedMoment B raw19042step0 raw19042step0Labels := by
      have ha : raw19042step0 = (fun i j => raw19042 (permutation498 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19042step0 raw19042; decide +kernel
      have hl : raw19042step0Labels = raw19042Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19042 raw19042Labels permutation498 permutation5
    mixedMoment B raw19042step0 raw19042step0Labels = mixedMoment B raw19042step1 raw19042step1Labels := by
      have ha : raw19042step1 = raw19042step0 := by apply Matrix.ext; unfold raw19042step1 raw19042step0; decide +kernel
      have hl : raw19042step0Labels = labelEmbedding8 ∘ raw19042step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19042step0 raw19042step0Labels raw19042step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw19043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw19043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw19043step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw19043step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19043 raw19043Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw19043 raw19043Labels = mixedMoment B raw19043step0 raw19043step0Labels := by
      have ha : raw19043step0 = (fun i j => raw19043 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19043step0 raw19043; decide +kernel
      have hl : raw19043step0Labels = raw19043Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19043 raw19043Labels permutation269 permutation3
    mixedMoment B raw19043step0 raw19043step0Labels = mixedMoment B raw19043step1 raw19043step1Labels := by
      have ha : raw19043step1 = raw19043step0 := by apply Matrix.ext; unfold raw19043step1 raw19043step0; decide +kernel
      have hl : raw19043step0Labels = labelEmbedding6 ∘ raw19043step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19043step0 raw19043step0Labels raw19043step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw19044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw19044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19044step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19044 raw19044Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw19044 raw19044Labels = mixedMoment B raw19044step0 raw19044step0Labels := by
      have ha : raw19044step0 = (fun i j => raw19044 (permutation565 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19044step0 raw19044; decide +kernel
      have hl : raw19044step0Labels = raw19044Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19044 raw19044Labels permutation565 permutation5
    mixedMoment B raw19044step0 raw19044step0Labels = mixedMoment B raw19044step1 raw19044step1Labels := by
      have ha : raw19044step1 = raw19044step0 := by apply Matrix.ext; unfold raw19044step1 raw19044step0; decide +kernel
      have hl : raw19044step0Labels = labelEmbedding8 ∘ raw19044step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19044step0 raw19044step0Labels raw19044step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw19045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw19045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19045step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19045step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19045step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19045step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19045 raw19045Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw19045 raw19045Labels = mixedMoment B raw19045step0 raw19045step0Labels := by
      have ha : raw19045step0 = (fun i j => raw19045 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19045step0 raw19045; decide +kernel
      have hl : raw19045step0Labels = raw19045Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19045 raw19045Labels permutation589 permutation3
    mixedMoment B raw19045step0 raw19045step0Labels = mixedMoment B raw19045step1 raw19045step1Labels := by
      have ha : raw19045step1 = -raw19045step0 := by apply Matrix.ext; change ∀ i j, raw19045step1 i j = -(raw19045step0 i j); unfold raw19045step1 raw19045step0; decide +kernel
      have hl : raw19045step1Labels = raw19045step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19045step1 raw19045step1Labels = mixedMoment B raw19045step2 raw19045step2Labels := by
      have ha : raw19045step2 = raw19045step1 := by apply Matrix.ext; unfold raw19045step2 raw19045step1; decide +kernel
      have hl : raw19045step1Labels = labelEmbedding6 ∘ raw19045step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19045step1 raw19045step1Labels raw19045step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw19046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw19046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19046step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19046step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19046 raw19046Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw19046 raw19046Labels = mixedMoment B raw19046step0 raw19046step0Labels := by
      have ha : raw19046step0 = (fun i j => raw19046 (permutation562 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19046step0 raw19046; decide +kernel
      have hl : raw19046step0Labels = raw19046Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19046 raw19046Labels permutation562 permutation5
    mixedMoment B raw19046step0 raw19046step0Labels = mixedMoment B raw19046step1 raw19046step1Labels := by
      have ha : raw19046step1 = raw19046step0 := by apply Matrix.ext; unfold raw19046step1 raw19046step0; decide +kernel
      have hl : raw19046step0Labels = labelEmbedding8 ∘ raw19046step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19046step0 raw19046step0Labels raw19046step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw19047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw19047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19047step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19047step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19047 raw19047Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw19047 raw19047Labels = mixedMoment B raw19047step0 raw19047step0Labels := by
      have ha : raw19047step0 = (fun i j => raw19047 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19047step0 raw19047; decide +kernel
      have hl : raw19047step0Labels = raw19047Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19047 raw19047Labels permutation267 permutation3
    mixedMoment B raw19047step0 raw19047step0Labels = mixedMoment B raw19047step1 raw19047step1Labels := by
      have ha : raw19047step1 = raw19047step0 := by apply Matrix.ext; unfold raw19047step1 raw19047step0; decide +kernel
      have hl : raw19047step0Labels = labelEmbedding6 ∘ raw19047step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19047step0 raw19047step0Labels raw19047step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw19048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw19048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19048step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw19048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19048 raw19048Labels = mixedMoment B node5467 node5467Labels := by
  calc
    mixedMoment B raw19048 raw19048Labels = mixedMoment B raw19048step0 raw19048step0Labels := by
      have ha : raw19048step0 = (fun i j => raw19048 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19048step0 raw19048; decide +kernel
      have hl : raw19048step0Labels = raw19048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19048 raw19048Labels permutation178 permutation3
    mixedMoment B raw19048step0 raw19048step0Labels = mixedMoment B raw19048step1 raw19048step1Labels := by
      have ha : raw19048step1 = raw19048step0 := by apply Matrix.ext; unfold raw19048step1 raw19048step0; decide +kernel
      have hl : raw19048step0Labels = labelEmbedding6 ∘ raw19048step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19048step0 raw19048step0Labels raw19048step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5467 node5467Labels := by rfl

def raw19049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw19049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19049step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19049 raw19049Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw19049 raw19049Labels = mixedMoment B raw19049step0 raw19049step0Labels := by
      have ha : raw19049step0 = (fun i j => raw19049 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19049step0 raw19049; decide +kernel
      have hl : raw19049step0Labels = raw19049Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19049 raw19049Labels permutation152 permutation3
    mixedMoment B raw19049step0 raw19049step0Labels = mixedMoment B raw19049step1 raw19049step1Labels := by
      have ha : raw19049step1 = raw19049step0 := by apply Matrix.ext; unfold raw19049step1 raw19049step0; decide +kernel
      have hl : raw19049step0Labels = labelEmbedding6 ∘ raw19049step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19049step0 raw19049step0Labels raw19049step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw19050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw19050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19050step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19050step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19050step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19050step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19050 raw19050Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw19050 raw19050Labels = mixedMoment B raw19050step0 raw19050step0Labels := by
      have hz : ∀ j, raw19050 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19050step0 = (fun i j => raw19050 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19050step0 raw19050; decide +kernel
      have hl : raw19050step0Labels = raw19050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19050 raw19050Labels permutation520 hz
    mixedMoment B raw19050step0 raw19050step0Labels = mixedMoment B raw19050step1 raw19050step1Labels := by
      have ha : raw19050step1 = (fun i j => raw19050step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19050step1 raw19050step0; decide +kernel
      have hl : raw19050step1Labels = raw19050step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19050step0 raw19050step0Labels permutation151 permutation3
    mixedMoment B raw19050step1 raw19050step1Labels = mixedMoment B raw19050step2 raw19050step2Labels := by
      have ha : raw19050step2 = -raw19050step1 := by apply Matrix.ext; change ∀ i j, raw19050step2 i j = -(raw19050step1 i j); unfold raw19050step2 raw19050step1; decide +kernel
      have hl : raw19050step2Labels = raw19050step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19050step2 raw19050step2Labels = mixedMoment B raw19050step3 raw19050step3Labels := by
      have ha : raw19050step3 = raw19050step2 := by apply Matrix.ext; unfold raw19050step3 raw19050step2; decide +kernel
      have hl : raw19050step2Labels = labelEmbedding6 ∘ raw19050step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19050step2 raw19050step2Labels raw19050step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw19051 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19051step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19051step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19051 raw19051Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw19051 raw19051Labels = mixedMoment B raw19051step0 raw19051step0Labels := by
      have ha : raw19051step0 = (fun i j => raw19051 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19051step0 raw19051; decide +kernel
      have hl : raw19051step0Labels = raw19051Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19051 raw19051Labels permutation152 permutation7
    mixedMoment B raw19051step0 raw19051step0Labels = mixedMoment B raw19051step1 raw19051step1Labels := by
      have ha : raw19051step1 = raw19051step0 := by apply Matrix.ext; unfold raw19051step1 raw19051step0; decide +kernel
      have hl : raw19051step0Labels = labelEmbedding10 ∘ raw19051step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19051step0 raw19051step0Labels raw19051step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw19052 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw19052step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19052step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19052 raw19052Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw19052 raw19052Labels = mixedMoment B raw19052step0 raw19052step0Labels := by
      have ha : raw19052step0 = (fun i j => raw19052 (permutation367 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19052step0 raw19052; decide +kernel
      have hl : raw19052step0Labels = raw19052Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19052 raw19052Labels permutation367 permutation5
    mixedMoment B raw19052step0 raw19052step0Labels = mixedMoment B raw19052step1 raw19052step1Labels := by
      have ha : raw19052step1 = -raw19052step0 := by apply Matrix.ext; change ∀ i j, raw19052step1 i j = -(raw19052step0 i j); unfold raw19052step1 raw19052step0; decide +kernel
      have hl : raw19052step1Labels = raw19052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19052step1 raw19052step1Labels = mixedMoment B raw19052step2 raw19052step2Labels := by
      have ha : raw19052step2 = raw19052step1 := by apply Matrix.ext; unfold raw19052step2 raw19052step1; decide +kernel
      have hl : raw19052step1Labels = labelEmbedding8 ∘ raw19052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19052step1 raw19052step1Labels raw19052step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw19053 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19053step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19053 raw19053Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw19053 raw19053Labels = mixedMoment B raw19053step0 raw19053step0Labels := by
      have ha : raw19053step0 = (fun i j => raw19053 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19053step0 raw19053; decide +kernel
      have hl : raw19053step0Labels = raw19053Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19053 raw19053Labels permutation155 permutation7
    mixedMoment B raw19053step0 raw19053step0Labels = mixedMoment B raw19053step1 raw19053step1Labels := by
      have ha : raw19053step1 = raw19053step0 := by apply Matrix.ext; unfold raw19053step1 raw19053step0; decide +kernel
      have hl : raw19053step0Labels = labelEmbedding10 ∘ raw19053step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19053step0 raw19053step0Labels raw19053step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw19054 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw19054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19054step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19054 raw19054Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw19054 raw19054Labels = mixedMoment B raw19054step0 raw19054step0Labels := by
      have ha : raw19054step0 = (fun i j => raw19054 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19054step0 raw19054; decide +kernel
      have hl : raw19054step0Labels = raw19054Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19054 raw19054Labels permutation153 permutation7
    mixedMoment B raw19054step0 raw19054step0Labels = mixedMoment B raw19054step1 raw19054step1Labels := by
      have ha : raw19054step1 = raw19054step0 := by apply Matrix.ext; unfold raw19054step1 raw19054step0; decide +kernel
      have hl : raw19054step0Labels = labelEmbedding10 ∘ raw19054step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19054step0 raw19054step0Labels raw19054step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw19055 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19055step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19055 raw19055Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw19055 raw19055Labels = mixedMoment B raw19055step0 raw19055step0Labels := by
      have ha : raw19055step0 = (fun i j => raw19055 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19055step0 raw19055; decide +kernel
      have hl : raw19055step0Labels = raw19055Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19055 raw19055Labels permutation152 permutation7
    mixedMoment B raw19055step0 raw19055step0Labels = mixedMoment B raw19055step1 raw19055step1Labels := by
      have ha : raw19055step1 = raw19055step0 := by apply Matrix.ext; unfold raw19055step1 raw19055step0; decide +kernel
      have hl : raw19055step0Labels = labelEmbedding10 ∘ raw19055step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19055step0 raw19055step0Labels raw19055step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw19056 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19056step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19056step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19056step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19056step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19056 raw19056Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw19056 raw19056Labels = mixedMoment B raw19056step0 raw19056step0Labels := by
      have ha : raw19056step0 = (fun i j => raw19056 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19056step0 raw19056; decide +kernel
      have hl : raw19056step0Labels = raw19056Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19056 raw19056Labels permutation176 permutation4
    mixedMoment B raw19056step0 raw19056step0Labels = mixedMoment B raw19056step1 raw19056step1Labels := by
      have ha : raw19056step1 = -raw19056step0 := by apply Matrix.ext; change ∀ i j, raw19056step1 i j = -(raw19056step0 i j); unfold raw19056step1 raw19056step0; decide +kernel
      have hl : raw19056step1Labels = raw19056step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19056step1 raw19056step1Labels = mixedMoment B raw19056step2 raw19056step2Labels := by
      have ha : raw19056step2 = raw19056step1 := by apply Matrix.ext; unfold raw19056step2 raw19056step1; decide +kernel
      have hl : raw19056step1Labels = labelEmbedding7 ∘ raw19056step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19056step1 raw19056step1Labels raw19056step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5427 node5427Labels := by rfl

def raw19057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw19057step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19057step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19057step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw19057step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19057 raw19057Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw19057 raw19057Labels = mixedMoment B raw19057step0 raw19057step0Labels := by
      have ha : raw19057step0 = (fun i j => raw19057 (permutation346 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19057step0 raw19057; decide +kernel
      have hl : raw19057step0Labels = raw19057Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19057 raw19057Labels permutation346 permutation5
    mixedMoment B raw19057step0 raw19057step0Labels = mixedMoment B raw19057step1 raw19057step1Labels := by
      have ha : raw19057step1 = -raw19057step0 := by apply Matrix.ext; change ∀ i j, raw19057step1 i j = -(raw19057step0 i j); unfold raw19057step1 raw19057step0; decide +kernel
      have hl : raw19057step1Labels = raw19057step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19057step1 raw19057step1Labels = mixedMoment B raw19057step2 raw19057step2Labels := by
      have ha : raw19057step2 = raw19057step1 := by apply Matrix.ext; unfold raw19057step2 raw19057step1; decide +kernel
      have hl : raw19057step1Labels = labelEmbedding8 ∘ raw19057step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19057step1 raw19057step1Labels raw19057step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw19058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19058step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19058 raw19058Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19058 raw19058Labels = mixedMoment B raw19058step0 raw19058step0Labels := by
      have ha : raw19058step0 = (fun i j => raw19058 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19058step0 raw19058; decide +kernel
      have hl : raw19058step0Labels = raw19058Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19058 raw19058Labels permutation155 permutation7
    mixedMoment B raw19058step0 raw19058step0Labels = mixedMoment B raw19058step1 raw19058step1Labels := by
      have ha : raw19058step1 = raw19058step0 := by apply Matrix.ext; unfold raw19058step1 raw19058step0; decide +kernel
      have hl : raw19058step0Labels = labelEmbedding10 ∘ raw19058step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19058step0 raw19058step0Labels raw19058step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw19059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19059step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19059 raw19059Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19059 raw19059Labels = mixedMoment B raw19059step0 raw19059step0Labels := by
      have ha : raw19059step0 = (fun i j => raw19059 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19059step0 raw19059; decide +kernel
      have hl : raw19059step0Labels = raw19059Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19059 raw19059Labels permutation153 permutation7
    mixedMoment B raw19059step0 raw19059step0Labels = mixedMoment B raw19059step1 raw19059step1Labels := by
      have ha : raw19059step1 = raw19059step0 := by apply Matrix.ext; unfold raw19059step1 raw19059step0; decide +kernel
      have hl : raw19059step0Labels = labelEmbedding10 ∘ raw19059step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19059step0 raw19059step0Labels raw19059step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19060step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19060step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19060 raw19060Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw19060 raw19060Labels = mixedMoment B raw19060step0 raw19060step0Labels := by
      have ha : raw19060step0 = (fun i j => raw19060 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19060step0 raw19060; decide +kernel
      have hl : raw19060step0Labels = raw19060Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19060 raw19060Labels permutation152 permutation7
    mixedMoment B raw19060step0 raw19060step0Labels = mixedMoment B raw19060step1 raw19060step1Labels := by
      have ha : raw19060step1 = raw19060step0 := by apply Matrix.ext; unfold raw19060step1 raw19060step0; decide +kernel
      have hl : raw19060step0Labels = labelEmbedding10 ∘ raw19060step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19060step0 raw19060step0Labels raw19060step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw19061 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19061step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw19061step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw19061step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19061step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw19061step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw19061step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical19061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19061 raw19061Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw19061 raw19061Labels = mixedMoment B raw19061step0 raw19061step0Labels := by
      have hz : ∀ j, raw19061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19061step0 = (fun i j => raw19061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19061step0 raw19061; decide +kernel
      have hl : raw19061step0Labels = raw19061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19061 raw19061Labels permutation346 hz
    mixedMoment B raw19061step0 raw19061step0Labels = mixedMoment B raw19061step1 raw19061step1Labels := by
      have hz : ∀ i, raw19061step0 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw19061step1 = (fun i j => raw19061step0 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw19061step1 raw19061step0; decide +kernel
      have hl : raw19061step1Labels = (fun j => raw19061step0Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw19061step0 raw19061step0Labels permutation2 hz
    mixedMoment B raw19061step1 raw19061step1Labels = mixedMoment B raw19061step2 raw19061step2Labels := by
      have ha : raw19061step2 = -raw19061step1 := by apply Matrix.ext; change ∀ i j, raw19061step2 i j = -(raw19061step1 i j); unfold raw19061step2 raw19061step1; decide +kernel
      have hl : raw19061step2Labels = raw19061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19061step2 raw19061step2Labels = mixedMoment B raw19061step3 raw19061step3Labels := by
      have ha : raw19061step3 = raw19061step2 := by apply Matrix.ext; unfold raw19061step3 raw19061step2; decide +kernel
      have hl : raw19061step2Labels = labelEmbedding3 ∘ raw19061step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19061step2 raw19061step2Labels raw19061step3Labels labelEmbedding3 hl
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw19062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19062step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19062step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19062 raw19062Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw19062 raw19062Labels = mixedMoment B raw19062step0 raw19062step0Labels := by
      have hz : ∀ j, raw19062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19062step0 = (fun i j => raw19062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19062step0 raw19062; decide +kernel
      have hl : raw19062step0Labels = raw19062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19062 raw19062Labels permutation346 hz
    mixedMoment B raw19062step0 raw19062step0Labels = mixedMoment B raw19062step1 raw19062step1Labels := by
      have ha : raw19062step1 = (fun i j => raw19062step0 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19062step1 raw19062step0; decide +kernel
      have hl : raw19062step1Labels = raw19062step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19062step0 raw19062step0Labels permutation56 permutation4
    mixedMoment B raw19062step1 raw19062step1Labels = mixedMoment B raw19062step2 raw19062step2Labels := by
      have ha : raw19062step2 = -raw19062step1 := by apply Matrix.ext; change ∀ i j, raw19062step2 i j = -(raw19062step1 i j); unfold raw19062step2 raw19062step1; decide +kernel
      have hl : raw19062step2Labels = raw19062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19062step2 raw19062step2Labels = mixedMoment B raw19062step3 raw19062step3Labels := by
      have ha : raw19062step3 = raw19062step2 := by apply Matrix.ext; unfold raw19062step3 raw19062step2; decide +kernel
      have hl : raw19062step2Labels = labelEmbedding7 ∘ raw19062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19062step2 raw19062step2Labels raw19062step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5474 node5474Labels := by rfl

def raw19063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19063step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19063 raw19063Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw19063 raw19063Labels = mixedMoment B raw19063step0 raw19063step0Labels := by
      have hz : ∀ j, raw19063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19063step0 = (fun i j => raw19063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19063step0 raw19063; decide +kernel
      have hl : raw19063step0Labels = raw19063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19063 raw19063Labels permutation346 hz
    mixedMoment B raw19063step0 raw19063step0Labels = mixedMoment B raw19063step1 raw19063step1Labels := by
      have ha : raw19063step1 = (fun i j => raw19063step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19063step1 raw19063step0; decide +kernel
      have hl : raw19063step1Labels = raw19063step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19063step0 raw19063step0Labels permutation32 permutation6
    mixedMoment B raw19063step1 raw19063step1Labels = mixedMoment B raw19063step2 raw19063step2Labels := by
      have ha : raw19063step2 = raw19063step1 := by apply Matrix.ext; unfold raw19063step2 raw19063step1; decide +kernel
      have hl : raw19063step1Labels = labelEmbedding9 ∘ raw19063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19063step1 raw19063step1Labels raw19063step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw19064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw19064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw19064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19064step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19064step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19064 raw19064Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw19064 raw19064Labels = mixedMoment B raw19064step0 raw19064step0Labels := by
      have hz : ∀ j, raw19064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19064step0 = (fun i j => raw19064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19064step0 raw19064; decide +kernel
      have hl : raw19064step0Labels = raw19064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19064 raw19064Labels permutation346 hz
    mixedMoment B raw19064step0 raw19064step0Labels = mixedMoment B raw19064step1 raw19064step1Labels := by
      have ha : raw19064step1 = (fun i j => raw19064step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19064step1 raw19064step0; decide +kernel
      have hl : raw19064step1Labels = raw19064step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19064step0 raw19064step0Labels permutation34 permutation6
    mixedMoment B raw19064step1 raw19064step1Labels = mixedMoment B raw19064step2 raw19064step2Labels := by
      have ha : raw19064step2 = raw19064step1 := by apply Matrix.ext; unfold raw19064step2 raw19064step1; decide +kernel
      have hl : raw19064step1Labels = labelEmbedding9 ∘ raw19064step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19064step1 raw19064step1Labels raw19064step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw19065 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19065step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19065step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19065step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19065step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19065 raw19065Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw19065 raw19065Labels = mixedMoment B raw19065step0 raw19065step0Labels := by
      have ha : raw19065step0 = (fun i j => raw19065 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19065step0 raw19065; decide +kernel
      have hl : raw19065step0Labels = raw19065Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19065 raw19065Labels permutation155 permutation4
    mixedMoment B raw19065step0 raw19065step0Labels = mixedMoment B raw19065step1 raw19065step1Labels := by
      have ha : raw19065step1 = -raw19065step0 := by apply Matrix.ext; change ∀ i j, raw19065step1 i j = -(raw19065step0 i j); unfold raw19065step1 raw19065step0; decide +kernel
      have hl : raw19065step1Labels = raw19065step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19065step1 raw19065step1Labels = mixedMoment B raw19065step2 raw19065step2Labels := by
      have ha : raw19065step2 = raw19065step1 := by apply Matrix.ext; unfold raw19065step2 raw19065step1; decide +kernel
      have hl : raw19065step1Labels = labelEmbedding7 ∘ raw19065step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19065step1 raw19065step1Labels raw19065step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw19066 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19066step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19066step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19066step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19066 raw19066Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw19066 raw19066Labels = mixedMoment B raw19066step0 raw19066step0Labels := by
      have ha : raw19066step0 = (fun i j => raw19066 (permutation268 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19066step0 raw19066; decide +kernel
      have hl : raw19066step0Labels = raw19066Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19066 raw19066Labels permutation268 permutation4
    mixedMoment B raw19066step0 raw19066step0Labels = mixedMoment B raw19066step1 raw19066step1Labels := by
      have ha : raw19066step1 = -raw19066step0 := by apply Matrix.ext; change ∀ i j, raw19066step1 i j = -(raw19066step0 i j); unfold raw19066step1 raw19066step0; decide +kernel
      have hl : raw19066step1Labels = raw19066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19066step1 raw19066step1Labels = mixedMoment B raw19066step2 raw19066step2Labels := by
      have ha : raw19066step2 = raw19066step1 := by apply Matrix.ext; unfold raw19066step2 raw19066step1; decide +kernel
      have hl : raw19066step1Labels = labelEmbedding7 ∘ raw19066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19066step1 raw19066step1Labels raw19066step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw19067 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw19067step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19067step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19067step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19067 raw19067Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw19067 raw19067Labels = mixedMoment B raw19067step0 raw19067step0Labels := by
      have ha : raw19067step0 = (fun i j => raw19067 (permutation369 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19067step0 raw19067; decide +kernel
      have hl : raw19067step0Labels = raw19067Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19067 raw19067Labels permutation369 permutation5
    mixedMoment B raw19067step0 raw19067step0Labels = mixedMoment B raw19067step1 raw19067step1Labels := by
      have ha : raw19067step1 = -raw19067step0 := by apply Matrix.ext; change ∀ i j, raw19067step1 i j = -(raw19067step0 i j); unfold raw19067step1 raw19067step0; decide +kernel
      have hl : raw19067step1Labels = raw19067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19067step1 raw19067step1Labels = mixedMoment B raw19067step2 raw19067step2Labels := by
      have ha : raw19067step2 = raw19067step1 := by apply Matrix.ext; unfold raw19067step2 raw19067step1; decide +kernel
      have hl : raw19067step1Labels = labelEmbedding8 ∘ raw19067step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19067step1 raw19067step1Labels raw19067step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw19068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw19068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19068step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19068 raw19068Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19068 raw19068Labels = mixedMoment B raw19068step0 raw19068step0Labels := by
      have ha : raw19068step0 = (fun i j => raw19068 (permutation519 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19068step0 raw19068; decide +kernel
      have hl : raw19068step0Labels = raw19068Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19068 raw19068Labels permutation519 permutation4
    mixedMoment B raw19068step0 raw19068step0Labels = mixedMoment B raw19068step1 raw19068step1Labels := by
      have ha : raw19068step1 = raw19068step0 := by apply Matrix.ext; unfold raw19068step1 raw19068step0; decide +kernel
      have hl : raw19068step0Labels = labelEmbedding7 ∘ raw19068step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19068step0 raw19068step0Labels raw19068step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw19069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19069step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19069 raw19069Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw19069 raw19069Labels = mixedMoment B raw19069step0 raw19069step0Labels := by
      have ha : raw19069step0 = (fun i j => raw19069 (permutation504 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19069step0 raw19069; decide +kernel
      have hl : raw19069step0Labels = raw19069Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19069 raw19069Labels permutation504 permutation4
    mixedMoment B raw19069step0 raw19069step0Labels = mixedMoment B raw19069step1 raw19069step1Labels := by
      have ha : raw19069step1 = raw19069step0 := by apply Matrix.ext; unfold raw19069step1 raw19069step0; decide +kernel
      have hl : raw19069step0Labels = labelEmbedding7 ∘ raw19069step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19069step0 raw19069step0Labels raw19069step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw19070 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw19070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19070step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19070step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19070 raw19070Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw19070 raw19070Labels = mixedMoment B raw19070step0 raw19070step0Labels := by
      have ha : raw19070step0 = (fun i j => raw19070 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19070step0 raw19070; decide +kernel
      have hl : raw19070step0Labels = raw19070Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19070 raw19070Labels permutation153 permutation4
    mixedMoment B raw19070step0 raw19070step0Labels = mixedMoment B raw19070step1 raw19070step1Labels := by
      have ha : raw19070step1 = -raw19070step0 := by apply Matrix.ext; change ∀ i j, raw19070step1 i j = -(raw19070step0 i j); unfold raw19070step1 raw19070step0; decide +kernel
      have hl : raw19070step1Labels = raw19070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19070step1 raw19070step1Labels = mixedMoment B raw19070step2 raw19070step2Labels := by
      have ha : raw19070step2 = raw19070step1 := by apply Matrix.ext; unfold raw19070step2 raw19070step1; decide +kernel
      have hl : raw19070step1Labels = labelEmbedding7 ∘ raw19070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19070step1 raw19070step1Labels raw19070step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw19071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1]]
def raw19071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19071step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19071step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19071step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19071 raw19071Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw19071 raw19071Labels = mixedMoment B raw19071step0 raw19071step0Labels := by
      have ha : raw19071step0 = (fun i j => raw19071 (permutation266 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19071step0 raw19071; decide +kernel
      have hl : raw19071step0Labels = raw19071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19071 raw19071Labels permutation266 permutation4
    mixedMoment B raw19071step0 raw19071step0Labels = mixedMoment B raw19071step1 raw19071step1Labels := by
      have ha : raw19071step1 = -raw19071step0 := by apply Matrix.ext; change ∀ i j, raw19071step1 i j = -(raw19071step0 i j); unfold raw19071step1 raw19071step0; decide +kernel
      have hl : raw19071step1Labels = raw19071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19071step1 raw19071step1Labels = mixedMoment B raw19071step2 raw19071step2Labels := by
      have ha : raw19071step2 = raw19071step1 := by apply Matrix.ext; unfold raw19071step2 raw19071step1; decide +kernel
      have hl : raw19071step1Labels = labelEmbedding7 ∘ raw19071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19071step1 raw19071step1Labels raw19071step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
