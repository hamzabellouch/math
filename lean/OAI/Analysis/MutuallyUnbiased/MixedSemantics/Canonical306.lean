import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
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

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39168 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39168Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39168step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39168step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39168 raw39168Labels = mixedMoment B node3607 node3607Labels := by
  calc
    mixedMoment B raw39168 raw39168Labels = mixedMoment B raw39168step0 raw39168step0Labels := by
      have ha : raw39168step0 = (fun i j => raw39168 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39168step0 raw39168; decide +kernel
      have hl : raw39168step0Labels = raw39168Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39168 raw39168Labels permutation32 permutation7
    mixedMoment B raw39168step0 raw39168step0Labels = mixedMoment B raw39168step1 raw39168step1Labels := by
      have ha : raw39168step1 = -raw39168step0 := by apply Matrix.ext; change ∀ i j, raw39168step1 i j = -(raw39168step0 i j); unfold raw39168step1 raw39168step0; decide +kernel
      have hl : raw39168step1Labels = raw39168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39168step1 raw39168step1Labels = mixedMoment B raw39168step2 raw39168step2Labels := by
      have ha : raw39168step2 = raw39168step1 := by apply Matrix.ext; unfold raw39168step2 raw39168step1; decide +kernel
      have hl : raw39168step1Labels = labelEmbedding4 ∘ raw39168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39168step1 raw39168step1Labels raw39168step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3607 node3607Labels := by rfl

def raw39169 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39169 raw39169Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw39169 raw39169Labels = mixedMoment B raw39169step0 raw39169step0Labels := by
      have ha : raw39169step0 = (fun i j => raw39169 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39169step0 raw39169; decide +kernel
      have hl : raw39169step0Labels = raw39169Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39169 raw39169Labels permutation34 permutation3
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw39170 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw39170step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw39170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw39170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39170 raw39170Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw39170 raw39170Labels = mixedMoment B raw39170step0 raw39170step0Labels := by
      have ha : raw39170step0 = (fun i j => raw39170 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39170step0 raw39170; decide +kernel
      have hl : raw39170step0Labels = raw39170Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39170 raw39170Labels permutation33 permutation7
    mixedMoment B raw39170step0 raw39170step0Labels = mixedMoment B raw39170step1 raw39170step1Labels := by
      have ha : raw39170step1 = -raw39170step0 := by apply Matrix.ext; change ∀ i j, raw39170step1 i j = -(raw39170step0 i j); unfold raw39170step1 raw39170step0; decide +kernel
      have hl : raw39170step1Labels = raw39170step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39170step1 raw39170step1Labels = mixedMoment B raw39170step2 raw39170step2Labels := by
      have ha : raw39170step2 = raw39170step1 := by apply Matrix.ext; unfold raw39170step2 raw39170step1; decide +kernel
      have hl : raw39170step1Labels = labelEmbedding1 ∘ raw39170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39170step1 raw39170step1Labels raw39170step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw39171 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw39171Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39171step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw39171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39171 raw39171Labels = mixedMoment B node2598 node2598Labels := by
  calc
    mixedMoment B raw39171 raw39171Labels = mixedMoment B raw39171step0 raw39171step0Labels := by
      have ha : raw39171step0 = raw39171 := by apply Matrix.ext; unfold raw39171step0 raw39171; decide +kernel
      have hl : raw39171Labels = labelEmbedding2 ∘ raw39171step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39171 raw39171Labels raw39171step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2598 node2598Labels := by rfl

def raw39172 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw39172Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39172step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]
def raw39172step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![2, 1, -3]]
def raw39172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39172 raw39172Labels = mixedMoment B node3608 node3608Labels := by
  calc
    mixedMoment B raw39172 raw39172Labels = mixedMoment B raw39172step0 raw39172step0Labels := by
      have ha : raw39172step0 = (fun i j => raw39172 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39172step0 raw39172; decide +kernel
      have hl : raw39172step0Labels = raw39172Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39172 raw39172Labels permutation31 permutation7
    mixedMoment B raw39172step0 raw39172step0Labels = mixedMoment B raw39172step1 raw39172step1Labels := by
      have ha : raw39172step1 = raw39172step0 := by apply Matrix.ext; unfold raw39172step1 raw39172step0; decide +kernel
      have hl : raw39172step0Labels = labelEmbedding4 ∘ raw39172step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39172step0 raw39172step0Labels raw39172step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3608 node3608Labels := by rfl

def raw39173 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39173Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39173 raw39173Labels = mixedMoment B node2599 node2599Labels := by
  calc
    mixedMoment B raw39173 raw39173Labels = mixedMoment B raw39173step0 raw39173step0Labels := by
      have ha : raw39173step0 = raw39173 := by apply Matrix.ext; unfold raw39173step0 raw39173; decide +kernel
      have hl : raw39173Labels = labelEmbedding2 ∘ raw39173step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39173 raw39173Labels raw39173step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2599 node2599Labels := by rfl

def raw39174 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39174Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1]]
def raw39174step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw39174step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw39174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39174 raw39174Labels = mixedMoment B node3613 node3613Labels := by
  calc
    mixedMoment B raw39174 raw39174Labels = mixedMoment B raw39174step0 raw39174step0Labels := by
      have ha : raw39174step0 = (fun i j => raw39174 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39174step0 raw39174; decide +kernel
      have hl : raw39174step0Labels = raw39174Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39174 raw39174Labels permutation36 permutation7
    mixedMoment B raw39174step0 raw39174step0Labels = mixedMoment B raw39174step1 raw39174step1Labels := by
      have ha : raw39174step1 = -raw39174step0 := by apply Matrix.ext; change ∀ i j, raw39174step1 i j = -(raw39174step0 i j); unfold raw39174step1 raw39174step0; decide +kernel
      have hl : raw39174step1Labels = raw39174step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39174step1 raw39174step1Labels = mixedMoment B raw39174step2 raw39174step2Labels := by
      have ha : raw39174step2 = raw39174step1 := by apply Matrix.ext; unfold raw39174step2 raw39174step1; decide +kernel
      have hl : raw39174step1Labels = labelEmbedding4 ∘ raw39174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39174step1 raw39174step1Labels raw39174step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3613 node3613Labels := by rfl

def raw39175 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39175Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39175step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39175 raw39175Labels = mixedMoment B node2601 node2601Labels := by
  calc
    mixedMoment B raw39175 raw39175Labels = mixedMoment B raw39175step0 raw39175step0Labels := by
      have ha : raw39175step0 = raw39175 := by apply Matrix.ext; unfold raw39175step0 raw39175; decide +kernel
      have hl : raw39175Labels = labelEmbedding2 ∘ raw39175step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39175 raw39175Labels raw39175step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2601 node2601Labels := by rfl

def raw39176 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw39176Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39176step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]
def raw39176step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39176step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]
def raw39176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39176 raw39176Labels = mixedMoment B node3615 node3615Labels := by
  calc
    mixedMoment B raw39176 raw39176Labels = mixedMoment B raw39176step0 raw39176step0Labels := by
      have ha : raw39176step0 = (fun i j => raw39176 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39176step0 raw39176; decide +kernel
      have hl : raw39176step0Labels = raw39176Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39176 raw39176Labels permutation31 permutation5
    mixedMoment B raw39176step0 raw39176step0Labels = mixedMoment B raw39176step1 raw39176step1Labels := by
      have ha : raw39176step1 = raw39176step0 := by apply Matrix.ext; unfold raw39176step1 raw39176step0; decide +kernel
      have hl : raw39176step0Labels = labelEmbedding4 ∘ raw39176step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39176step0 raw39176step0Labels raw39176step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3615 node3615Labels := by rfl

def raw39177 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39177Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39177step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39177 raw39177Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw39177 raw39177Labels = mixedMoment B raw39177step0 raw39177step0Labels := by
      have ha : raw39177step0 = raw39177 := by apply Matrix.ext; unfold raw39177step0 raw39177; decide +kernel
      have hl : raw39177Labels = labelEmbedding2 ∘ raw39177step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39177 raw39177Labels raw39177step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw39178 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39178Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39178step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw39178step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39178step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def raw39178step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39178step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![2, 0, -2]]
def raw39178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39178 raw39178Labels = mixedMoment B node3614 node3614Labels := by
  calc
    mixedMoment B raw39178 raw39178Labels = mixedMoment B raw39178step0 raw39178step0Labels := by
      have ha : raw39178step0 = (fun i j => raw39178 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39178step0 raw39178; decide +kernel
      have hl : raw39178step0Labels = raw39178Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39178 raw39178Labels permutation8 permutation7
    mixedMoment B raw39178step0 raw39178step0Labels = mixedMoment B raw39178step1 raw39178step1Labels := by
      have ha : raw39178step1 = -raw39178step0 := by apply Matrix.ext; change ∀ i j, raw39178step1 i j = -(raw39178step0 i j); unfold raw39178step1 raw39178step0; decide +kernel
      have hl : raw39178step1Labels = raw39178step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39178step1 raw39178step1Labels = mixedMoment B raw39178step2 raw39178step2Labels := by
      have ha : raw39178step2 = raw39178step1 := by apply Matrix.ext; unfold raw39178step2 raw39178step1; decide +kernel
      have hl : raw39178step1Labels = labelEmbedding4 ∘ raw39178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39178step1 raw39178step1Labels raw39178step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3614 node3614Labels := by rfl

def raw39179 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39179Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39179step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39179 raw39179Labels = mixedMoment B node2605 node2605Labels := by
  calc
    mixedMoment B raw39179 raw39179Labels = mixedMoment B raw39179step0 raw39179step0Labels := by
      have ha : raw39179step0 = raw39179 := by apply Matrix.ext; unfold raw39179step0 raw39179; decide +kernel
      have hl : raw39179Labels = labelEmbedding2 ∘ raw39179step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39179 raw39179Labels raw39179step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2605 node2605Labels := by rfl

def raw39180 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39180Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39180step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw39180step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39180step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw39180step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39180step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw39180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39180 raw39180Labels = mixedMoment B node3616 node3616Labels := by
  calc
    mixedMoment B raw39180 raw39180Labels = mixedMoment B raw39180step0 raw39180step0Labels := by
      have ha : raw39180step0 = (fun i j => raw39180 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39180step0 raw39180; decide +kernel
      have hl : raw39180step0Labels = raw39180Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39180 raw39180Labels permutation8 permutation7
    mixedMoment B raw39180step0 raw39180step0Labels = mixedMoment B raw39180step1 raw39180step1Labels := by
      have ha : raw39180step1 = -raw39180step0 := by apply Matrix.ext; change ∀ i j, raw39180step1 i j = -(raw39180step0 i j); unfold raw39180step1 raw39180step0; decide +kernel
      have hl : raw39180step1Labels = raw39180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39180step1 raw39180step1Labels = mixedMoment B raw39180step2 raw39180step2Labels := by
      have ha : raw39180step2 = raw39180step1 := by apply Matrix.ext; unfold raw39180step2 raw39180step1; decide +kernel
      have hl : raw39180step1Labels = labelEmbedding4 ∘ raw39180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39180step1 raw39180step1Labels raw39180step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3616 node3616Labels := by rfl

def raw39181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw39181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw39181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw39181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39181 raw39181Labels = mixedMoment B node3620 node3620Labels := by
  calc
    mixedMoment B raw39181 raw39181Labels = mixedMoment B raw39181step0 raw39181step0Labels := by
      have ha : raw39181step0 = (fun i j => raw39181 (permutation216 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39181step0 raw39181; decide +kernel
      have hl : raw39181step0Labels = raw39181Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39181 raw39181Labels permutation216 permutation7
    mixedMoment B raw39181step0 raw39181step0Labels = mixedMoment B raw39181step1 raw39181step1Labels := by
      have ha : raw39181step1 = -raw39181step0 := by apply Matrix.ext; change ∀ i j, raw39181step1 i j = -(raw39181step0 i j); unfold raw39181step1 raw39181step0; decide +kernel
      have hl : raw39181step1Labels = raw39181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39181step1 raw39181step1Labels = mixedMoment B raw39181step2 raw39181step2Labels := by
      have ha : raw39181step2 = raw39181step1 := by apply Matrix.ext; unfold raw39181step2 raw39181step1; decide +kernel
      have hl : raw39181step1Labels = labelEmbedding1 ∘ raw39181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39181step1 raw39181step1Labels raw39181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3620 node3620Labels := by rfl

def raw39182 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw39182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39182 raw39182Labels = mixedMoment B node2856 node2856Labels := by
  calc
    mixedMoment B raw39182 raw39182Labels = mixedMoment B raw39182step0 raw39182step0Labels := by
      have ha : raw39182step0 = (fun i j => raw39182 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39182step0 raw39182; decide +kernel
      have hl : raw39182step0Labels = raw39182Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39182 raw39182Labels permutation32 permutation3
    _ = mixedMoment B node2856 node2856Labels := by rfl

def raw39183 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw39183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw39183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw39183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw39183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39183 raw39183Labels = mixedMoment B node3630 node3630Labels := by
  calc
    mixedMoment B raw39183 raw39183Labels = mixedMoment B raw39183step0 raw39183step0Labels := by
      have ha : raw39183step0 = (fun i j => raw39183 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39183step0 raw39183; decide +kernel
      have hl : raw39183step0Labels = raw39183Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39183 raw39183Labels permutation48 permutation7
    mixedMoment B raw39183step0 raw39183step0Labels = mixedMoment B raw39183step1 raw39183step1Labels := by
      have ha : raw39183step1 = -raw39183step0 := by apply Matrix.ext; change ∀ i j, raw39183step1 i j = -(raw39183step0 i j); unfold raw39183step1 raw39183step0; decide +kernel
      have hl : raw39183step1Labels = raw39183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39183step1 raw39183step1Labels = mixedMoment B raw39183step2 raw39183step2Labels := by
      have ha : raw39183step2 = raw39183step1 := by apply Matrix.ext; unfold raw39183step2 raw39183step1; decide +kernel
      have hl : raw39183step1Labels = labelEmbedding1 ∘ raw39183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39183step1 raw39183step1Labels raw39183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3630 node3630Labels := by rfl

def raw39184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw39184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw39184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw39184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39184 raw39184Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw39184 raw39184Labels = mixedMoment B raw39184step0 raw39184step0Labels := by
      have ha : raw39184step0 = (fun i j => raw39184 (permutation184 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39184step0 raw39184; decide +kernel
      have hl : raw39184step0Labels = raw39184Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39184 raw39184Labels permutation184 permutation7
    mixedMoment B raw39184step0 raw39184step0Labels = mixedMoment B raw39184step1 raw39184step1Labels := by
      have ha : raw39184step1 = -raw39184step0 := by apply Matrix.ext; change ∀ i j, raw39184step1 i j = -(raw39184step0 i j); unfold raw39184step1 raw39184step0; decide +kernel
      have hl : raw39184step1Labels = raw39184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39184step1 raw39184step1Labels = mixedMoment B raw39184step2 raw39184step2Labels := by
      have ha : raw39184step2 = raw39184step1 := by apply Matrix.ext; unfold raw39184step2 raw39184step1; decide +kernel
      have hl : raw39184step1Labels = labelEmbedding1 ∘ raw39184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39184step1 raw39184step1Labels raw39184step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

def raw39185 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39185 raw39185Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw39185 raw39185Labels = mixedMoment B raw39185step0 raw39185step0Labels := by
      have ha : raw39185step0 = (fun i j => raw39185 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39185step0 raw39185; decide +kernel
      have hl : raw39185step0Labels = raw39185Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39185 raw39185Labels permutation32 permutation3
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw39186 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw39186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw39186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw39186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39186 raw39186Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw39186 raw39186Labels = mixedMoment B raw39186step0 raw39186step0Labels := by
      have ha : raw39186step0 = (fun i j => raw39186 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39186step0 raw39186; decide +kernel
      have hl : raw39186step0Labels = raw39186Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39186 raw39186Labels permutation40 permutation7
    mixedMoment B raw39186step0 raw39186step0Labels = mixedMoment B raw39186step1 raw39186step1Labels := by
      have ha : raw39186step1 = -raw39186step0 := by apply Matrix.ext; change ∀ i j, raw39186step1 i j = -(raw39186step0 i j); unfold raw39186step1 raw39186step0; decide +kernel
      have hl : raw39186step1Labels = raw39186step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39186step1 raw39186step1Labels = mixedMoment B raw39186step2 raw39186step2Labels := by
      have ha : raw39186step2 = raw39186step1 := by apply Matrix.ext; unfold raw39186step2 raw39186step1; decide +kernel
      have hl : raw39186step1Labels = labelEmbedding1 ∘ raw39186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39186step1 raw39186step1Labels raw39186step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

def raw39187 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39187 raw39187Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw39187 raw39187Labels = mixedMoment B raw39187step0 raw39187step0Labels := by
      have ha : raw39187step0 = (fun i j => raw39187 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39187step0 raw39187; decide +kernel
      have hl : raw39187step0Labels = raw39187Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39187 raw39187Labels permutation34 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw39188 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw39188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw39188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw39188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39188 raw39188Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw39188 raw39188Labels = mixedMoment B raw39188step0 raw39188step0Labels := by
      have ha : raw39188step0 = (fun i j => raw39188 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39188step0 raw39188; decide +kernel
      have hl : raw39188step0Labels = raw39188Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39188 raw39188Labels permutation42 permutation7
    mixedMoment B raw39188step0 raw39188step0Labels = mixedMoment B raw39188step1 raw39188step1Labels := by
      have ha : raw39188step1 = -raw39188step0 := by apply Matrix.ext; change ∀ i j, raw39188step1 i j = -(raw39188step0 i j); unfold raw39188step1 raw39188step0; decide +kernel
      have hl : raw39188step1Labels = raw39188step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39188step1 raw39188step1Labels = mixedMoment B raw39188step2 raw39188step2Labels := by
      have ha : raw39188step2 = raw39188step1 := by apply Matrix.ext; unfold raw39188step2 raw39188step1; decide +kernel
      have hl : raw39188step1Labels = labelEmbedding1 ∘ raw39188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39188step1 raw39188step1Labels raw39188step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw39189 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39189step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw39189step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39189 raw39189Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw39189 raw39189Labels = mixedMoment B raw39189step0 raw39189step0Labels := by
      have ha : raw39189step0 = (fun i j => raw39189 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39189step0 raw39189; decide +kernel
      have hl : raw39189step0Labels = raw39189Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39189 raw39189Labels permutation9 permutation3
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw39190 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39190step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw39190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw39190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw39190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39190 raw39190Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw39190 raw39190Labels = mixedMoment B raw39190step0 raw39190step0Labels := by
      have ha : raw39190step0 = (fun i j => raw39190 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39190step0 raw39190; decide +kernel
      have hl : raw39190step0Labels = raw39190Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39190 raw39190Labels permutation10 permutation7
    mixedMoment B raw39190step0 raw39190step0Labels = mixedMoment B raw39190step1 raw39190step1Labels := by
      have ha : raw39190step1 = -raw39190step0 := by apply Matrix.ext; change ∀ i j, raw39190step1 i j = -(raw39190step0 i j); unfold raw39190step1 raw39190step0; decide +kernel
      have hl : raw39190step1Labels = raw39190step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39190step1 raw39190step1Labels = mixedMoment B raw39190step2 raw39190step2Labels := by
      have ha : raw39190step2 = raw39190step1 := by apply Matrix.ext; unfold raw39190step2 raw39190step1; decide +kernel
      have hl : raw39190step1Labels = labelEmbedding1 ∘ raw39190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39190step1 raw39190step1Labels raw39190step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3631 node3631Labels := by rfl

def raw39191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39191 raw39191Labels = mixedMoment B node2839 node2839Labels := by
  calc
    mixedMoment B raw39191 raw39191Labels = mixedMoment B raw39191step0 raw39191step0Labels := by
      have ha : raw39191step0 = (fun i j => raw39191 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39191step0 raw39191; decide +kernel
      have hl : raw39191step0Labels = raw39191Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39191 raw39191Labels permutation152 permutation3
    _ = mixedMoment B node2839 node2839Labels := by rfl

def raw39192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw39192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39192 raw39192Labels = mixedMoment B node2839 node2839Labels := by
  calc
    mixedMoment B raw39192 raw39192Labels = mixedMoment B raw39192step0 raw39192step0Labels := by
      have ha : raw39192step0 = (fun i j => raw39192 (permutation265 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39192step0 raw39192; decide +kernel
      have hl : raw39192step0Labels = raw39192Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39192 raw39192Labels permutation265 permutation5
    mixedMoment B raw39192step0 raw39192step0Labels = mixedMoment B raw39192step1 raw39192step1Labels := by
      have ha : raw39192step1 = -raw39192step0 := by apply Matrix.ext; change ∀ i j, raw39192step1 i j = -(raw39192step0 i j); unfold raw39192step1 raw39192step0; decide +kernel
      have hl : raw39192step1Labels = raw39192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39192step1 raw39192step1Labels = mixedMoment B raw39192step2 raw39192step2Labels := by
      have ha : raw39192step2 = raw39192step1 := by apply Matrix.ext; unfold raw39192step2 raw39192step1; decide +kernel
      have hl : raw39192step1Labels = labelEmbedding1 ∘ raw39192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39192step1 raw39192step1Labels raw39192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2839 node2839Labels := by rfl

def raw39193 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39193 raw39193Labels = mixedMoment B node2840 node2840Labels := by
  calc
    mixedMoment B raw39193 raw39193Labels = mixedMoment B raw39193step0 raw39193step0Labels := by
      have ha : raw39193step0 = (fun i j => raw39193 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39193step0 raw39193; decide +kernel
      have hl : raw39193step0Labels = raw39193Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39193 raw39193Labels permutation32 permutation3
    _ = mixedMoment B node2840 node2840Labels := by rfl

def raw39194 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw39194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39194 raw39194Labels = mixedMoment B node2840 node2840Labels := by
  calc
    mixedMoment B raw39194 raw39194Labels = mixedMoment B raw39194step0 raw39194step0Labels := by
      have ha : raw39194step0 = (fun i j => raw39194 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39194step0 raw39194; decide +kernel
      have hl : raw39194step0Labels = raw39194Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39194 raw39194Labels permutation56 permutation5
    mixedMoment B raw39194step0 raw39194step0Labels = mixedMoment B raw39194step1 raw39194step1Labels := by
      have ha : raw39194step1 = -raw39194step0 := by apply Matrix.ext; change ∀ i j, raw39194step1 i j = -(raw39194step0 i j); unfold raw39194step1 raw39194step0; decide +kernel
      have hl : raw39194step1Labels = raw39194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39194step1 raw39194step1Labels = mixedMoment B raw39194step2 raw39194step2Labels := by
      have ha : raw39194step2 = raw39194step1 := by apply Matrix.ext; unfold raw39194step2 raw39194step1; decide +kernel
      have hl : raw39194step1Labels = labelEmbedding1 ∘ raw39194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39194step1 raw39194step1Labels raw39194step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2840 node2840Labels := by rfl

def raw39195 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw39195Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39195step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def raw39195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39195 raw39195Labels = mixedMoment B node2843 node2843Labels := by
  calc
    mixedMoment B raw39195 raw39195Labels = mixedMoment B raw39195step0 raw39195step0Labels := by
      have ha : raw39195step0 = (fun i j => raw39195 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39195step0 raw39195; decide +kernel
      have hl : raw39195step0Labels = raw39195Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39195 raw39195Labels permutation8 permutation3
    _ = mixedMoment B node2843 node2843Labels := by rfl

def raw39196 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw39196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39196step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-2, 0, 2], ![-2, 0, 2]]
def raw39196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def raw39196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39196step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def raw39196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39196 raw39196Labels = mixedMoment B node2843 node2843Labels := by
  calc
    mixedMoment B raw39196 raw39196Labels = mixedMoment B raw39196step0 raw39196step0Labels := by
      have ha : raw39196step0 = (fun i j => raw39196 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39196step0 raw39196; decide +kernel
      have hl : raw39196step0Labels = raw39196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39196 raw39196Labels permutation14 permutation5
    mixedMoment B raw39196step0 raw39196step0Labels = mixedMoment B raw39196step1 raw39196step1Labels := by
      have ha : raw39196step1 = -raw39196step0 := by apply Matrix.ext; change ∀ i j, raw39196step1 i j = -(raw39196step0 i j); unfold raw39196step1 raw39196step0; decide +kernel
      have hl : raw39196step1Labels = raw39196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39196step1 raw39196step1Labels = mixedMoment B raw39196step2 raw39196step2Labels := by
      have ha : raw39196step2 = raw39196step1 := by apply Matrix.ext; unfold raw39196step2 raw39196step1; decide +kernel
      have hl : raw39196step1Labels = labelEmbedding1 ∘ raw39196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39196step1 raw39196step1Labels raw39196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2843 node2843Labels := by rfl

def raw39197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39197Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39197 raw39197Labels = mixedMoment B node2671 node2671Labels := by
  calc
    mixedMoment B raw39197 raw39197Labels = mixedMoment B raw39197step0 raw39197step0Labels := by
      have ha : raw39197step0 = raw39197 := by apply Matrix.ext; unfold raw39197step0 raw39197; decide +kernel
      have hl : raw39197Labels = labelEmbedding2 ∘ raw39197step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39197 raw39197Labels raw39197step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2671 node2671Labels := by rfl

def raw39198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39198Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw39198step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39198step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39198step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39198 raw39198Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw39198 raw39198Labels = mixedMoment B raw39198step0 raw39198step0Labels := by
      have ha : raw39198step0 = (fun i j => raw39198 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39198step0 raw39198; decide +kernel
      have hl : raw39198step0Labels = raw39198Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39198 raw39198Labels permutation152 permutation7
    mixedMoment B raw39198step0 raw39198step0Labels = mixedMoment B raw39198step1 raw39198step1Labels := by
      have ha : raw39198step1 = -raw39198step0 := by apply Matrix.ext; change ∀ i j, raw39198step1 i j = -(raw39198step0 i j); unfold raw39198step1 raw39198step0; decide +kernel
      have hl : raw39198step1Labels = raw39198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39198step1 raw39198step1Labels = mixedMoment B raw39198step2 raw39198step2Labels := by
      have ha : raw39198step2 = raw39198step1 := by apply Matrix.ext; unfold raw39198step2 raw39198step1; decide +kernel
      have hl : raw39198step1Labels = labelEmbedding4 ∘ raw39198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39198step1 raw39198step1Labels raw39198step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3390 node3390Labels := by rfl

def raw39199 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39199Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39199 raw39199Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw39199 raw39199Labels = mixedMoment B raw39199step0 raw39199step0Labels := by
      have ha : raw39199step0 = raw39199 := by apply Matrix.ext; unfold raw39199step0 raw39199; decide +kernel
      have hl : raw39199Labels = labelEmbedding2 ∘ raw39199step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39199 raw39199Labels raw39199step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw39200 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39200Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw39200step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39200step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39200step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39200 raw39200Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw39200 raw39200Labels = mixedMoment B raw39200step0 raw39200step0Labels := by
      have ha : raw39200step0 = (fun i j => raw39200 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39200step0 raw39200; decide +kernel
      have hl : raw39200step0Labels = raw39200Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39200 raw39200Labels permutation32 permutation7
    mixedMoment B raw39200step0 raw39200step0Labels = mixedMoment B raw39200step1 raw39200step1Labels := by
      have ha : raw39200step1 = -raw39200step0 := by apply Matrix.ext; change ∀ i j, raw39200step1 i j = -(raw39200step0 i j); unfold raw39200step1 raw39200step0; decide +kernel
      have hl : raw39200step1Labels = raw39200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39200step1 raw39200step1Labels = mixedMoment B raw39200step2 raw39200step2Labels := by
      have ha : raw39200step2 = raw39200step1 := by apply Matrix.ext; unfold raw39200step2 raw39200step1; decide +kernel
      have hl : raw39200step1Labels = labelEmbedding4 ∘ raw39200step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39200step1 raw39200step1Labels raw39200step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw39201 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39201Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39201 raw39201Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw39201 raw39201Labels = mixedMoment B raw39201step0 raw39201step0Labels := by
      have ha : raw39201step0 = raw39201 := by apply Matrix.ext; unfold raw39201step0 raw39201; decide +kernel
      have hl : raw39201Labels = labelEmbedding2 ∘ raw39201step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39201 raw39201Labels raw39201step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw39202 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39202Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39202step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39202step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39202step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39202 raw39202Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw39202 raw39202Labels = mixedMoment B raw39202step0 raw39202step0Labels := by
      have ha : raw39202step0 = (fun i j => raw39202 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39202step0 raw39202; decide +kernel
      have hl : raw39202step0Labels = raw39202Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39202 raw39202Labels permutation32 permutation7
    mixedMoment B raw39202step0 raw39202step0Labels = mixedMoment B raw39202step1 raw39202step1Labels := by
      have ha : raw39202step1 = -raw39202step0 := by apply Matrix.ext; change ∀ i j, raw39202step1 i j = -(raw39202step0 i j); unfold raw39202step1 raw39202step0; decide +kernel
      have hl : raw39202step1Labels = raw39202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39202step1 raw39202step1Labels = mixedMoment B raw39202step2 raw39202step2Labels := by
      have ha : raw39202step2 = raw39202step1 := by apply Matrix.ext; unfold raw39202step2 raw39202step1; decide +kernel
      have hl : raw39202step1Labels = labelEmbedding4 ∘ raw39202step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39202step1 raw39202step1Labels raw39202step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw39203 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw39203Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39203step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw39203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39203 raw39203Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw39203 raw39203Labels = mixedMoment B raw39203step0 raw39203step0Labels := by
      have ha : raw39203step0 = raw39203 := by apply Matrix.ext; unfold raw39203step0 raw39203; decide +kernel
      have hl : raw39203Labels = labelEmbedding2 ∘ raw39203step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39203 raw39203Labels raw39203step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw39204 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw39204Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39204step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw39204step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39204step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39204step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39204step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39204 raw39204Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw39204 raw39204Labels = mixedMoment B raw39204step0 raw39204step0Labels := by
      have ha : raw39204step0 = (fun i j => raw39204 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39204step0 raw39204; decide +kernel
      have hl : raw39204step0Labels = raw39204Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39204 raw39204Labels permutation8 permutation7
    mixedMoment B raw39204step0 raw39204step0Labels = mixedMoment B raw39204step1 raw39204step1Labels := by
      have ha : raw39204step1 = -raw39204step0 := by apply Matrix.ext; change ∀ i j, raw39204step1 i j = -(raw39204step0 i j); unfold raw39204step1 raw39204step0; decide +kernel
      have hl : raw39204step1Labels = raw39204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39204step1 raw39204step1Labels = mixedMoment B raw39204step2 raw39204step2Labels := by
      have ha : raw39204step2 = raw39204step1 := by apply Matrix.ext; unfold raw39204step2 raw39204step1; decide +kernel
      have hl : raw39204step1Labels = labelEmbedding4 ∘ raw39204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39204step1 raw39204step1Labels raw39204step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw39205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39205Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39205 raw39205Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw39205 raw39205Labels = mixedMoment B raw39205step0 raw39205step0Labels := by
      have ha : raw39205step0 = raw39205 := by apply Matrix.ext; unfold raw39205step0 raw39205; decide +kernel
      have hl : raw39205Labels = labelEmbedding2 ∘ raw39205step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39205 raw39205Labels raw39205step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw39206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39206Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw39206step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39206step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39206step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39206step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39206 raw39206Labels = mixedMoment B node3493 node3493Labels := by
  calc
    mixedMoment B raw39206 raw39206Labels = mixedMoment B raw39206step0 raw39206step0Labels := by
      have ha : raw39206step0 = (fun i j => raw39206 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39206step0 raw39206; decide +kernel
      have hl : raw39206step0Labels = raw39206Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39206 raw39206Labels permutation152 permutation7
    mixedMoment B raw39206step0 raw39206step0Labels = mixedMoment B raw39206step1 raw39206step1Labels := by
      have ha : raw39206step1 = -raw39206step0 := by apply Matrix.ext; change ∀ i j, raw39206step1 i j = -(raw39206step0 i j); unfold raw39206step1 raw39206step0; decide +kernel
      have hl : raw39206step1Labels = raw39206step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39206step1 raw39206step1Labels = mixedMoment B raw39206step2 raw39206step2Labels := by
      have ha : raw39206step2 = raw39206step1 := by apply Matrix.ext; unfold raw39206step2 raw39206step1; decide +kernel
      have hl : raw39206step1Labels = labelEmbedding4 ∘ raw39206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39206step1 raw39206step1Labels raw39206step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3493 node3493Labels := by rfl

def raw39207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39207Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39207 raw39207Labels = mixedMoment B node2703 node2703Labels := by
  calc
    mixedMoment B raw39207 raw39207Labels = mixedMoment B raw39207step0 raw39207step0Labels := by
      have ha : raw39207step0 = raw39207 := by apply Matrix.ext; unfold raw39207step0 raw39207; decide +kernel
      have hl : raw39207Labels = labelEmbedding2 ∘ raw39207step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39207 raw39207Labels raw39207step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2703 node2703Labels := by rfl

def raw39208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39208Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39208step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39208step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39208step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39208 raw39208Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw39208 raw39208Labels = mixedMoment B raw39208step0 raw39208step0Labels := by
      have ha : raw39208step0 = (fun i j => raw39208 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39208step0 raw39208; decide +kernel
      have hl : raw39208step0Labels = raw39208Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39208 raw39208Labels permutation152 permutation7
    mixedMoment B raw39208step0 raw39208step0Labels = mixedMoment B raw39208step1 raw39208step1Labels := by
      have ha : raw39208step1 = -raw39208step0 := by apply Matrix.ext; change ∀ i j, raw39208step1 i j = -(raw39208step0 i j); unfold raw39208step1 raw39208step0; decide +kernel
      have hl : raw39208step1Labels = raw39208step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39208step1 raw39208step1Labels = mixedMoment B raw39208step2 raw39208step2Labels := by
      have ha : raw39208step2 = raw39208step1 := by apply Matrix.ext; unfold raw39208step2 raw39208step1; decide +kernel
      have hl : raw39208step1Labels = labelEmbedding4 ∘ raw39208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39208step1 raw39208step1Labels raw39208step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3496 node3496Labels := by rfl

def raw39209 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39209Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39209 raw39209Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw39209 raw39209Labels = mixedMoment B raw39209step0 raw39209step0Labels := by
      have ha : raw39209step0 = raw39209 := by apply Matrix.ext; unfold raw39209step0 raw39209; decide +kernel
      have hl : raw39209Labels = labelEmbedding2 ∘ raw39209step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39209 raw39209Labels raw39209step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw39210 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39210Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw39210step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39210step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39210step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39210 raw39210Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw39210 raw39210Labels = mixedMoment B raw39210step0 raw39210step0Labels := by
      have ha : raw39210step0 = (fun i j => raw39210 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39210step0 raw39210; decide +kernel
      have hl : raw39210step0Labels = raw39210Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39210 raw39210Labels permutation32 permutation7
    mixedMoment B raw39210step0 raw39210step0Labels = mixedMoment B raw39210step1 raw39210step1Labels := by
      have ha : raw39210step1 = -raw39210step0 := by apply Matrix.ext; change ∀ i j, raw39210step1 i j = -(raw39210step0 i j); unfold raw39210step1 raw39210step0; decide +kernel
      have hl : raw39210step1Labels = raw39210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39210step1 raw39210step1Labels = mixedMoment B raw39210step2 raw39210step2Labels := by
      have ha : raw39210step2 = raw39210step1 := by apply Matrix.ext; unfold raw39210step2 raw39210step1; decide +kernel
      have hl : raw39210step1Labels = labelEmbedding4 ∘ raw39210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39210step1 raw39210step1Labels raw39210step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3498 node3498Labels := by rfl

def raw39211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39211Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39211 raw39211Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw39211 raw39211Labels = mixedMoment B raw39211step0 raw39211step0Labels := by
      have ha : raw39211step0 = raw39211 := by apply Matrix.ext; unfold raw39211step0 raw39211; decide +kernel
      have hl : raw39211Labels = labelEmbedding2 ∘ raw39211step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39211 raw39211Labels raw39211step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw39212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39212Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39212step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39212step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39212step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39212 raw39212Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw39212 raw39212Labels = mixedMoment B raw39212step0 raw39212step0Labels := by
      have ha : raw39212step0 = (fun i j => raw39212 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39212step0 raw39212; decide +kernel
      have hl : raw39212step0Labels = raw39212Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39212 raw39212Labels permutation158 permutation7
    mixedMoment B raw39212step0 raw39212step0Labels = mixedMoment B raw39212step1 raw39212step1Labels := by
      have ha : raw39212step1 = -raw39212step0 := by apply Matrix.ext; change ∀ i j, raw39212step1 i j = -(raw39212step0 i j); unfold raw39212step1 raw39212step0; decide +kernel
      have hl : raw39212step1Labels = raw39212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39212step1 raw39212step1Labels = mixedMoment B raw39212step2 raw39212step2Labels := by
      have ha : raw39212step2 = raw39212step1 := by apply Matrix.ext; unfold raw39212step2 raw39212step1; decide +kernel
      have hl : raw39212step1Labels = labelEmbedding4 ∘ raw39212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39212step1 raw39212step1Labels raw39212step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw39213 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39213Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39213 raw39213Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw39213 raw39213Labels = mixedMoment B raw39213step0 raw39213step0Labels := by
      have ha : raw39213step0 = raw39213 := by apply Matrix.ext; unfold raw39213step0 raw39213; decide +kernel
      have hl : raw39213Labels = labelEmbedding2 ∘ raw39213step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39213 raw39213Labels raw39213step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw39214 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39214Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39214step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39214step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39214 raw39214Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw39214 raw39214Labels = mixedMoment B raw39214step0 raw39214step0Labels := by
      have ha : raw39214step0 = (fun i j => raw39214 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39214step0 raw39214; decide +kernel
      have hl : raw39214step0Labels = raw39214Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39214 raw39214Labels permutation34 permutation7
    mixedMoment B raw39214step0 raw39214step0Labels = mixedMoment B raw39214step1 raw39214step1Labels := by
      have ha : raw39214step1 = -raw39214step0 := by apply Matrix.ext; change ∀ i j, raw39214step1 i j = -(raw39214step0 i j); unfold raw39214step1 raw39214step0; decide +kernel
      have hl : raw39214step1Labels = raw39214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39214step1 raw39214step1Labels = mixedMoment B raw39214step2 raw39214step2Labels := by
      have ha : raw39214step2 = raw39214step1 := by apply Matrix.ext; unfold raw39214step2 raw39214step1; decide +kernel
      have hl : raw39214step1Labels = labelEmbedding4 ∘ raw39214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39214step1 raw39214step1Labels raw39214step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw39215 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39215Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39215 raw39215Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw39215 raw39215Labels = mixedMoment B raw39215step0 raw39215step0Labels := by
      have ha : raw39215step0 = raw39215 := by apply Matrix.ext; unfold raw39215step0 raw39215; decide +kernel
      have hl : raw39215Labels = labelEmbedding2 ∘ raw39215step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39215 raw39215Labels raw39215step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw39216 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39216Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw39216step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39216step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39216 raw39216Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw39216 raw39216Labels = mixedMoment B raw39216step0 raw39216step0Labels := by
      have ha : raw39216step0 = (fun i j => raw39216 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39216step0 raw39216; decide +kernel
      have hl : raw39216step0Labels = raw39216Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39216 raw39216Labels permutation32 permutation7
    mixedMoment B raw39216step0 raw39216step0Labels = mixedMoment B raw39216step1 raw39216step1Labels := by
      have ha : raw39216step1 = -raw39216step0 := by apply Matrix.ext; change ∀ i j, raw39216step1 i j = -(raw39216step0 i j); unfold raw39216step1 raw39216step0; decide +kernel
      have hl : raw39216step1Labels = raw39216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39216step1 raw39216step1Labels = mixedMoment B raw39216step2 raw39216step2Labels := by
      have ha : raw39216step2 = raw39216step1 := by apply Matrix.ext; unfold raw39216step2 raw39216step1; decide +kernel
      have hl : raw39216step1Labels = labelEmbedding4 ∘ raw39216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39216step1 raw39216step1Labels raw39216step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw39217 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw39217Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39217step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw39217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39217 raw39217Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw39217 raw39217Labels = mixedMoment B raw39217step0 raw39217step0Labels := by
      have ha : raw39217step0 = raw39217 := by apply Matrix.ext; unfold raw39217step0 raw39217; decide +kernel
      have hl : raw39217Labels = labelEmbedding2 ∘ raw39217step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39217 raw39217Labels raw39217step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw39218 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw39218Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39218step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39218step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39218step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39218 raw39218Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw39218 raw39218Labels = mixedMoment B raw39218step0 raw39218step0Labels := by
      have ha : raw39218step0 = (fun i j => raw39218 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39218step0 raw39218; decide +kernel
      have hl : raw39218step0Labels = raw39218Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39218 raw39218Labels permutation31 permutation7
    mixedMoment B raw39218step0 raw39218step0Labels = mixedMoment B raw39218step1 raw39218step1Labels := by
      have ha : raw39218step1 = raw39218step0 := by apply Matrix.ext; unfold raw39218step1 raw39218step0; decide +kernel
      have hl : raw39218step0Labels = labelEmbedding4 ∘ raw39218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39218step0 raw39218step0Labels raw39218step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

def raw39219 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39219Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39219 raw39219Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw39219 raw39219Labels = mixedMoment B raw39219step0 raw39219step0Labels := by
      have ha : raw39219step0 = raw39219 := by apply Matrix.ext; unfold raw39219step0 raw39219; decide +kernel
      have hl : raw39219Labels = labelEmbedding2 ∘ raw39219step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39219 raw39219Labels raw39219step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw39220 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39220Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39220step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39220step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39220 raw39220Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw39220 raw39220Labels = mixedMoment B raw39220step0 raw39220step0Labels := by
      have ha : raw39220step0 = (fun i j => raw39220 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39220step0 raw39220; decide +kernel
      have hl : raw39220step0Labels = raw39220Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39220 raw39220Labels permutation32 permutation7
    mixedMoment B raw39220step0 raw39220step0Labels = mixedMoment B raw39220step1 raw39220step1Labels := by
      have ha : raw39220step1 = -raw39220step0 := by apply Matrix.ext; change ∀ i j, raw39220step1 i j = -(raw39220step0 i j); unfold raw39220step1 raw39220step0; decide +kernel
      have hl : raw39220step1Labels = raw39220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39220step1 raw39220step1Labels = mixedMoment B raw39220step2 raw39220step2Labels := by
      have ha : raw39220step2 = raw39220step1 := by apply Matrix.ext; unfold raw39220step2 raw39220step1; decide +kernel
      have hl : raw39220step1Labels = labelEmbedding4 ∘ raw39220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39220step1 raw39220step1Labels raw39220step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw39221 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39221Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39221step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39221 raw39221Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw39221 raw39221Labels = mixedMoment B raw39221step0 raw39221step0Labels := by
      have ha : raw39221step0 = raw39221 := by apply Matrix.ext; unfold raw39221step0 raw39221; decide +kernel
      have hl : raw39221Labels = labelEmbedding2 ∘ raw39221step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39221 raw39221Labels raw39221step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw39222 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39222Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39222step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39222step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39222 raw39222Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw39222 raw39222Labels = mixedMoment B raw39222step0 raw39222step0Labels := by
      have ha : raw39222step0 = (fun i j => raw39222 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39222step0 raw39222; decide +kernel
      have hl : raw39222step0Labels = raw39222Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39222 raw39222Labels permutation31 permutation7
    mixedMoment B raw39222step0 raw39222step0Labels = mixedMoment B raw39222step1 raw39222step1Labels := by
      have ha : raw39222step1 = raw39222step0 := by apply Matrix.ext; unfold raw39222step1 raw39222step0; decide +kernel
      have hl : raw39222step0Labels = labelEmbedding4 ∘ raw39222step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39222step0 raw39222step0Labels raw39222step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw39223 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39223Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39223step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39223 raw39223Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw39223 raw39223Labels = mixedMoment B raw39223step0 raw39223step0Labels := by
      have ha : raw39223step0 = raw39223 := by apply Matrix.ext; unfold raw39223step0 raw39223; decide +kernel
      have hl : raw39223Labels = labelEmbedding2 ∘ raw39223step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39223 raw39223Labels raw39223step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw39224 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39224Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39224step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw39224step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39224step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39224 raw39224Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw39224 raw39224Labels = mixedMoment B raw39224step0 raw39224step0Labels := by
      have ha : raw39224step0 = (fun i j => raw39224 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39224step0 raw39224; decide +kernel
      have hl : raw39224step0Labels = raw39224Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39224 raw39224Labels permutation9 permutation7
    mixedMoment B raw39224step0 raw39224step0Labels = mixedMoment B raw39224step1 raw39224step1Labels := by
      have ha : raw39224step1 = -raw39224step0 := by apply Matrix.ext; change ∀ i j, raw39224step1 i j = -(raw39224step0 i j); unfold raw39224step1 raw39224step0; decide +kernel
      have hl : raw39224step1Labels = raw39224step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39224step1 raw39224step1Labels = mixedMoment B raw39224step2 raw39224step2Labels := by
      have ha : raw39224step2 = raw39224step1 := by apply Matrix.ext; unfold raw39224step2 raw39224step1; decide +kernel
      have hl : raw39224step1Labels = labelEmbedding4 ∘ raw39224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39224step1 raw39224step1Labels raw39224step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw39225 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39225Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39225 raw39225Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw39225 raw39225Labels = mixedMoment B raw39225step0 raw39225step0Labels := by
      have ha : raw39225step0 = (fun i j => raw39225 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39225step0 raw39225; decide +kernel
      have hl : raw39225step0Labels = raw39225Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39225 raw39225Labels permutation32 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw39226 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39226Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw39226step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39226step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39226step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39226 raw39226Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw39226 raw39226Labels = mixedMoment B raw39226step0 raw39226step0Labels := by
      have ha : raw39226step0 = (fun i j => raw39226 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39226step0 raw39226; decide +kernel
      have hl : raw39226step0Labels = raw39226Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39226 raw39226Labels permutation48 permutation7
    mixedMoment B raw39226step0 raw39226step0Labels = mixedMoment B raw39226step1 raw39226step1Labels := by
      have ha : raw39226step1 = -raw39226step0 := by apply Matrix.ext; change ∀ i j, raw39226step1 i j = -(raw39226step0 i j); unfold raw39226step1 raw39226step0; decide +kernel
      have hl : raw39226step1Labels = raw39226step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39226step1 raw39226step1Labels = mixedMoment B raw39226step2 raw39226step2Labels := by
      have ha : raw39226step2 = raw39226step1 := by apply Matrix.ext; unfold raw39226step2 raw39226step1; decide +kernel
      have hl : raw39226step1Labels = labelEmbedding1 ∘ raw39226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39226step1 raw39226step1Labels raw39226step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw39227 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39227Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39227 raw39227Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw39227 raw39227Labels = mixedMoment B raw39227step0 raw39227step0Labels := by
      have ha : raw39227step0 = raw39227 := by apply Matrix.ext; unfold raw39227step0 raw39227; decide +kernel
      have hl : raw39227Labels = labelEmbedding2 ∘ raw39227step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39227 raw39227Labels raw39227step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw39228 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39228Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39228step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39228step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39228 raw39228Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw39228 raw39228Labels = mixedMoment B raw39228step0 raw39228step0Labels := by
      have ha : raw39228step0 = (fun i j => raw39228 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39228step0 raw39228; decide +kernel
      have hl : raw39228step0Labels = raw39228Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39228 raw39228Labels permutation38 permutation7
    mixedMoment B raw39228step0 raw39228step0Labels = mixedMoment B raw39228step1 raw39228step1Labels := by
      have ha : raw39228step1 = -raw39228step0 := by apply Matrix.ext; change ∀ i j, raw39228step1 i j = -(raw39228step0 i j); unfold raw39228step1 raw39228step0; decide +kernel
      have hl : raw39228step1Labels = raw39228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39228step1 raw39228step1Labels = mixedMoment B raw39228step2 raw39228step2Labels := by
      have ha : raw39228step2 = raw39228step1 := by apply Matrix.ext; unfold raw39228step2 raw39228step1; decide +kernel
      have hl : raw39228step1Labels = labelEmbedding4 ∘ raw39228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39228step1 raw39228step1Labels raw39228step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw39229 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39229Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39229step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39229 raw39229Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw39229 raw39229Labels = mixedMoment B raw39229step0 raw39229step0Labels := by
      have ha : raw39229step0 = raw39229 := by apply Matrix.ext; unfold raw39229step0 raw39229; decide +kernel
      have hl : raw39229Labels = labelEmbedding2 ∘ raw39229step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39229 raw39229Labels raw39229step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw39230 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39230Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39230step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39230step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39230step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39230step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39230step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39230 raw39230Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw39230 raw39230Labels = mixedMoment B raw39230step0 raw39230step0Labels := by
      have ha : raw39230step0 = (fun i j => raw39230 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39230step0 raw39230; decide +kernel
      have hl : raw39230step0Labels = raw39230Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39230 raw39230Labels permutation10 permutation7
    mixedMoment B raw39230step0 raw39230step0Labels = mixedMoment B raw39230step1 raw39230step1Labels := by
      have ha : raw39230step1 = -raw39230step0 := by apply Matrix.ext; change ∀ i j, raw39230step1 i j = -(raw39230step0 i j); unfold raw39230step1 raw39230step0; decide +kernel
      have hl : raw39230step1Labels = raw39230step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39230step1 raw39230step1Labels = mixedMoment B raw39230step2 raw39230step2Labels := by
      have ha : raw39230step2 = raw39230step1 := by apply Matrix.ext; unfold raw39230step2 raw39230step1; decide +kernel
      have hl : raw39230step1Labels = labelEmbedding4 ∘ raw39230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39230step1 raw39230step1Labels raw39230step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw39231 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39231Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39231 raw39231Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw39231 raw39231Labels = mixedMoment B raw39231step0 raw39231step0Labels := by
      have ha : raw39231step0 = raw39231 := by apply Matrix.ext; unfold raw39231step0 raw39231; decide +kernel
      have hl : raw39231Labels = labelEmbedding2 ∘ raw39231step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39231 raw39231Labels raw39231step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw39232 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39232Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39232step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39232step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39232 raw39232Labels = mixedMoment B node3622 node3622Labels := by
  calc
    mixedMoment B raw39232 raw39232Labels = mixedMoment B raw39232step0 raw39232step0Labels := by
      have ha : raw39232step0 = (fun i j => raw39232 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39232step0 raw39232; decide +kernel
      have hl : raw39232step0Labels = raw39232Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39232 raw39232Labels permutation40 permutation7
    mixedMoment B raw39232step0 raw39232step0Labels = mixedMoment B raw39232step1 raw39232step1Labels := by
      have ha : raw39232step1 = -raw39232step0 := by apply Matrix.ext; change ∀ i j, raw39232step1 i j = -(raw39232step0 i j); unfold raw39232step1 raw39232step0; decide +kernel
      have hl : raw39232step1Labels = raw39232step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39232step1 raw39232step1Labels = mixedMoment B raw39232step2 raw39232step2Labels := by
      have ha : raw39232step2 = raw39232step1 := by apply Matrix.ext; unfold raw39232step2 raw39232step1; decide +kernel
      have hl : raw39232step1Labels = labelEmbedding4 ∘ raw39232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39232step1 raw39232step1Labels raw39232step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3622 node3622Labels := by rfl

def raw39233 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39233Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39233step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39233 raw39233Labels = mixedMoment B node2767 node2767Labels := by
  calc
    mixedMoment B raw39233 raw39233Labels = mixedMoment B raw39233step0 raw39233step0Labels := by
      have ha : raw39233step0 = raw39233 := by apply Matrix.ext; unfold raw39233step0 raw39233; decide +kernel
      have hl : raw39233Labels = labelEmbedding2 ∘ raw39233step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39233 raw39233Labels raw39233step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2767 node2767Labels := by rfl

def raw39234 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39234Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39234step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw39234step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw39234step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw39234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39234 raw39234Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw39234 raw39234Labels = mixedMoment B raw39234step0 raw39234step0Labels := by
      have ha : raw39234step0 = (fun i j => raw39234 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39234step0 raw39234; decide +kernel
      have hl : raw39234step0Labels = raw39234Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39234 raw39234Labels permutation10 permutation7
    mixedMoment B raw39234step0 raw39234step0Labels = mixedMoment B raw39234step1 raw39234step1Labels := by
      have ha : raw39234step1 = -raw39234step0 := by apply Matrix.ext; change ∀ i j, raw39234step1 i j = -(raw39234step0 i j); unfold raw39234step1 raw39234step0; decide +kernel
      have hl : raw39234step1Labels = raw39234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39234step1 raw39234step1Labels = mixedMoment B raw39234step2 raw39234step2Labels := by
      have ha : raw39234step2 = raw39234step1 := by apply Matrix.ext; unfold raw39234step2 raw39234step1; decide +kernel
      have hl : raw39234step1Labels = labelEmbedding4 ∘ raw39234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39234step1 raw39234step1Labels raw39234step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3627 node3627Labels := by rfl

def raw39235 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39235Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39235step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39235 raw39235Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw39235 raw39235Labels = mixedMoment B raw39235step0 raw39235step0Labels := by
      have ha : raw39235step0 = raw39235 := by apply Matrix.ext; unfold raw39235step0 raw39235; decide +kernel
      have hl : raw39235Labels = labelEmbedding2 ∘ raw39235step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39235 raw39235Labels raw39235step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw39236 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39236Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39236step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw39236step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw39236step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39236step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw39236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39236 raw39236Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw39236 raw39236Labels = mixedMoment B raw39236step0 raw39236step0Labels := by
      have ha : raw39236step0 = (fun i j => raw39236 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39236step0 raw39236; decide +kernel
      have hl : raw39236step0Labels = raw39236Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39236 raw39236Labels permutation12 permutation7
    mixedMoment B raw39236step0 raw39236step0Labels = mixedMoment B raw39236step1 raw39236step1Labels := by
      have ha : raw39236step1 = -raw39236step0 := by apply Matrix.ext; change ∀ i j, raw39236step1 i j = -(raw39236step0 i j); unfold raw39236step1 raw39236step0; decide +kernel
      have hl : raw39236step1Labels = raw39236step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39236step1 raw39236step1Labels = mixedMoment B raw39236step2 raw39236step2Labels := by
      have ha : raw39236step2 = raw39236step1 := by apply Matrix.ext; unfold raw39236step2 raw39236step1; decide +kernel
      have hl : raw39236step1Labels = labelEmbedding4 ∘ raw39236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39236step1 raw39236step1Labels raw39236step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3632 node3632Labels := by rfl

def raw39237 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw39237Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39237step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw39237step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39237 raw39237Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw39237 raw39237Labels = mixedMoment B raw39237step0 raw39237step0Labels := by
      have ha : raw39237step0 = raw39237 := by apply Matrix.ext; unfold raw39237step0 raw39237; decide +kernel
      have hl : raw39237Labels = labelEmbedding2 ∘ raw39237step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39237 raw39237Labels raw39237step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw39238 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw39238Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39238step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def raw39238step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39238step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![1, -1, 0], ![1, 2, -3]]
def raw39238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39238 raw39238Labels = mixedMoment B node3634 node3634Labels := by
  calc
    mixedMoment B raw39238 raw39238Labels = mixedMoment B raw39238step0 raw39238step0Labels := by
      have ha : raw39238step0 = (fun i j => raw39238 (permutation7 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39238step0 raw39238; decide +kernel
      have hl : raw39238step0Labels = raw39238Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39238 raw39238Labels permutation7 permutation5
    mixedMoment B raw39238step0 raw39238step0Labels = mixedMoment B raw39238step1 raw39238step1Labels := by
      have ha : raw39238step1 = raw39238step0 := by apply Matrix.ext; unfold raw39238step1 raw39238step0; decide +kernel
      have hl : raw39238step0Labels = labelEmbedding4 ∘ raw39238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39238step0 raw39238step0Labels raw39238step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3634 node3634Labels := by rfl

def raw39239 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39239 raw39239Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw39239 raw39239Labels = mixedMoment B raw39239step0 raw39239step0Labels := by
      have ha : raw39239step0 = (fun i j => raw39239 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39239step0 raw39239; decide +kernel
      have hl : raw39239step0Labels = raw39239Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39239 raw39239Labels permutation32 permutation3
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw39240 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39240Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw39240step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39240step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39240step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39240step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39240 raw39240Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw39240 raw39240Labels = mixedMoment B raw39240step0 raw39240step0Labels := by
      have ha : raw39240step0 = (fun i j => raw39240 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39240step0 raw39240; decide +kernel
      have hl : raw39240step0Labels = raw39240Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39240 raw39240Labels permutation41 permutation7
    mixedMoment B raw39240step0 raw39240step0Labels = mixedMoment B raw39240step1 raw39240step1Labels := by
      have ha : raw39240step1 = -raw39240step0 := by apply Matrix.ext; change ∀ i j, raw39240step1 i j = -(raw39240step0 i j); unfold raw39240step1 raw39240step0; decide +kernel
      have hl : raw39240step1Labels = raw39240step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39240step1 raw39240step1Labels = mixedMoment B raw39240step2 raw39240step2Labels := by
      have ha : raw39240step2 = raw39240step1 := by apply Matrix.ext; unfold raw39240step2 raw39240step1; decide +kernel
      have hl : raw39240step1Labels = labelEmbedding1 ∘ raw39240step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39240step1 raw39240step1Labels raw39240step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw39241 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39241step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw39241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39241 raw39241Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw39241 raw39241Labels = mixedMoment B raw39241step0 raw39241step0Labels := by
      have ha : raw39241step0 = (fun i j => raw39241 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39241step0 raw39241; decide +kernel
      have hl : raw39241step0Labels = raw39241Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39241 raw39241Labels permutation8 permutation3
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw39242 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39242Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39242step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw39242step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw39242step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw39242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39242 raw39242Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw39242 raw39242Labels = mixedMoment B raw39242step0 raw39242step0Labels := by
      have ha : raw39242step0 = (fun i j => raw39242 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39242step0 raw39242; decide +kernel
      have hl : raw39242step0Labels = raw39242Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39242 raw39242Labels permutation11 permutation7
    mixedMoment B raw39242step0 raw39242step0Labels = mixedMoment B raw39242step1 raw39242step1Labels := by
      have ha : raw39242step1 = -raw39242step0 := by apply Matrix.ext; change ∀ i j, raw39242step1 i j = -(raw39242step0 i j); unfold raw39242step1 raw39242step0; decide +kernel
      have hl : raw39242step1Labels = raw39242step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39242step1 raw39242step1Labels = mixedMoment B raw39242step2 raw39242step2Labels := by
      have ha : raw39242step2 = raw39242step1 := by apply Matrix.ext; unfold raw39242step2 raw39242step1; decide +kernel
      have hl : raw39242step1Labels = labelEmbedding1 ∘ raw39242step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39242step1 raw39242step1Labels raw39242step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw39243 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39243Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39243step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39243step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39243 raw39243Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw39243 raw39243Labels = mixedMoment B raw39243step0 raw39243step0Labels := by
      have ha : raw39243step0 = raw39243 := by apply Matrix.ext; unfold raw39243step0 raw39243; decide +kernel
      have hl : raw39243Labels = labelEmbedding2 ∘ raw39243step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39243 raw39243Labels raw39243step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw39244 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39244Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39244step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39244step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39244step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39244step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39244 raw39244Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw39244 raw39244Labels = mixedMoment B raw39244step0 raw39244step0Labels := by
      have ha : raw39244step0 = (fun i j => raw39244 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39244step0 raw39244; decide +kernel
      have hl : raw39244step0Labels = raw39244Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39244 raw39244Labels permutation8 permutation7
    mixedMoment B raw39244step0 raw39244step0Labels = mixedMoment B raw39244step1 raw39244step1Labels := by
      have ha : raw39244step1 = -raw39244step0 := by apply Matrix.ext; change ∀ i j, raw39244step1 i j = -(raw39244step0 i j); unfold raw39244step1 raw39244step0; decide +kernel
      have hl : raw39244step1Labels = raw39244step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39244step1 raw39244step1Labels = mixedMoment B raw39244step2 raw39244step2Labels := by
      have ha : raw39244step2 = raw39244step1 := by apply Matrix.ext; unfold raw39244step2 raw39244step1; decide +kernel
      have hl : raw39244step1Labels = labelEmbedding4 ∘ raw39244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39244step1 raw39244step1Labels raw39244step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw39245 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw39245Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39245step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw39245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39245 raw39245Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw39245 raw39245Labels = mixedMoment B raw39245step0 raw39245step0Labels := by
      have ha : raw39245step0 = raw39245 := by apply Matrix.ext; unfold raw39245step0 raw39245; decide +kernel
      have hl : raw39245Labels = labelEmbedding2 ∘ raw39245step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39245 raw39245Labels raw39245step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw39246 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw39246Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39246step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw39246step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39246step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw39246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39246 raw39246Labels = mixedMoment B node2783 node2783Labels := by
  calc
    mixedMoment B raw39246 raw39246Labels = mixedMoment B raw39246step0 raw39246step0Labels := by
      have ha : raw39246step0 = (fun i j => raw39246 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39246step0 raw39246; decide +kernel
      have hl : raw39246step0Labels = raw39246Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39246 raw39246Labels permutation7 permutation7
    mixedMoment B raw39246step0 raw39246step0Labels = mixedMoment B raw39246step1 raw39246step1Labels := by
      have ha : raw39246step1 = raw39246step0 := by apply Matrix.ext; unfold raw39246step1 raw39246step0; decide +kernel
      have hl : raw39246step0Labels = labelEmbedding4 ∘ raw39246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39246step0 raw39246step0Labels raw39246step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2783 node2783Labels := by rfl

def raw39247 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39247Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39247step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39247 raw39247Labels = mixedMoment B node2784 node2784Labels := by
  calc
    mixedMoment B raw39247 raw39247Labels = mixedMoment B raw39247step0 raw39247step0Labels := by
      have ha : raw39247step0 = raw39247 := by apply Matrix.ext; unfold raw39247step0 raw39247; decide +kernel
      have hl : raw39247Labels = labelEmbedding2 ∘ raw39247step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39247 raw39247Labels raw39247step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2784 node2784Labels := by rfl

def raw39248 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39248Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39248step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw39248step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw39248step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw39248step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39248 raw39248Labels = mixedMoment B node3623 node3623Labels := by
  calc
    mixedMoment B raw39248 raw39248Labels = mixedMoment B raw39248step0 raw39248step0Labels := by
      have ha : raw39248step0 = (fun i j => raw39248 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39248step0 raw39248; decide +kernel
      have hl : raw39248step0Labels = raw39248Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39248 raw39248Labels permutation8 permutation7
    mixedMoment B raw39248step0 raw39248step0Labels = mixedMoment B raw39248step1 raw39248step1Labels := by
      have ha : raw39248step1 = -raw39248step0 := by apply Matrix.ext; change ∀ i j, raw39248step1 i j = -(raw39248step0 i j); unfold raw39248step1 raw39248step0; decide +kernel
      have hl : raw39248step1Labels = raw39248step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39248step1 raw39248step1Labels = mixedMoment B raw39248step2 raw39248step2Labels := by
      have ha : raw39248step2 = raw39248step1 := by apply Matrix.ext; unfold raw39248step2 raw39248step1; decide +kernel
      have hl : raw39248step1Labels = labelEmbedding4 ∘ raw39248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39248step1 raw39248step1Labels raw39248step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3623 node3623Labels := by rfl

def raw39249 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39249Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39249step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39249 raw39249Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw39249 raw39249Labels = mixedMoment B raw39249step0 raw39249step0Labels := by
      have ha : raw39249step0 = raw39249 := by apply Matrix.ext; unfold raw39249step0 raw39249; decide +kernel
      have hl : raw39249Labels = labelEmbedding2 ∘ raw39249step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39249 raw39249Labels raw39249step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw39250 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39250Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39250step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-2, 1, 1]]
def raw39250step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39250step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw39250step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39250step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![2, -1, -1]]
def raw39250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39250 raw39250Labels = mixedMoment B node3633 node3633Labels := by
  calc
    mixedMoment B raw39250 raw39250Labels = mixedMoment B raw39250step0 raw39250step0Labels := by
      have ha : raw39250step0 = (fun i j => raw39250 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39250step0 raw39250; decide +kernel
      have hl : raw39250step0Labels = raw39250Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39250 raw39250Labels permutation3 permutation7
    mixedMoment B raw39250step0 raw39250step0Labels = mixedMoment B raw39250step1 raw39250step1Labels := by
      have ha : raw39250step1 = -raw39250step0 := by apply Matrix.ext; change ∀ i j, raw39250step1 i j = -(raw39250step0 i j); unfold raw39250step1 raw39250step0; decide +kernel
      have hl : raw39250step1Labels = raw39250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39250step1 raw39250step1Labels = mixedMoment B raw39250step2 raw39250step2Labels := by
      have ha : raw39250step2 = raw39250step1 := by apply Matrix.ext; unfold raw39250step2 raw39250step1; decide +kernel
      have hl : raw39250step1Labels = labelEmbedding4 ∘ raw39250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39250step1 raw39250step1Labels raw39250step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3633 node3633Labels := by rfl

def raw39251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39251Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39251 raw39251Labels = mixedMoment B node3638 node3638Labels := by
  calc
    mixedMoment B raw39251 raw39251Labels = mixedMoment B raw39251step0 raw39251step0Labels := by
      have ha : raw39251step0 = raw39251 := by apply Matrix.ext; unfold raw39251step0 raw39251; decide +kernel
      have hl : raw39251Labels = labelEmbedding2 ∘ raw39251step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39251 raw39251Labels raw39251step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3638 node3638Labels := by rfl

def raw39252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39252Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw39252step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw39252step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39252step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw39252step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39252 raw39252Labels = mixedMoment B node3643 node3643Labels := by
  calc
    mixedMoment B raw39252 raw39252Labels = mixedMoment B raw39252step0 raw39252step0Labels := by
      have ha : raw39252step0 = (fun i j => raw39252 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39252step0 raw39252; decide +kernel
      have hl : raw39252step0Labels = raw39252Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39252 raw39252Labels permutation154 permutation7
    mixedMoment B raw39252step0 raw39252step0Labels = mixedMoment B raw39252step1 raw39252step1Labels := by
      have ha : raw39252step1 = -raw39252step0 := by apply Matrix.ext; change ∀ i j, raw39252step1 i j = -(raw39252step0 i j); unfold raw39252step1 raw39252step0; decide +kernel
      have hl : raw39252step1Labels = raw39252step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39252step1 raw39252step1Labels = mixedMoment B raw39252step2 raw39252step2Labels := by
      have ha : raw39252step2 = raw39252step1 := by apply Matrix.ext; unfold raw39252step2 raw39252step1; decide +kernel
      have hl : raw39252step1Labels = labelEmbedding4 ∘ raw39252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39252step1 raw39252step1Labels raw39252step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3643 node3643Labels := by rfl

def raw39253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39253Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39253 raw39253Labels = mixedMoment B node3639 node3639Labels := by
  calc
    mixedMoment B raw39253 raw39253Labels = mixedMoment B raw39253step0 raw39253step0Labels := by
      have ha : raw39253step0 = raw39253 := by apply Matrix.ext; unfold raw39253step0 raw39253; decide +kernel
      have hl : raw39253Labels = labelEmbedding2 ∘ raw39253step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39253 raw39253Labels raw39253step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3639 node3639Labels := by rfl

def raw39254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39254Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw39254step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw39254step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39254step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw39254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39254 raw39254Labels = mixedMoment B node3645 node3645Labels := by
  calc
    mixedMoment B raw39254 raw39254Labels = mixedMoment B raw39254step0 raw39254step0Labels := by
      have ha : raw39254step0 = (fun i j => raw39254 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39254step0 raw39254; decide +kernel
      have hl : raw39254step0Labels = raw39254Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39254 raw39254Labels permutation155 permutation7
    mixedMoment B raw39254step0 raw39254step0Labels = mixedMoment B raw39254step1 raw39254step1Labels := by
      have ha : raw39254step1 = -raw39254step0 := by apply Matrix.ext; change ∀ i j, raw39254step1 i j = -(raw39254step0 i j); unfold raw39254step1 raw39254step0; decide +kernel
      have hl : raw39254step1Labels = raw39254step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39254step1 raw39254step1Labels = mixedMoment B raw39254step2 raw39254step2Labels := by
      have ha : raw39254step2 = raw39254step1 := by apply Matrix.ext; unfold raw39254step2 raw39254step1; decide +kernel
      have hl : raw39254step1Labels = labelEmbedding4 ∘ raw39254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39254step1 raw39254step1Labels raw39254step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3645 node3645Labels := by rfl

def raw39255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39255Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39255 raw39255Labels = mixedMoment B node3640 node3640Labels := by
  calc
    mixedMoment B raw39255 raw39255Labels = mixedMoment B raw39255step0 raw39255step0Labels := by
      have ha : raw39255step0 = raw39255 := by apply Matrix.ext; unfold raw39255step0 raw39255; decide +kernel
      have hl : raw39255Labels = labelEmbedding2 ∘ raw39255step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39255 raw39255Labels raw39255step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3640 node3640Labels := by rfl

def raw39256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39256Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw39256step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39256step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39256step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39256 raw39256Labels = mixedMoment B node3649 node3649Labels := by
  calc
    mixedMoment B raw39256 raw39256Labels = mixedMoment B raw39256step0 raw39256step0Labels := by
      have ha : raw39256step0 = (fun i j => raw39256 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39256step0 raw39256; decide +kernel
      have hl : raw39256step0Labels = raw39256Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39256 raw39256Labels permutation158 permutation7
    mixedMoment B raw39256step0 raw39256step0Labels = mixedMoment B raw39256step1 raw39256step1Labels := by
      have ha : raw39256step1 = -raw39256step0 := by apply Matrix.ext; change ∀ i j, raw39256step1 i j = -(raw39256step0 i j); unfold raw39256step1 raw39256step0; decide +kernel
      have hl : raw39256step1Labels = raw39256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39256step1 raw39256step1Labels = mixedMoment B raw39256step2 raw39256step2Labels := by
      have ha : raw39256step2 = raw39256step1 := by apply Matrix.ext; unfold raw39256step2 raw39256step1; decide +kernel
      have hl : raw39256step1Labels = labelEmbedding4 ∘ raw39256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39256step1 raw39256step1Labels raw39256step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3649 node3649Labels := by rfl

def raw39257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39257Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39257 raw39257Labels = mixedMoment B node3641 node3641Labels := by
  calc
    mixedMoment B raw39257 raw39257Labels = mixedMoment B raw39257step0 raw39257step0Labels := by
      have ha : raw39257step0 = raw39257 := by apply Matrix.ext; unfold raw39257step0 raw39257; decide +kernel
      have hl : raw39257Labels = labelEmbedding2 ∘ raw39257step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39257 raw39257Labels raw39257step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3641 node3641Labels := by rfl

def raw39258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39258Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw39258step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39258step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39258 raw39258Labels = mixedMoment B node3655 node3655Labels := by
  calc
    mixedMoment B raw39258 raw39258Labels = mixedMoment B raw39258step0 raw39258step0Labels := by
      have ha : raw39258step0 = (fun i j => raw39258 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39258step0 raw39258; decide +kernel
      have hl : raw39258step0Labels = raw39258Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39258 raw39258Labels permutation164 permutation7
    mixedMoment B raw39258step0 raw39258step0Labels = mixedMoment B raw39258step1 raw39258step1Labels := by
      have ha : raw39258step1 = -raw39258step0 := by apply Matrix.ext; change ∀ i j, raw39258step1 i j = -(raw39258step0 i j); unfold raw39258step1 raw39258step0; decide +kernel
      have hl : raw39258step1Labels = raw39258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39258step1 raw39258step1Labels = mixedMoment B raw39258step2 raw39258step2Labels := by
      have ha : raw39258step2 = raw39258step1 := by apply Matrix.ext; unfold raw39258step2 raw39258step1; decide +kernel
      have hl : raw39258step1Labels = labelEmbedding4 ∘ raw39258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39258step1 raw39258step1Labels raw39258step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3655 node3655Labels := by rfl

def raw39259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39259Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39259 raw39259Labels = mixedMoment B node3642 node3642Labels := by
  calc
    mixedMoment B raw39259 raw39259Labels = mixedMoment B raw39259step0 raw39259step0Labels := by
      have ha : raw39259step0 = raw39259 := by apply Matrix.ext; unfold raw39259step0 raw39259; decide +kernel
      have hl : raw39259Labels = labelEmbedding2 ∘ raw39259step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39259 raw39259Labels raw39259step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3642 node3642Labels := by rfl

def raw39260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39260Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw39260step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw39260step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39260step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw39260step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39260 raw39260Labels = mixedMoment B node3662 node3662Labels := by
  calc
    mixedMoment B raw39260 raw39260Labels = mixedMoment B raw39260step0 raw39260step0Labels := by
      have ha : raw39260step0 = (fun i j => raw39260 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39260step0 raw39260; decide +kernel
      have hl : raw39260step0Labels = raw39260Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39260 raw39260Labels permutation152 permutation7
    mixedMoment B raw39260step0 raw39260step0Labels = mixedMoment B raw39260step1 raw39260step1Labels := by
      have ha : raw39260step1 = -raw39260step0 := by apply Matrix.ext; change ∀ i j, raw39260step1 i j = -(raw39260step0 i j); unfold raw39260step1 raw39260step0; decide +kernel
      have hl : raw39260step1Labels = raw39260step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39260step1 raw39260step1Labels = mixedMoment B raw39260step2 raw39260step2Labels := by
      have ha : raw39260step2 = raw39260step1 := by apply Matrix.ext; unfold raw39260step2 raw39260step1; decide +kernel
      have hl : raw39260step1Labels = labelEmbedding4 ∘ raw39260step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39260step1 raw39260step1Labels raw39260step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3662 node3662Labels := by rfl

def raw39261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39261Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39261 raw39261Labels = mixedMoment B node3646 node3646Labels := by
  calc
    mixedMoment B raw39261 raw39261Labels = mixedMoment B raw39261step0 raw39261step0Labels := by
      have ha : raw39261step0 = raw39261 := by apply Matrix.ext; unfold raw39261step0 raw39261; decide +kernel
      have hl : raw39261Labels = labelEmbedding2 ∘ raw39261step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39261 raw39261Labels raw39261step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3646 node3646Labels := by rfl

def raw39262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39262Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw39262step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39262step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39262step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39262 raw39262Labels = mixedMoment B node3656 node3656Labels := by
  calc
    mixedMoment B raw39262 raw39262Labels = mixedMoment B raw39262step0 raw39262step0Labels := by
      have ha : raw39262step0 = (fun i j => raw39262 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39262step0 raw39262; decide +kernel
      have hl : raw39262step0Labels = raw39262Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39262 raw39262Labels permutation164 permutation7
    mixedMoment B raw39262step0 raw39262step0Labels = mixedMoment B raw39262step1 raw39262step1Labels := by
      have ha : raw39262step1 = -raw39262step0 := by apply Matrix.ext; change ∀ i j, raw39262step1 i j = -(raw39262step0 i j); unfold raw39262step1 raw39262step0; decide +kernel
      have hl : raw39262step1Labels = raw39262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39262step1 raw39262step1Labels = mixedMoment B raw39262step2 raw39262step2Labels := by
      have ha : raw39262step2 = raw39262step1 := by apply Matrix.ext; unfold raw39262step2 raw39262step1; decide +kernel
      have hl : raw39262step1Labels = labelEmbedding4 ∘ raw39262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39262step1 raw39262step1Labels raw39262step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3656 node3656Labels := by rfl

def raw39263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39263Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39263 raw39263Labels = mixedMoment B node3647 node3647Labels := by
  calc
    mixedMoment B raw39263 raw39263Labels = mixedMoment B raw39263step0 raw39263step0Labels := by
      have ha : raw39263step0 = raw39263 := by apply Matrix.ext; unfold raw39263step0 raw39263; decide +kernel
      have hl : raw39263Labels = labelEmbedding2 ∘ raw39263step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39263 raw39263Labels raw39263step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3647 node3647Labels := by rfl

def raw39264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39264Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw39264step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw39264step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw39264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39264 raw39264Labels = mixedMoment B node3663 node3663Labels := by
  calc
    mixedMoment B raw39264 raw39264Labels = mixedMoment B raw39264step0 raw39264step0Labels := by
      have ha : raw39264step0 = (fun i j => raw39264 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39264step0 raw39264; decide +kernel
      have hl : raw39264step0Labels = raw39264Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39264 raw39264Labels permutation152 permutation7
    mixedMoment B raw39264step0 raw39264step0Labels = mixedMoment B raw39264step1 raw39264step1Labels := by
      have ha : raw39264step1 = -raw39264step0 := by apply Matrix.ext; change ∀ i j, raw39264step1 i j = -(raw39264step0 i j); unfold raw39264step1 raw39264step0; decide +kernel
      have hl : raw39264step1Labels = raw39264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39264step1 raw39264step1Labels = mixedMoment B raw39264step2 raw39264step2Labels := by
      have ha : raw39264step2 = raw39264step1 := by apply Matrix.ext; unfold raw39264step2 raw39264step1; decide +kernel
      have hl : raw39264step1Labels = labelEmbedding4 ∘ raw39264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39264step1 raw39264step1Labels raw39264step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3663 node3663Labels := by rfl

def raw39265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39265Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39265 raw39265Labels = mixedMoment B node3651 node3651Labels := by
  calc
    mixedMoment B raw39265 raw39265Labels = mixedMoment B raw39265step0 raw39265step0Labels := by
      have ha : raw39265step0 = raw39265 := by apply Matrix.ext; unfold raw39265step0 raw39265; decide +kernel
      have hl : raw39265Labels = labelEmbedding2 ∘ raw39265step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39265 raw39265Labels raw39265step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3651 node3651Labels := by rfl

def raw39266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39266Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw39266step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39266step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39266step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39266 raw39266Labels = mixedMoment B node3651 node3651Labels := by
  calc
    mixedMoment B raw39266 raw39266Labels = mixedMoment B raw39266step0 raw39266step0Labels := by
      have ha : raw39266step0 = (fun i j => raw39266 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39266step0 raw39266; decide +kernel
      have hl : raw39266step0Labels = raw39266Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39266 raw39266Labels permutation159 permutation7
    mixedMoment B raw39266step0 raw39266step0Labels = mixedMoment B raw39266step1 raw39266step1Labels := by
      have ha : raw39266step1 = -raw39266step0 := by apply Matrix.ext; change ∀ i j, raw39266step1 i j = -(raw39266step0 i j); unfold raw39266step1 raw39266step0; decide +kernel
      have hl : raw39266step1Labels = raw39266step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39266step1 raw39266step1Labels = mixedMoment B raw39266step2 raw39266step2Labels := by
      have ha : raw39266step2 = raw39266step1 := by apply Matrix.ext; unfold raw39266step2 raw39266step1; decide +kernel
      have hl : raw39266step1Labels = labelEmbedding4 ∘ raw39266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39266step1 raw39266step1Labels raw39266step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3651 node3651Labels := by rfl

def raw39267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39267Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39267 raw39267Labels = mixedMoment B node3653 node3653Labels := by
  calc
    mixedMoment B raw39267 raw39267Labels = mixedMoment B raw39267step0 raw39267step0Labels := by
      have ha : raw39267step0 = raw39267 := by apply Matrix.ext; unfold raw39267step0 raw39267; decide +kernel
      have hl : raw39267Labels = labelEmbedding2 ∘ raw39267step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39267 raw39267Labels raw39267step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3653 node3653Labels := by rfl

def raw39268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39268Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw39268step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39268step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39268step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39268 raw39268Labels = mixedMoment B node3657 node3657Labels := by
  calc
    mixedMoment B raw39268 raw39268Labels = mixedMoment B raw39268step0 raw39268step0Labels := by
      have ha : raw39268step0 = (fun i j => raw39268 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39268step0 raw39268; decide +kernel
      have hl : raw39268step0Labels = raw39268Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39268 raw39268Labels permutation170 permutation7
    mixedMoment B raw39268step0 raw39268step0Labels = mixedMoment B raw39268step1 raw39268step1Labels := by
      have ha : raw39268step1 = -raw39268step0 := by apply Matrix.ext; change ∀ i j, raw39268step1 i j = -(raw39268step0 i j); unfold raw39268step1 raw39268step0; decide +kernel
      have hl : raw39268step1Labels = raw39268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39268step1 raw39268step1Labels = mixedMoment B raw39268step2 raw39268step2Labels := by
      have ha : raw39268step2 = raw39268step1 := by apply Matrix.ext; unfold raw39268step2 raw39268step1; decide +kernel
      have hl : raw39268step1Labels = labelEmbedding4 ∘ raw39268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39268step1 raw39268step1Labels raw39268step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3657 node3657Labels := by rfl

def raw39269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39269Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39269 raw39269Labels = mixedMoment B node3659 node3659Labels := by
  calc
    mixedMoment B raw39269 raw39269Labels = mixedMoment B raw39269step0 raw39269step0Labels := by
      have ha : raw39269step0 = raw39269 := by apply Matrix.ext; unfold raw39269step0 raw39269; decide +kernel
      have hl : raw39269Labels = labelEmbedding2 ∘ raw39269step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39269 raw39269Labels raw39269step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3659 node3659Labels := by rfl

def raw39270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39270Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39270step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39270step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39270step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39270 raw39270Labels = mixedMoment B node3659 node3659Labels := by
  calc
    mixedMoment B raw39270 raw39270Labels = mixedMoment B raw39270step0 raw39270step0Labels := by
      have ha : raw39270step0 = (fun i j => raw39270 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39270step0 raw39270; decide +kernel
      have hl : raw39270step0Labels = raw39270Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39270 raw39270Labels permutation173 permutation7
    mixedMoment B raw39270step0 raw39270step0Labels = mixedMoment B raw39270step1 raw39270step1Labels := by
      have ha : raw39270step1 = -raw39270step0 := by apply Matrix.ext; change ∀ i j, raw39270step1 i j = -(raw39270step0 i j); unfold raw39270step1 raw39270step0; decide +kernel
      have hl : raw39270step1Labels = raw39270step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39270step1 raw39270step1Labels = mixedMoment B raw39270step2 raw39270step2Labels := by
      have ha : raw39270step2 = raw39270step1 := by apply Matrix.ext; unfold raw39270step2 raw39270step1; decide +kernel
      have hl : raw39270step1Labels = labelEmbedding4 ∘ raw39270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39270step1 raw39270step1Labels raw39270step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3659 node3659Labels := by rfl

def raw39271 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39271Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39271 raw39271Labels = mixedMoment B node3660 node3660Labels := by
  calc
    mixedMoment B raw39271 raw39271Labels = mixedMoment B raw39271step0 raw39271step0Labels := by
      have ha : raw39271step0 = raw39271 := by apply Matrix.ext; unfold raw39271step0 raw39271; decide +kernel
      have hl : raw39271Labels = labelEmbedding2 ∘ raw39271step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39271 raw39271Labels raw39271step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3660 node3660Labels := by rfl

def raw39272 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39272Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw39272step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39272step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39272 raw39272Labels = mixedMoment B node3660 node3660Labels := by
  calc
    mixedMoment B raw39272 raw39272Labels = mixedMoment B raw39272step0 raw39272step0Labels := by
      have ha : raw39272step0 = (fun i j => raw39272 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39272step0 raw39272; decide +kernel
      have hl : raw39272step0Labels = raw39272Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39272 raw39272Labels permutation34 permutation7
    mixedMoment B raw39272step0 raw39272step0Labels = mixedMoment B raw39272step1 raw39272step1Labels := by
      have ha : raw39272step1 = -raw39272step0 := by apply Matrix.ext; change ∀ i j, raw39272step1 i j = -(raw39272step0 i j); unfold raw39272step1 raw39272step0; decide +kernel
      have hl : raw39272step1Labels = raw39272step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39272step1 raw39272step1Labels = mixedMoment B raw39272step2 raw39272step2Labels := by
      have ha : raw39272step2 = raw39272step1 := by apply Matrix.ext; unfold raw39272step2 raw39272step1; decide +kernel
      have hl : raw39272step1Labels = labelEmbedding4 ∘ raw39272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39272step1 raw39272step1Labels raw39272step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3660 node3660Labels := by rfl

def raw39273 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39273Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39273step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39273 raw39273Labels = mixedMoment B node3661 node3661Labels := by
  calc
    mixedMoment B raw39273 raw39273Labels = mixedMoment B raw39273step0 raw39273step0Labels := by
      have ha : raw39273step0 = raw39273 := by apply Matrix.ext; unfold raw39273step0 raw39273; decide +kernel
      have hl : raw39273Labels = labelEmbedding2 ∘ raw39273step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39273 raw39273Labels raw39273step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3661 node3661Labels := by rfl

def raw39274 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39274Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw39274step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39274step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39274 raw39274Labels = mixedMoment B node3666 node3666Labels := by
  calc
    mixedMoment B raw39274 raw39274Labels = mixedMoment B raw39274step0 raw39274step0Labels := by
      have ha : raw39274step0 = (fun i j => raw39274 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39274step0 raw39274; decide +kernel
      have hl : raw39274step0Labels = raw39274Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39274 raw39274Labels permutation35 permutation7
    mixedMoment B raw39274step0 raw39274step0Labels = mixedMoment B raw39274step1 raw39274step1Labels := by
      have ha : raw39274step1 = -raw39274step0 := by apply Matrix.ext; change ∀ i j, raw39274step1 i j = -(raw39274step0 i j); unfold raw39274step1 raw39274step0; decide +kernel
      have hl : raw39274step1Labels = raw39274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39274step1 raw39274step1Labels = mixedMoment B raw39274step2 raw39274step2Labels := by
      have ha : raw39274step2 = raw39274step1 := by apply Matrix.ext; unfold raw39274step2 raw39274step1; decide +kernel
      have hl : raw39274step1Labels = labelEmbedding4 ∘ raw39274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39274step1 raw39274step1Labels raw39274step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3666 node3666Labels := by rfl

def raw39275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39275Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39275 raw39275Labels = mixedMoment B node3668 node3668Labels := by
  calc
    mixedMoment B raw39275 raw39275Labels = mixedMoment B raw39275step0 raw39275step0Labels := by
      have ha : raw39275step0 = raw39275 := by apply Matrix.ext; unfold raw39275step0 raw39275; decide +kernel
      have hl : raw39275Labels = labelEmbedding2 ∘ raw39275step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39275 raw39275Labels raw39275step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3668 node3668Labels := by rfl

def raw39276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39276Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39276step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39276 raw39276Labels = mixedMoment B node3677 node3677Labels := by
  calc
    mixedMoment B raw39276 raw39276Labels = mixedMoment B raw39276step0 raw39276step0Labels := by
      have ha : raw39276step0 = (fun i j => raw39276 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39276step0 raw39276; decide +kernel
      have hl : raw39276step0Labels = raw39276Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39276 raw39276Labels permutation664 permutation7
    mixedMoment B raw39276step0 raw39276step0Labels = mixedMoment B raw39276step1 raw39276step1Labels := by
      have ha : raw39276step1 = raw39276step0 := by apply Matrix.ext; unfold raw39276step1 raw39276step0; decide +kernel
      have hl : raw39276step0Labels = labelEmbedding4 ∘ raw39276step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39276step0 raw39276step0Labels raw39276step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3677 node3677Labels := by rfl

def raw39277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39277Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39277 raw39277Labels = mixedMoment B node3669 node3669Labels := by
  calc
    mixedMoment B raw39277 raw39277Labels = mixedMoment B raw39277step0 raw39277step0Labels := by
      have ha : raw39277step0 = raw39277 := by apply Matrix.ext; unfold raw39277step0 raw39277; decide +kernel
      have hl : raw39277Labels = labelEmbedding2 ∘ raw39277step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39277 raw39277Labels raw39277step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3669 node3669Labels := by rfl

def raw39278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39278Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw39278step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw39278step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39278step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw39278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39278 raw39278Labels = mixedMoment B node3742 node3742Labels := by
  calc
    mixedMoment B raw39278 raw39278Labels = mixedMoment B raw39278step0 raw39278step0Labels := by
      have ha : raw39278step0 = (fun i j => raw39278 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39278step0 raw39278; decide +kernel
      have hl : raw39278step0Labels = raw39278Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39278 raw39278Labels permutation155 permutation7
    mixedMoment B raw39278step0 raw39278step0Labels = mixedMoment B raw39278step1 raw39278step1Labels := by
      have ha : raw39278step1 = -raw39278step0 := by apply Matrix.ext; change ∀ i j, raw39278step1 i j = -(raw39278step0 i j); unfold raw39278step1 raw39278step0; decide +kernel
      have hl : raw39278step1Labels = raw39278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39278step1 raw39278step1Labels = mixedMoment B raw39278step2 raw39278step2Labels := by
      have ha : raw39278step2 = raw39278step1 := by apply Matrix.ext; unfold raw39278step2 raw39278step1; decide +kernel
      have hl : raw39278step1Labels = labelEmbedding4 ∘ raw39278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39278step1 raw39278step1Labels raw39278step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3742 node3742Labels := by rfl

def raw39279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39279Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39279 raw39279Labels = mixedMoment B node3670 node3670Labels := by
  calc
    mixedMoment B raw39279 raw39279Labels = mixedMoment B raw39279step0 raw39279step0Labels := by
      have ha : raw39279step0 = raw39279 := by apply Matrix.ext; unfold raw39279step0 raw39279; decide +kernel
      have hl : raw39279Labels = labelEmbedding2 ∘ raw39279step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39279 raw39279Labels raw39279step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3670 node3670Labels := by rfl

def raw39280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39280Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39280step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39280 raw39280Labels = mixedMoment B node3753 node3753Labels := by
  calc
    mixedMoment B raw39280 raw39280Labels = mixedMoment B raw39280step0 raw39280step0Labels := by
      have ha : raw39280step0 = (fun i j => raw39280 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39280step0 raw39280; decide +kernel
      have hl : raw39280step0Labels = raw39280Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39280 raw39280Labels permutation688 permutation7
    mixedMoment B raw39280step0 raw39280step0Labels = mixedMoment B raw39280step1 raw39280step1Labels := by
      have ha : raw39280step1 = raw39280step0 := by apply Matrix.ext; unfold raw39280step1 raw39280step0; decide +kernel
      have hl : raw39280step0Labels = labelEmbedding4 ∘ raw39280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39280step0 raw39280step0Labels raw39280step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3753 node3753Labels := by rfl

def raw39281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39281Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39281 raw39281Labels = mixedMoment B node3671 node3671Labels := by
  calc
    mixedMoment B raw39281 raw39281Labels = mixedMoment B raw39281step0 raw39281step0Labels := by
      have ha : raw39281step0 = raw39281 := by apply Matrix.ext; unfold raw39281step0 raw39281; decide +kernel
      have hl : raw39281Labels = labelEmbedding2 ∘ raw39281step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39281 raw39281Labels raw39281step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3671 node3671Labels := by rfl

def raw39282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39282Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw39282step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw39282step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39282step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw39282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39282 raw39282Labels = mixedMoment B node3754 node3754Labels := by
  calc
    mixedMoment B raw39282 raw39282Labels = mixedMoment B raw39282step0 raw39282step0Labels := by
      have ha : raw39282step0 = (fun i j => raw39282 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39282step0 raw39282; decide +kernel
      have hl : raw39282step0Labels = raw39282Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39282 raw39282Labels permutation154 permutation7
    mixedMoment B raw39282step0 raw39282step0Labels = mixedMoment B raw39282step1 raw39282step1Labels := by
      have ha : raw39282step1 = -raw39282step0 := by apply Matrix.ext; change ∀ i j, raw39282step1 i j = -(raw39282step0 i j); unfold raw39282step1 raw39282step0; decide +kernel
      have hl : raw39282step1Labels = raw39282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39282step1 raw39282step1Labels = mixedMoment B raw39282step2 raw39282step2Labels := by
      have ha : raw39282step2 = raw39282step1 := by apply Matrix.ext; unfold raw39282step2 raw39282step1; decide +kernel
      have hl : raw39282step1Labels = labelEmbedding4 ∘ raw39282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39282step1 raw39282step1Labels raw39282step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3754 node3754Labels := by rfl

def raw39283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39283Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39283step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39283 raw39283Labels = mixedMoment B node3672 node3672Labels := by
  calc
    mixedMoment B raw39283 raw39283Labels = mixedMoment B raw39283step0 raw39283step0Labels := by
      have ha : raw39283step0 = raw39283 := by apply Matrix.ext; unfold raw39283step0 raw39283; decide +kernel
      have hl : raw39283Labels = labelEmbedding2 ∘ raw39283step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39283 raw39283Labels raw39283step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3672 node3672Labels := by rfl

def raw39284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39284Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw39284step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw39284step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw39284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39284 raw39284Labels = mixedMoment B node3756 node3756Labels := by
  calc
    mixedMoment B raw39284 raw39284Labels = mixedMoment B raw39284step0 raw39284step0Labels := by
      have ha : raw39284step0 = (fun i j => raw39284 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39284step0 raw39284; decide +kernel
      have hl : raw39284step0Labels = raw39284Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39284 raw39284Labels permutation152 permutation7
    mixedMoment B raw39284step0 raw39284step0Labels = mixedMoment B raw39284step1 raw39284step1Labels := by
      have ha : raw39284step1 = -raw39284step0 := by apply Matrix.ext; change ∀ i j, raw39284step1 i j = -(raw39284step0 i j); unfold raw39284step1 raw39284step0; decide +kernel
      have hl : raw39284step1Labels = raw39284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39284step1 raw39284step1Labels = mixedMoment B raw39284step2 raw39284step2Labels := by
      have ha : raw39284step2 = raw39284step1 := by apply Matrix.ext; unfold raw39284step2 raw39284step1; decide +kernel
      have hl : raw39284step1Labels = labelEmbedding4 ∘ raw39284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39284step1 raw39284step1Labels raw39284step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3756 node3756Labels := by rfl

def raw39285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39285Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39285step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39285 raw39285Labels = mixedMoment B node3678 node3678Labels := by
  calc
    mixedMoment B raw39285 raw39285Labels = mixedMoment B raw39285step0 raw39285step0Labels := by
      have ha : raw39285step0 = raw39285 := by apply Matrix.ext; unfold raw39285step0 raw39285; decide +kernel
      have hl : raw39285Labels = labelEmbedding2 ∘ raw39285step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39285 raw39285Labels raw39285step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3678 node3678Labels := by rfl

def raw39286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39286Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39286step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39286 raw39286Labels = mixedMoment B node3744 node3744Labels := by
  calc
    mixedMoment B raw39286 raw39286Labels = mixedMoment B raw39286step0 raw39286step0Labels := by
      have ha : raw39286step0 = (fun i j => raw39286 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39286step0 raw39286; decide +kernel
      have hl : raw39286step0Labels = raw39286Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39286 raw39286Labels permutation688 permutation7
    mixedMoment B raw39286step0 raw39286step0Labels = mixedMoment B raw39286step1 raw39286step1Labels := by
      have ha : raw39286step1 = raw39286step0 := by apply Matrix.ext; unfold raw39286step1 raw39286step0; decide +kernel
      have hl : raw39286step0Labels = labelEmbedding4 ∘ raw39286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39286step0 raw39286step0Labels raw39286step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3744 node3744Labels := by rfl

def raw39287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39287Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39287 raw39287Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw39287 raw39287Labels = mixedMoment B raw39287step0 raw39287step0Labels := by
      have ha : raw39287step0 = raw39287 := by apply Matrix.ext; unfold raw39287step0 raw39287; decide +kernel
      have hl : raw39287Labels = labelEmbedding2 ∘ raw39287step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39287 raw39287Labels raw39287step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3681 node3681Labels := by rfl

def raw39288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39288Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39288step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39288 raw39288Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw39288 raw39288Labels = mixedMoment B raw39288step0 raw39288step0Labels := by
      have ha : raw39288step0 = (fun i j => raw39288 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39288step0 raw39288; decide +kernel
      have hl : raw39288step0Labels = raw39288Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39288 raw39288Labels permutation688 permutation7
    mixedMoment B raw39288step0 raw39288step0Labels = mixedMoment B raw39288step1 raw39288step1Labels := by
      have ha : raw39288step1 = raw39288step0 := by apply Matrix.ext; unfold raw39288step1 raw39288step0; decide +kernel
      have hl : raw39288step0Labels = labelEmbedding4 ∘ raw39288step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39288step0 raw39288step0Labels raw39288step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3681 node3681Labels := by rfl

def raw39289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39289Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39289step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39289 raw39289Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw39289 raw39289Labels = mixedMoment B raw39289step0 raw39289step0Labels := by
      have ha : raw39289step0 = raw39289 := by apply Matrix.ext; unfold raw39289step0 raw39289; decide +kernel
      have hl : raw39289Labels = labelEmbedding2 ∘ raw39289step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39289 raw39289Labels raw39289step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3683 node3683Labels := by rfl

def raw39290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39290Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39290step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39290step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39290 raw39290Labels = mixedMoment B node3746 node3746Labels := by
  calc
    mixedMoment B raw39290 raw39290Labels = mixedMoment B raw39290step0 raw39290step0Labels := by
      have ha : raw39290step0 = (fun i j => raw39290 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39290step0 raw39290; decide +kernel
      have hl : raw39290step0Labels = raw39290Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39290 raw39290Labels permutation153 permutation7
    mixedMoment B raw39290step0 raw39290step0Labels = mixedMoment B raw39290step1 raw39290step1Labels := by
      have ha : raw39290step1 = -raw39290step0 := by apply Matrix.ext; change ∀ i j, raw39290step1 i j = -(raw39290step0 i j); unfold raw39290step1 raw39290step0; decide +kernel
      have hl : raw39290step1Labels = raw39290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39290step1 raw39290step1Labels = mixedMoment B raw39290step2 raw39290step2Labels := by
      have ha : raw39290step2 = raw39290step1 := by apply Matrix.ext; unfold raw39290step2 raw39290step1; decide +kernel
      have hl : raw39290step1Labels = labelEmbedding4 ∘ raw39290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39290step1 raw39290step1Labels raw39290step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3746 node3746Labels := by rfl

def raw39291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39291Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39291 raw39291Labels = mixedMoment B node3687 node3687Labels := by
  calc
    mixedMoment B raw39291 raw39291Labels = mixedMoment B raw39291step0 raw39291step0Labels := by
      have ha : raw39291step0 = raw39291 := by apply Matrix.ext; unfold raw39291step0 raw39291; decide +kernel
      have hl : raw39291Labels = labelEmbedding2 ∘ raw39291step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39291 raw39291Labels raw39291step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3687 node3687Labels := by rfl

def raw39292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39292Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw39292step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39292step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39292step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39292 raw39292Labels = mixedMoment B node3749 node3749Labels := by
  calc
    mixedMoment B raw39292 raw39292Labels = mixedMoment B raw39292step0 raw39292step0Labels := by
      have ha : raw39292step0 = (fun i j => raw39292 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39292step0 raw39292; decide +kernel
      have hl : raw39292step0Labels = raw39292Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39292 raw39292Labels permutation158 permutation7
    mixedMoment B raw39292step0 raw39292step0Labels = mixedMoment B raw39292step1 raw39292step1Labels := by
      have ha : raw39292step1 = -raw39292step0 := by apply Matrix.ext; change ∀ i j, raw39292step1 i j = -(raw39292step0 i j); unfold raw39292step1 raw39292step0; decide +kernel
      have hl : raw39292step1Labels = raw39292step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39292step1 raw39292step1Labels = mixedMoment B raw39292step2 raw39292step2Labels := by
      have ha : raw39292step2 = raw39292step1 := by apply Matrix.ext; unfold raw39292step2 raw39292step1; decide +kernel
      have hl : raw39292step1Labels = labelEmbedding4 ∘ raw39292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39292step1 raw39292step1Labels raw39292step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3749 node3749Labels := by rfl

def raw39293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39293Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39293step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39293 raw39293Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw39293 raw39293Labels = mixedMoment B raw39293step0 raw39293step0Labels := by
      have ha : raw39293step0 = raw39293 := by apply Matrix.ext; unfold raw39293step0 raw39293; decide +kernel
      have hl : raw39293Labels = labelEmbedding2 ∘ raw39293step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39293 raw39293Labels raw39293step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3689 node3689Labels := by rfl

def raw39294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39294Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39294step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39294step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39294step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39294 raw39294Labels = mixedMoment B node3757 node3757Labels := by
  calc
    mixedMoment B raw39294 raw39294Labels = mixedMoment B raw39294step0 raw39294step0Labels := by
      have ha : raw39294step0 = (fun i j => raw39294 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39294step0 raw39294; decide +kernel
      have hl : raw39294step0Labels = raw39294Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39294 raw39294Labels permutation160 permutation7
    mixedMoment B raw39294step0 raw39294step0Labels = mixedMoment B raw39294step1 raw39294step1Labels := by
      have ha : raw39294step1 = -raw39294step0 := by apply Matrix.ext; change ∀ i j, raw39294step1 i j = -(raw39294step0 i j); unfold raw39294step1 raw39294step0; decide +kernel
      have hl : raw39294step1Labels = raw39294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39294step1 raw39294step1Labels = mixedMoment B raw39294step2 raw39294step2Labels := by
      have ha : raw39294step2 = raw39294step1 := by apply Matrix.ext; unfold raw39294step2 raw39294step1; decide +kernel
      have hl : raw39294step1Labels = labelEmbedding4 ∘ raw39294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39294step1 raw39294step1Labels raw39294step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3757 node3757Labels := by rfl

def raw39295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39295Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39295 raw39295Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw39295 raw39295Labels = mixedMoment B raw39295step0 raw39295step0Labels := by
      have ha : raw39295step0 = raw39295 := by apply Matrix.ext; unfold raw39295step0 raw39295; decide +kernel
      have hl : raw39295Labels = labelEmbedding2 ∘ raw39295step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39295 raw39295Labels raw39295step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3690 node3690Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
