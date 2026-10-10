import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15616 raw15616Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw15616 raw15616Labels = mixedMoment B raw15616step0 raw15616step0Labels := by
      have ha : raw15616step0 = (fun i j => raw15616 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15616step0 raw15616; decide +kernel
      have hl : raw15616step0Labels = raw15616Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15616 raw15616Labels permutation227 permutation5
    mixedMoment B raw15616step0 raw15616step0Labels = mixedMoment B raw15616step1 raw15616step1Labels := by
      have ha : raw15616step1 = -raw15616step0 := by apply Matrix.ext; change ∀ i j, raw15616step1 i j = -(raw15616step0 i j); unfold raw15616step1 raw15616step0; decide +kernel
      have hl : raw15616step1Labels = raw15616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15616step1 raw15616step1Labels = mixedMoment B raw15616step2 raw15616step2Labels := by
      have ha : raw15616step2 = raw15616step1 := by apply Matrix.ext; unfold raw15616step2 raw15616step1; decide +kernel
      have hl : raw15616step1Labels = labelEmbedding1 ∘ raw15616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15616step1 raw15616step1Labels raw15616step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3720 node3720Labels := by rfl

def raw15617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15617step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15617step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15617 raw15617Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw15617 raw15617Labels = mixedMoment B raw15617step0 raw15617step0Labels := by
      have ha : raw15617step0 = (fun i j => raw15617 (permutation229 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15617step0 raw15617; decide +kernel
      have hl : raw15617step0Labels = raw15617Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15617 raw15617Labels permutation229 permutation5
    mixedMoment B raw15617step0 raw15617step0Labels = mixedMoment B raw15617step1 raw15617step1Labels := by
      have ha : raw15617step1 = -raw15617step0 := by apply Matrix.ext; change ∀ i j, raw15617step1 i j = -(raw15617step0 i j); unfold raw15617step1 raw15617step0; decide +kernel
      have hl : raw15617step1Labels = raw15617step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15617step1 raw15617step1Labels = mixedMoment B raw15617step2 raw15617step2Labels := by
      have ha : raw15617step2 = raw15617step1 := by apply Matrix.ext; unfold raw15617step2 raw15617step1; decide +kernel
      have hl : raw15617step1Labels = labelEmbedding1 ∘ raw15617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15617step1 raw15617step1Labels raw15617step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw15618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15618 raw15618Labels = mixedMoment B node2076 node2076Labels := by
  calc
    mixedMoment B raw15618 raw15618Labels = mixedMoment B raw15618step0 raw15618step0Labels := by
      have ha : raw15618step0 = (fun i j => raw15618 (permutation225 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15618step0 raw15618; decide +kernel
      have hl : raw15618step0Labels = raw15618Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15618 raw15618Labels permutation225 permutation5
    mixedMoment B raw15618step0 raw15618step0Labels = mixedMoment B raw15618step1 raw15618step1Labels := by
      have ha : raw15618step1 = -raw15618step0 := by apply Matrix.ext; change ∀ i j, raw15618step1 i j = -(raw15618step0 i j); unfold raw15618step1 raw15618step0; decide +kernel
      have hl : raw15618step1Labels = raw15618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15618step1 raw15618step1Labels = mixedMoment B raw15618step2 raw15618step2Labels := by
      have ha : raw15618step2 = raw15618step1 := by apply Matrix.ext; unfold raw15618step2 raw15618step1; decide +kernel
      have hl : raw15618step1Labels = labelEmbedding1 ∘ raw15618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15618step1 raw15618step1Labels raw15618step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2076 node2076Labels := by rfl

def raw15619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15619step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15619 raw15619Labels = mixedMoment B node3750 node3750Labels := by
  calc
    mixedMoment B raw15619 raw15619Labels = mixedMoment B raw15619step0 raw15619step0Labels := by
      have ha : raw15619step0 = (fun i j => raw15619 (permutation165 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15619step0 raw15619; decide +kernel
      have hl : raw15619step0Labels = raw15619Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15619 raw15619Labels permutation165 permutation5
    mixedMoment B raw15619step0 raw15619step0Labels = mixedMoment B raw15619step1 raw15619step1Labels := by
      have ha : raw15619step1 = -raw15619step0 := by apply Matrix.ext; change ∀ i j, raw15619step1 i j = -(raw15619step0 i j); unfold raw15619step1 raw15619step0; decide +kernel
      have hl : raw15619step1Labels = raw15619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15619step1 raw15619step1Labels = mixedMoment B raw15619step2 raw15619step2Labels := by
      have ha : raw15619step2 = raw15619step1 := by apply Matrix.ext; unfold raw15619step2 raw15619step1; decide +kernel
      have hl : raw15619step1Labels = labelEmbedding1 ∘ raw15619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15619step1 raw15619step1Labels raw15619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3750 node3750Labels := by rfl

def raw15620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15620step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15620 raw15620Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw15620 raw15620Labels = mixedMoment B raw15620step0 raw15620step0Labels := by
      have ha : raw15620step0 = (fun i j => raw15620 (permutation225 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15620step0 raw15620; decide +kernel
      have hl : raw15620step0Labels = raw15620Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15620 raw15620Labels permutation225 permutation5
    mixedMoment B raw15620step0 raw15620step0Labels = mixedMoment B raw15620step1 raw15620step1Labels := by
      have ha : raw15620step1 = -raw15620step0 := by apply Matrix.ext; change ∀ i j, raw15620step1 i j = -(raw15620step0 i j); unfold raw15620step1 raw15620step0; decide +kernel
      have hl : raw15620step1Labels = raw15620step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15620step1 raw15620step1Labels = mixedMoment B raw15620step2 raw15620step2Labels := by
      have ha : raw15620step2 = raw15620step1 := by apply Matrix.ext; unfold raw15620step2 raw15620step1; decide +kernel
      have hl : raw15620step1Labels = labelEmbedding1 ∘ raw15620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15620step1 raw15620step1Labels raw15620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw15621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw15621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15621step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw15621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15621 raw15621Labels = mixedMoment B node3720 node3720Labels := by
  calc
    mixedMoment B raw15621 raw15621Labels = mixedMoment B raw15621step0 raw15621step0Labels := by
      have ha : raw15621step0 = (fun i j => raw15621 (permutation225 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15621step0 raw15621; decide +kernel
      have hl : raw15621step0Labels = raw15621Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15621 raw15621Labels permutation225 permutation5
    mixedMoment B raw15621step0 raw15621step0Labels = mixedMoment B raw15621step1 raw15621step1Labels := by
      have ha : raw15621step1 = -raw15621step0 := by apply Matrix.ext; change ∀ i j, raw15621step1 i j = -(raw15621step0 i j); unfold raw15621step1 raw15621step0; decide +kernel
      have hl : raw15621step1Labels = raw15621step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15621step1 raw15621step1Labels = mixedMoment B raw15621step2 raw15621step2Labels := by
      have ha : raw15621step2 = raw15621step1 := by apply Matrix.ext; unfold raw15621step2 raw15621step1; decide +kernel
      have hl : raw15621step1Labels = labelEmbedding1 ∘ raw15621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15621step1 raw15621step1Labels raw15621step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3720 node3720Labels := by rfl

def raw15622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15622step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15622 raw15622Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw15622 raw15622Labels = mixedMoment B raw15622step0 raw15622step0Labels := by
      have ha : raw15622step0 = (fun i j => raw15622 (permutation228 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15622step0 raw15622; decide +kernel
      have hl : raw15622step0Labels = raw15622Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15622 raw15622Labels permutation228 permutation5
    mixedMoment B raw15622step0 raw15622step0Labels = mixedMoment B raw15622step1 raw15622step1Labels := by
      have ha : raw15622step1 = -raw15622step0 := by apply Matrix.ext; change ∀ i j, raw15622step1 i j = -(raw15622step0 i j); unfold raw15622step1 raw15622step0; decide +kernel
      have hl : raw15622step1Labels = raw15622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15622step1 raw15622step1Labels = mixedMoment B raw15622step2 raw15622step2Labels := by
      have ha : raw15622step2 = raw15622step1 := by apply Matrix.ext; unfold raw15622step2 raw15622step1; decide +kernel
      have hl : raw15622step1Labels = labelEmbedding1 ∘ raw15622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15622step1 raw15622step1Labels raw15622step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw15623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15623step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15623 raw15623Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw15623 raw15623Labels = mixedMoment B raw15623step0 raw15623step0Labels := by
      have ha : raw15623step0 = (fun i j => raw15623 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15623step0 raw15623; decide +kernel
      have hl : raw15623step0Labels = raw15623Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15623 raw15623Labels permutation164 permutation5
    mixedMoment B raw15623step0 raw15623step0Labels = mixedMoment B raw15623step1 raw15623step1Labels := by
      have ha : raw15623step1 = -raw15623step0 := by apply Matrix.ext; change ∀ i j, raw15623step1 i j = -(raw15623step0 i j); unfold raw15623step1 raw15623step0; decide +kernel
      have hl : raw15623step1Labels = raw15623step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15623step1 raw15623step1Labels = mixedMoment B raw15623step2 raw15623step2Labels := by
      have ha : raw15623step2 = raw15623step1 := by apply Matrix.ext; unfold raw15623step2 raw15623step1; decide +kernel
      have hl : raw15623step1Labels = labelEmbedding1 ∘ raw15623step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15623step1 raw15623step1Labels raw15623step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw15624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15624 raw15624Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw15624 raw15624Labels = mixedMoment B raw15624step0 raw15624step0Labels := by
      have ha : raw15624step0 = (fun i j => raw15624 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15624step0 raw15624; decide +kernel
      have hl : raw15624step0Labels = raw15624Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15624 raw15624Labels permutation164 permutation5
    mixedMoment B raw15624step0 raw15624step0Labels = mixedMoment B raw15624step1 raw15624step1Labels := by
      have ha : raw15624step1 = -raw15624step0 := by apply Matrix.ext; change ∀ i j, raw15624step1 i j = -(raw15624step0 i j); unfold raw15624step1 raw15624step0; decide +kernel
      have hl : raw15624step1Labels = raw15624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15624step1 raw15624step1Labels = mixedMoment B raw15624step2 raw15624step2Labels := by
      have ha : raw15624step2 = raw15624step1 := by apply Matrix.ext; unfold raw15624step2 raw15624step1; decide +kernel
      have hl : raw15624step1Labels = labelEmbedding1 ∘ raw15624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15624step1 raw15624step1Labels raw15624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

def raw15625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15625 raw15625Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw15625 raw15625Labels = mixedMoment B raw15625step0 raw15625step0Labels := by
      have ha : raw15625step0 = (fun i j => raw15625 (permutation573 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15625step0 raw15625; decide +kernel
      have hl : raw15625step0Labels = raw15625Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15625 raw15625Labels permutation573 permutation7
    mixedMoment B raw15625step0 raw15625step0Labels = mixedMoment B raw15625step1 raw15625step1Labels := by
      have ha : raw15625step1 = raw15625step0 := by apply Matrix.ext; unfold raw15625step1 raw15625step0; decide +kernel
      have hl : raw15625step0Labels = labelEmbedding1 ∘ raw15625step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15625step0 raw15625step0Labels raw15625step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw15626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15626 raw15626Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw15626 raw15626Labels = mixedMoment B raw15626step0 raw15626step0Labels := by
      have ha : raw15626step0 = (fun i j => raw15626 (permutation571 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15626step0 raw15626; decide +kernel
      have hl : raw15626step0Labels = raw15626Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15626 raw15626Labels permutation571 permutation7
    mixedMoment B raw15626step0 raw15626step0Labels = mixedMoment B raw15626step1 raw15626step1Labels := by
      have ha : raw15626step1 = raw15626step0 := by apply Matrix.ext; unfold raw15626step1 raw15626step0; decide +kernel
      have hl : raw15626step0Labels = labelEmbedding1 ∘ raw15626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15626step0 raw15626step0Labels raw15626step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw15627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15627step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15627 raw15627Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw15627 raw15627Labels = mixedMoment B raw15627step0 raw15627step0Labels := by
      have ha : raw15627step0 = (fun i j => raw15627 (permutation572 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15627step0 raw15627; decide +kernel
      have hl : raw15627step0Labels = raw15627Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15627 raw15627Labels permutation572 permutation7
    mixedMoment B raw15627step0 raw15627step0Labels = mixedMoment B raw15627step1 raw15627step1Labels := by
      have ha : raw15627step1 = raw15627step0 := by apply Matrix.ext; unfold raw15627step1 raw15627step0; decide +kernel
      have hl : raw15627step0Labels = labelEmbedding1 ∘ raw15627step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15627step0 raw15627step0Labels raw15627step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw15628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw15628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw15628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw15628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15628 raw15628Labels = mixedMoment B node2074 node2074Labels := by
  calc
    mixedMoment B raw15628 raw15628Labels = mixedMoment B raw15628step0 raw15628step0Labels := by
      have ha : raw15628step0 = (fun i j => raw15628 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15628step0 raw15628; decide +kernel
      have hl : raw15628step0Labels = raw15628Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15628 raw15628Labels permutation224 permutation5
    mixedMoment B raw15628step0 raw15628step0Labels = mixedMoment B raw15628step1 raw15628step1Labels := by
      have ha : raw15628step1 = -raw15628step0 := by apply Matrix.ext; change ∀ i j, raw15628step1 i j = -(raw15628step0 i j); unfold raw15628step1 raw15628step0; decide +kernel
      have hl : raw15628step1Labels = raw15628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15628step1 raw15628step1Labels = mixedMoment B raw15628step2 raw15628step2Labels := by
      have ha : raw15628step2 = raw15628step1 := by apply Matrix.ext; unfold raw15628step2 raw15628step1; decide +kernel
      have hl : raw15628step1Labels = labelEmbedding1 ∘ raw15628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15628step1 raw15628step1Labels raw15628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2074 node2074Labels := by rfl

def raw15629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15629step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw15629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15629 raw15629Labels = mixedMoment B node3491 node3491Labels := by
  calc
    mixedMoment B raw15629 raw15629Labels = mixedMoment B raw15629step0 raw15629step0Labels := by
      have ha : raw15629step0 = (fun i j => raw15629 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15629step0 raw15629; decide +kernel
      have hl : raw15629step0Labels = raw15629Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15629 raw15629Labels permutation640 permutation5
    mixedMoment B raw15629step0 raw15629step0Labels = mixedMoment B raw15629step1 raw15629step1Labels := by
      have ha : raw15629step1 = raw15629step0 := by apply Matrix.ext; unfold raw15629step1 raw15629step0; decide +kernel
      have hl : raw15629step0Labels = labelEmbedding1 ∘ raw15629step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15629step0 raw15629step0Labels raw15629step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3491 node3491Labels := by rfl

def raw15630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15630 raw15630Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw15630 raw15630Labels = mixedMoment B raw15630step0 raw15630step0Labels := by
      have ha : raw15630step0 = (fun i j => raw15630 (permutation653 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15630step0 raw15630; decide +kernel
      have hl : raw15630step0Labels = raw15630Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15630 raw15630Labels permutation653 permutation5
    mixedMoment B raw15630step0 raw15630step0Labels = mixedMoment B raw15630step1 raw15630step1Labels := by
      have ha : raw15630step1 = raw15630step0 := by apply Matrix.ext; unfold raw15630step1 raw15630step0; decide +kernel
      have hl : raw15630step0Labels = labelEmbedding1 ∘ raw15630step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15630step0 raw15630step0Labels raw15630step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

def raw15631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15631Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15631step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15631 raw15631Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw15631 raw15631Labels = mixedMoment B raw15631step0 raw15631step0Labels := by
      have ha : raw15631step0 = (fun i j => raw15631 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15631step0 raw15631; decide +kernel
      have hl : raw15631step0Labels = raw15631Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15631 raw15631Labels permutation632 permutation5
    mixedMoment B raw15631step0 raw15631step0Labels = mixedMoment B raw15631step1 raw15631step1Labels := by
      have ha : raw15631step1 = raw15631step0 := by apply Matrix.ext; unfold raw15631step1 raw15631step0; decide +kernel
      have hl : raw15631step0Labels = labelEmbedding1 ∘ raw15631step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15631step0 raw15631step0Labels raw15631step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

def raw15632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw15632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15632 raw15632Labels = mixedMoment B node3488 node3488Labels := by
  calc
    mixedMoment B raw15632 raw15632Labels = mixedMoment B raw15632step0 raw15632step0Labels := by
      have ha : raw15632step0 = (fun i j => raw15632 (permutation638 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15632step0 raw15632; decide +kernel
      have hl : raw15632step0Labels = raw15632Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15632 raw15632Labels permutation638 permutation5
    mixedMoment B raw15632step0 raw15632step0Labels = mixedMoment B raw15632step1 raw15632step1Labels := by
      have ha : raw15632step1 = raw15632step0 := by apply Matrix.ext; unfold raw15632step1 raw15632step0; decide +kernel
      have hl : raw15632step0Labels = labelEmbedding1 ∘ raw15632step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15632step0 raw15632step0Labels raw15632step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3488 node3488Labels := by rfl

def raw15633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15633Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15633 raw15633Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw15633 raw15633Labels = mixedMoment B raw15633step0 raw15633step0Labels := by
      have ha : raw15633step0 = (fun i j => raw15633 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15633step0 raw15633; decide +kernel
      have hl : raw15633step0Labels = raw15633Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15633 raw15633Labels permutation682 permutation2
    mixedMoment B raw15633step0 raw15633step0Labels = mixedMoment B raw15633step1 raw15633step1Labels := by
      have ha : raw15633step1 = -raw15633step0 := by apply Matrix.ext; change ∀ i j, raw15633step1 i j = -(raw15633step0 i j); unfold raw15633step1 raw15633step0; decide +kernel
      have hl : raw15633step1Labels = raw15633step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw15634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15634Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15634step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15634 raw15634Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw15634 raw15634Labels = mixedMoment B raw15634step0 raw15634step0Labels := by
      have ha : raw15634step0 = (fun i j => raw15634 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15634step0 raw15634; decide +kernel
      have hl : raw15634step0Labels = raw15634Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15634 raw15634Labels permutation681 permutation2
    mixedMoment B raw15634step0 raw15634step0Labels = mixedMoment B raw15634step1 raw15634step1Labels := by
      have ha : raw15634step1 = -raw15634step0 := by apply Matrix.ext; change ∀ i j, raw15634step1 i j = -(raw15634step0 i j); unfold raw15634step1 raw15634step0; decide +kernel
      have hl : raw15634step1Labels = raw15634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3953 node3953Labels := by rfl

def raw15635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15635Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15635step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15635 raw15635Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw15635 raw15635Labels = mixedMoment B raw15635step0 raw15635step0Labels := by
      have ha : raw15635step0 = (fun i j => raw15635 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15635step0 raw15635; decide +kernel
      have hl : raw15635step0Labels = raw15635Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15635 raw15635Labels permutation683 permutation2
    mixedMoment B raw15635step0 raw15635step0Labels = mixedMoment B raw15635step1 raw15635step1Labels := by
      have ha : raw15635step1 = -raw15635step0 := by apply Matrix.ext; change ∀ i j, raw15635step1 i j = -(raw15635step0 i j); unfold raw15635step1 raw15635step0; decide +kernel
      have hl : raw15635step1Labels = raw15635step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw15636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15636Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15636 raw15636Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw15636 raw15636Labels = mixedMoment B raw15636step0 raw15636step0Labels := by
      have ha : raw15636step0 = (fun i j => raw15636 (permutation677 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15636step0 raw15636; decide +kernel
      have hl : raw15636step0Labels = raw15636Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15636 raw15636Labels permutation677 permutation2
    mixedMoment B raw15636step0 raw15636step0Labels = mixedMoment B raw15636step1 raw15636step1Labels := by
      have ha : raw15636step1 = -raw15636step0 := by apply Matrix.ext; change ∀ i j, raw15636step1 i j = -(raw15636step0 i j); unfold raw15636step1 raw15636step0; decide +kernel
      have hl : raw15636step1Labels = raw15636step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw15637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15637Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15637 raw15637Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw15637 raw15637Labels = mixedMoment B raw15637step0 raw15637step0Labels := by
      have ha : raw15637step0 = (fun i j => raw15637 (permutation524 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15637step0 raw15637; decide +kernel
      have hl : raw15637step0Labels = raw15637Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15637 raw15637Labels permutation524 permutation4
    mixedMoment B raw15637step0 raw15637step0Labels = mixedMoment B raw15637step1 raw15637step1Labels := by
      have ha : raw15637step1 = -raw15637step0 := by apply Matrix.ext; change ∀ i j, raw15637step1 i j = -(raw15637step0 i j); unfold raw15637step1 raw15637step0; decide +kernel
      have hl : raw15637step1Labels = raw15637step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw15638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15638Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15638 raw15638Labels = mixedMoment B node4046 node4046Labels := by
  calc
    mixedMoment B raw15638 raw15638Labels = mixedMoment B raw15638step0 raw15638step0Labels := by
      have ha : raw15638step0 = (fun i j => raw15638 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15638step0 raw15638; decide +kernel
      have hl : raw15638step0Labels = raw15638Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15638 raw15638Labels permutation583 permutation2
    mixedMoment B raw15638step0 raw15638step0Labels = mixedMoment B raw15638step1 raw15638step1Labels := by
      have ha : raw15638step1 = -raw15638step0 := by apply Matrix.ext; change ∀ i j, raw15638step1 i j = -(raw15638step0 i j); unfold raw15638step1 raw15638step0; decide +kernel
      have hl : raw15638step1Labels = raw15638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4046 node4046Labels := by rfl

def raw15639 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw15639Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15639step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw15639step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15639step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw15639step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw15639step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw15639step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical15639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15639 raw15639Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw15639 raw15639Labels = mixedMoment B raw15639step0 raw15639step0Labels := by
      have hz : ∀ j, raw15639 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw15639step0 = (fun i j => raw15639 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw15639step0 raw15639; decide +kernel
      have hl : raw15639step0Labels = raw15639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15639 raw15639Labels permutation152 hz
    mixedMoment B raw15639step0 raw15639step0Labels = mixedMoment B raw15639step1 raw15639step1Labels := by
      have ha : raw15639step1 = (fun i j => raw15639step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw15639step1 raw15639step0; decide +kernel
      have hl : raw15639step1Labels = raw15639step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15639step0 raw15639step0Labels permutation122 permutation0
    mixedMoment B raw15639step1 raw15639step1Labels = mixedMoment B raw15639step2 raw15639step2Labels := by
      have ha : raw15639step2 = -raw15639step1 := by apply Matrix.ext; change ∀ i j, raw15639step2 i j = -(raw15639step1 i j); unfold raw15639step2 raw15639step1; decide +kernel
      have hl : raw15639step2Labels = raw15639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw15640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15640Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15640step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15640 raw15640Labels = mixedMoment B node3179 node3179Labels := by
  calc
    mixedMoment B raw15640 raw15640Labels = mixedMoment B raw15640step0 raw15640step0Labels := by
      have ha : raw15640step0 = (fun i j => raw15640 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15640step0 raw15640; decide +kernel
      have hl : raw15640step0Labels = raw15640Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15640 raw15640Labels permutation240 permutation4
    mixedMoment B raw15640step0 raw15640step0Labels = mixedMoment B raw15640step1 raw15640step1Labels := by
      have ha : raw15640step1 = -raw15640step0 := by apply Matrix.ext; change ∀ i j, raw15640step1 i j = -(raw15640step0 i j); unfold raw15640step1 raw15640step0; decide +kernel
      have hl : raw15640step1Labels = raw15640step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3179 node3179Labels := by rfl

def raw15641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15641Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15641step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15641 raw15641Labels = mixedMoment B node3176 node3176Labels := by
  calc
    mixedMoment B raw15641 raw15641Labels = mixedMoment B raw15641step0 raw15641step0Labels := by
      have ha : raw15641step0 = (fun i j => raw15641 (permutation229 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15641step0 raw15641; decide +kernel
      have hl : raw15641step0Labels = raw15641Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15641 raw15641Labels permutation229 permutation4
    mixedMoment B raw15641step0 raw15641step0Labels = mixedMoment B raw15641step1 raw15641step1Labels := by
      have ha : raw15641step1 = -raw15641step0 := by apply Matrix.ext; change ∀ i j, raw15641step1 i j = -(raw15641step0 i j); unfold raw15641step1 raw15641step0; decide +kernel
      have hl : raw15641step1Labels = raw15641step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3176 node3176Labels := by rfl

def raw15642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15642Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15642step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15642 raw15642Labels = mixedMoment B node3176 node3176Labels := by
  calc
    mixedMoment B raw15642 raw15642Labels = mixedMoment B raw15642step0 raw15642step0Labels := by
      have ha : raw15642step0 = (fun i j => raw15642 (permutation228 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15642step0 raw15642; decide +kernel
      have hl : raw15642step0Labels = raw15642Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15642 raw15642Labels permutation228 permutation4
    mixedMoment B raw15642step0 raw15642step0Labels = mixedMoment B raw15642step1 raw15642step1Labels := by
      have ha : raw15642step1 = -raw15642step0 := by apply Matrix.ext; change ∀ i j, raw15642step1 i j = -(raw15642step0 i j); unfold raw15642step1 raw15642step0; decide +kernel
      have hl : raw15642step1Labels = raw15642step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3176 node3176Labels := by rfl

def raw15643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15643Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw15643step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15643 raw15643Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw15643 raw15643Labels = mixedMoment B raw15643step0 raw15643step0Labels := by
      have ha : raw15643step0 = (fun i j => raw15643 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15643step0 raw15643; decide +kernel
      have hl : raw15643step0Labels = raw15643Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15643 raw15643Labels permutation153 permutation2
    _ = mixedMoment B node3199 node3199Labels := by rfl

def raw15644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15644Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw15644step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw15644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15644 raw15644Labels = mixedMoment B node2858 node2858Labels := by
  calc
    mixedMoment B raw15644 raw15644Labels = mixedMoment B raw15644step0 raw15644step0Labels := by
      have ha : raw15644step0 = (fun i j => raw15644 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15644step0 raw15644; decide +kernel
      have hl : raw15644step0Labels = raw15644Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15644 raw15644Labels permutation682 permutation2
    mixedMoment B raw15644step0 raw15644step0Labels = mixedMoment B raw15644step1 raw15644step1Labels := by
      have ha : raw15644step1 = -raw15644step0 := by apply Matrix.ext; change ∀ i j, raw15644step1 i j = -(raw15644step0 i j); unfold raw15644step1 raw15644step0; decide +kernel
      have hl : raw15644step1Labels = raw15644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2858 node2858Labels := by rfl

def raw15645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15645Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15645step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15645step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15645 raw15645Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw15645 raw15645Labels = mixedMoment B raw15645step0 raw15645step0Labels := by
      have ha : raw15645step0 = (fun i j => raw15645 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15645step0 raw15645; decide +kernel
      have hl : raw15645step0Labels = raw15645Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15645 raw15645Labels permutation676 permutation2
    mixedMoment B raw15645step0 raw15645step0Labels = mixedMoment B raw15645step1 raw15645step1Labels := by
      have ha : raw15645step1 = -raw15645step0 := by apply Matrix.ext; change ∀ i j, raw15645step1 i j = -(raw15645step0 i j); unfold raw15645step1 raw15645step0; decide +kernel
      have hl : raw15645step1Labels = raw15645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw15646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15646Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15646step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15646step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15646 raw15646Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw15646 raw15646Labels = mixedMoment B raw15646step0 raw15646step0Labels := by
      have ha : raw15646step0 = (fun i j => raw15646 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15646step0 raw15646; decide +kernel
      have hl : raw15646step0Labels = raw15646Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15646 raw15646Labels permutation674 permutation2
    mixedMoment B raw15646step0 raw15646step0Labels = mixedMoment B raw15646step1 raw15646step1Labels := by
      have ha : raw15646step1 = -raw15646step0 := by apply Matrix.ext; change ∀ i j, raw15646step1 i j = -(raw15646step0 i j); unfold raw15646step1 raw15646step0; decide +kernel
      have hl : raw15646step1Labels = raw15646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw15647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15647Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15647step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15647step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15647 raw15647Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw15647 raw15647Labels = mixedMoment B raw15647step0 raw15647step0Labels := by
      have ha : raw15647step0 = (fun i j => raw15647 (permutation526 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15647step0 raw15647; decide +kernel
      have hl : raw15647step0Labels = raw15647Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15647 raw15647Labels permutation526 permutation4
    mixedMoment B raw15647step0 raw15647step0Labels = mixedMoment B raw15647step1 raw15647step1Labels := by
      have ha : raw15647step1 = -raw15647step0 := by apply Matrix.ext; change ∀ i j, raw15647step1 i j = -(raw15647step0 i j); unfold raw15647step1 raw15647step0; decide +kernel
      have hl : raw15647step1Labels = raw15647step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3731 node3731Labels := by rfl

def raw15648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15648Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw15648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15648 raw15648Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw15648 raw15648Labels = mixedMoment B raw15648step0 raw15648step0Labels := by
      have ha : raw15648step0 = (fun i j => raw15648 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15648step0 raw15648; decide +kernel
      have hl : raw15648step0Labels = raw15648Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15648 raw15648Labels permutation240 permutation4
    mixedMoment B raw15648step0 raw15648step0Labels = mixedMoment B raw15648step1 raw15648step1Labels := by
      have ha : raw15648step1 = -raw15648step0 := by apply Matrix.ext; change ∀ i j, raw15648step1 i j = -(raw15648step0 i j); unfold raw15648step1 raw15648step0; decide +kernel
      have hl : raw15648step1Labels = raw15648step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw15649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15649Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15649step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15649 raw15649Labels = mixedMoment B node3935 node3935Labels := by
  calc
    mixedMoment B raw15649 raw15649Labels = mixedMoment B raw15649step0 raw15649step0Labels := by
      have ha : raw15649step0 = (fun i j => raw15649 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15649step0 raw15649; decide +kernel
      have hl : raw15649step0Labels = raw15649Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15649 raw15649Labels permutation271 permutation2
    _ = mixedMoment B node3935 node3935Labels := by rfl

def raw15650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15650Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15650 raw15650Labels = mixedMoment B node3935 node3935Labels := by
  calc
    mixedMoment B raw15650 raw15650Labels = mixedMoment B raw15650step0 raw15650step0Labels := by
      have ha : raw15650step0 = (fun i j => raw15650 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15650step0 raw15650; decide +kernel
      have hl : raw15650step0Labels = raw15650Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15650 raw15650Labels permutation265 permutation2
    _ = mixedMoment B node3935 node3935Labels := by rfl

def raw15651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15651Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15651step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15651 raw15651Labels = mixedMoment B node3685 node3685Labels := by
  calc
    mixedMoment B raw15651 raw15651Labels = mixedMoment B raw15651step0 raw15651step0Labels := by
      have ha : raw15651step0 = (fun i j => raw15651 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15651step0 raw15651; decide +kernel
      have hl : raw15651step0Labels = raw15651Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15651 raw15651Labels permutation583 permutation2
    mixedMoment B raw15651step0 raw15651step0Labels = mixedMoment B raw15651step1 raw15651step1Labels := by
      have ha : raw15651step1 = -raw15651step0 := by apply Matrix.ext; change ∀ i j, raw15651step1 i j = -(raw15651step0 i j); unfold raw15651step1 raw15651step0; decide +kernel
      have hl : raw15651step1Labels = raw15651step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3685 node3685Labels := by rfl

def raw15652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15652Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw15652step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15652 raw15652Labels = mixedMoment B node2859 node2859Labels := by
  calc
    mixedMoment B raw15652 raw15652Labels = mixedMoment B raw15652step0 raw15652step0Labels := by
      have ha : raw15652step0 = (fun i j => raw15652 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15652step0 raw15652; decide +kernel
      have hl : raw15652step0Labels = raw15652Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15652 raw15652Labels permutation681 permutation2
    mixedMoment B raw15652step0 raw15652step0Labels = mixedMoment B raw15652step1 raw15652step1Labels := by
      have ha : raw15652step1 = -raw15652step0 := by apply Matrix.ext; change ∀ i j, raw15652step1 i j = -(raw15652step0 i j); unfold raw15652step1 raw15652step0; decide +kernel
      have hl : raw15652step1Labels = raw15652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2859 node2859Labels := by rfl

def raw15653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15653Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15653 raw15653Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw15653 raw15653Labels = mixedMoment B raw15653step0 raw15653step0Labels := by
      have ha : raw15653step0 = (fun i j => raw15653 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15653step0 raw15653; decide +kernel
      have hl : raw15653step0Labels = raw15653Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15653 raw15653Labels permutation680 permutation2
    mixedMoment B raw15653step0 raw15653step0Labels = mixedMoment B raw15653step1 raw15653step1Labels := by
      have ha : raw15653step1 = -raw15653step0 := by apply Matrix.ext; change ∀ i j, raw15653step1 i j = -(raw15653step0 i j); unfold raw15653step1 raw15653step0; decide +kernel
      have hl : raw15653step1Labels = raw15653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3949 node3949Labels := by rfl

def raw15654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15654Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15654 raw15654Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw15654 raw15654Labels = mixedMoment B raw15654step0 raw15654step0Labels := by
      have ha : raw15654step0 = (fun i j => raw15654 (permutation525 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15654step0 raw15654; decide +kernel
      have hl : raw15654step0Labels = raw15654Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15654 raw15654Labels permutation525 permutation4
    mixedMoment B raw15654step0 raw15654step0Labels = mixedMoment B raw15654step1 raw15654step1Labels := by
      have ha : raw15654step1 = -raw15654step0 := by apply Matrix.ext; change ∀ i j, raw15654step1 i j = -(raw15654step0 i j); unfold raw15654step1 raw15654step0; decide +kernel
      have hl : raw15654step1Labels = raw15654step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3724 node3724Labels := by rfl

def raw15655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw15655Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15655 raw15655Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw15655 raw15655Labels = mixedMoment B raw15655step0 raw15655step0Labels := by
      have ha : raw15655step0 = (fun i j => raw15655 (permutation388 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15655step0 raw15655; decide +kernel
      have hl : raw15655step0Labels = raw15655Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15655 raw15655Labels permutation388 permutation4
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw15656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw15656Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15656 raw15656Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw15656 raw15656Labels = mixedMoment B raw15656step0 raw15656step0Labels := by
      have ha : raw15656step0 = (fun i j => raw15656 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15656step0 raw15656; decide +kernel
      have hl : raw15656step0Labels = raw15656Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15656 raw15656Labels permutation686 permutation2
    mixedMoment B raw15656step0 raw15656step0Labels = mixedMoment B raw15656step1 raw15656step1Labels := by
      have ha : raw15656step1 = -raw15656step0 := by apply Matrix.ext; change ∀ i j, raw15656step1 i j = -(raw15656step0 i j); unfold raw15656step1 raw15656step0; decide +kernel
      have hl : raw15656step1Labels = raw15656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3949 node3949Labels := by rfl

def raw15657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15657Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15657step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15657 raw15657Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw15657 raw15657Labels = mixedMoment B raw15657step0 raw15657step0Labels := by
      have ha : raw15657step0 = (fun i j => raw15657 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15657step0 raw15657; decide +kernel
      have hl : raw15657step0Labels = raw15657Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15657 raw15657Labels permutation587 permutation2
    mixedMoment B raw15657step0 raw15657step0Labels = mixedMoment B raw15657step1 raw15657step1Labels := by
      have ha : raw15657step1 = -raw15657step0 := by apply Matrix.ext; change ∀ i j, raw15657step1 i j = -(raw15657step0 i j); unfold raw15657step1 raw15657step0; decide +kernel
      have hl : raw15657step1Labels = raw15657step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3692 node3692Labels := by rfl

def raw15658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15658Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15658step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15658 raw15658Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw15658 raw15658Labels = mixedMoment B raw15658step0 raw15658step0Labels := by
      have ha : raw15658step0 = (fun i j => raw15658 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15658step0 raw15658; decide +kernel
      have hl : raw15658step0Labels = raw15658Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15658 raw15658Labels permutation686 permutation2
    mixedMoment B raw15658step0 raw15658step0Labels = mixedMoment B raw15658step1 raw15658step1Labels := by
      have ha : raw15658step1 = -raw15658step0 := by apply Matrix.ext; change ∀ i j, raw15658step1 i j = -(raw15658step0 i j); unfold raw15658step1 raw15658step0; decide +kernel
      have hl : raw15658step1Labels = raw15658step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2864 node2864Labels := by rfl

def raw15659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw15659Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15659 raw15659Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw15659 raw15659Labels = mixedMoment B raw15659step0 raw15659step0Labels := by
      have ha : raw15659step0 = (fun i j => raw15659 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15659step0 raw15659; decide +kernel
      have hl : raw15659step0Labels = raw15659Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15659 raw15659Labels permutation582 permutation2
    mixedMoment B raw15659step0 raw15659step0Labels = mixedMoment B raw15659step1 raw15659step1Labels := by
      have ha : raw15659step1 = -raw15659step0 := by apply Matrix.ext; change ∀ i j, raw15659step1 i j = -(raw15659step0 i j); unfold raw15659step1 raw15659step0; decide +kernel
      have hl : raw15659step1Labels = raw15659step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3692 node3692Labels := by rfl

def raw15660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw15660Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15660 raw15660Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw15660 raw15660Labels = mixedMoment B raw15660step0 raw15660step0Labels := by
      have ha : raw15660step0 = (fun i j => raw15660 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15660step0 raw15660; decide +kernel
      have hl : raw15660step0Labels = raw15660Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15660 raw15660Labels permutation584 permutation2
    mixedMoment B raw15660step0 raw15660step0Labels = mixedMoment B raw15660step1 raw15660step1Labels := by
      have ha : raw15660step1 = -raw15660step0 := by apply Matrix.ext; change ∀ i j, raw15660step1 i j = -(raw15660step0 i j); unfold raw15660step1 raw15660step0; decide +kernel
      have hl : raw15660step1Labels = raw15660step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw15661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw15661Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15661step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15661 raw15661Labels = mixedMoment B node3724 node3724Labels := by
  calc
    mixedMoment B raw15661 raw15661Labels = mixedMoment B raw15661step0 raw15661step0Labels := by
      have ha : raw15661step0 = (fun i j => raw15661 (permutation524 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15661step0 raw15661; decide +kernel
      have hl : raw15661step0Labels = raw15661Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15661 raw15661Labels permutation524 permutation4
    mixedMoment B raw15661step0 raw15661step0Labels = mixedMoment B raw15661step1 raw15661step1Labels := by
      have ha : raw15661step1 = -raw15661step0 := by apply Matrix.ext; change ∀ i j, raw15661step1 i j = -(raw15661step0 i j); unfold raw15661step1 raw15661step0; decide +kernel
      have hl : raw15661step1Labels = raw15661step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3724 node3724Labels := by rfl

def raw15662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw15662Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15662 raw15662Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw15662 raw15662Labels = mixedMoment B raw15662step0 raw15662step0Labels := by
      have ha : raw15662step0 = (fun i j => raw15662 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15662step0 raw15662; decide +kernel
      have hl : raw15662step0Labels = raw15662Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15662 raw15662Labels permutation682 permutation2
    mixedMoment B raw15662step0 raw15662step0Labels = mixedMoment B raw15662step1 raw15662step1Labels := by
      have ha : raw15662step1 = -raw15662step0 := by apply Matrix.ext; change ∀ i j, raw15662step1 i j = -(raw15662step0 i j); unfold raw15662step1 raw15662step0; decide +kernel
      have hl : raw15662step1Labels = raw15662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3030 node3030Labels := by rfl

def raw15663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw15663Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15663step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15663 raw15663Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw15663 raw15663Labels = mixedMoment B raw15663step0 raw15663step0Labels := by
      have ha : raw15663step0 = (fun i j => raw15663 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15663step0 raw15663; decide +kernel
      have hl : raw15663step0Labels = raw15663Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15663 raw15663Labels permutation680 permutation2
    mixedMoment B raw15663step0 raw15663step0Labels = mixedMoment B raw15663step1 raw15663step1Labels := by
      have ha : raw15663step1 = -raw15663step0 := by apply Matrix.ext; change ∀ i j, raw15663step1 i j = -(raw15663step0 i j); unfold raw15663step1 raw15663step0; decide +kernel
      have hl : raw15663step1Labels = raw15663step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2864 node2864Labels := by rfl

def raw15664 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15664step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15664step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15664step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15664step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15664 raw15664Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw15664 raw15664Labels = mixedMoment B raw15664step0 raw15664step0Labels := by
      have ha : raw15664step0 = (fun i j => raw15664 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15664step0 raw15664; decide +kernel
      have hl : raw15664step0Labels = raw15664Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15664 raw15664Labels permutation682 permutation7
    mixedMoment B raw15664step0 raw15664step0Labels = mixedMoment B raw15664step1 raw15664step1Labels := by
      have ha : raw15664step1 = -raw15664step0 := by apply Matrix.ext; change ∀ i j, raw15664step1 i j = -(raw15664step0 i j); unfold raw15664step1 raw15664step0; decide +kernel
      have hl : raw15664step1Labels = raw15664step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15664step1 raw15664step1Labels = mixedMoment B raw15664step2 raw15664step2Labels := by
      have ha : raw15664step2 = raw15664step1 := by apply Matrix.ext; unfold raw15664step2 raw15664step1; decide +kernel
      have hl : raw15664step1Labels = labelEmbedding10 ∘ raw15664step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15664step1 raw15664step1Labels raw15664step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw15665 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15665step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15665step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15665step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15665step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15665step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15665 raw15665Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw15665 raw15665Labels = mixedMoment B raw15665step0 raw15665step0Labels := by
      have hz : ∀ j, raw15665 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15665step0 = (fun i j => raw15665 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15665step0 raw15665; decide +kernel
      have hl : raw15665step0Labels = raw15665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15665 raw15665Labels permutation434 hz
    mixedMoment B raw15665step0 raw15665step0Labels = mixedMoment B raw15665step1 raw15665step1Labels := by
      have ha : raw15665step1 = (fun i j => raw15665step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15665step1 raw15665step0; decide +kernel
      have hl : raw15665step1Labels = raw15665step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15665step0 raw15665step0Labels permutation151 permutation7
    mixedMoment B raw15665step1 raw15665step1Labels = mixedMoment B raw15665step2 raw15665step2Labels := by
      have ha : raw15665step2 = -raw15665step1 := by apply Matrix.ext; change ∀ i j, raw15665step2 i j = -(raw15665step1 i j); unfold raw15665step2 raw15665step1; decide +kernel
      have hl : raw15665step2Labels = raw15665step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15665step2 raw15665step2Labels = mixedMoment B raw15665step3 raw15665step3Labels := by
      have ha : raw15665step3 = raw15665step2 := by apply Matrix.ext; unfold raw15665step3 raw15665step2; decide +kernel
      have hl : raw15665step2Labels = labelEmbedding10 ∘ raw15665step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15665step2 raw15665step2Labels raw15665step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw15666 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15666step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15666 raw15666Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw15666 raw15666Labels = mixedMoment B raw15666step0 raw15666step0Labels := by
      have ha : raw15666step0 = (fun i j => raw15666 (permutation569 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15666step0 raw15666; decide +kernel
      have hl : raw15666step0Labels = raw15666Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15666 raw15666Labels permutation569 permutation3
    mixedMoment B raw15666step0 raw15666step0Labels = mixedMoment B raw15666step1 raw15666step1Labels := by
      have ha : raw15666step1 = raw15666step0 := by apply Matrix.ext; unfold raw15666step1 raw15666step0; decide +kernel
      have hl : raw15666step0Labels = labelEmbedding6 ∘ raw15666step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15666step0 raw15666step0Labels raw15666step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw15667 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15667step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15667 raw15667Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw15667 raw15667Labels = mixedMoment B raw15667step0 raw15667step0Labels := by
      have ha : raw15667step0 = (fun i j => raw15667 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15667step0 raw15667; decide +kernel
      have hl : raw15667step0Labels = raw15667Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15667 raw15667Labels permutation682 permutation2
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw15668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15668step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15668step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15668step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15668step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15668 raw15668Labels = mixedMoment B node5196 node5196Labels := by
  calc
    mixedMoment B raw15668 raw15668Labels = mixedMoment B raw15668step0 raw15668step0Labels := by
      have ha : raw15668step0 = (fun i j => raw15668 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15668step0 raw15668; decide +kernel
      have hl : raw15668step0Labels = raw15668Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15668 raw15668Labels permutation224 permutation4
    mixedMoment B raw15668step0 raw15668step0Labels = mixedMoment B raw15668step1 raw15668step1Labels := by
      have ha : raw15668step1 = -raw15668step0 := by apply Matrix.ext; change ∀ i j, raw15668step1 i j = -(raw15668step0 i j); unfold raw15668step1 raw15668step0; decide +kernel
      have hl : raw15668step1Labels = raw15668step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15668step1 raw15668step1Labels = mixedMoment B raw15668step2 raw15668step2Labels := by
      have ha : raw15668step2 = raw15668step1 := by apply Matrix.ext; unfold raw15668step2 raw15668step1; decide +kernel
      have hl : raw15668step1Labels = labelEmbedding7 ∘ raw15668step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15668step1 raw15668step1Labels raw15668step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5196 node5196Labels := by rfl

def raw15669 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15669step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw15669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15669step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15669 raw15669Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw15669 raw15669Labels = mixedMoment B raw15669step0 raw15669step0Labels := by
      have hz : ∀ j, raw15669 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15669step0 = (fun i j => raw15669 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15669step0 raw15669; decide +kernel
      have hl : raw15669step0Labels = raw15669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15669 raw15669Labels permutation434 hz
    mixedMoment B raw15669step0 raw15669step0Labels = mixedMoment B raw15669step1 raw15669step1Labels := by
      have ha : raw15669step1 = (fun i j => raw15669step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15669step1 raw15669step0; decide +kernel
      have hl : raw15669step1Labels = raw15669step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15669step0 raw15669step0Labels permutation32 permutation6
    mixedMoment B raw15669step1 raw15669step1Labels = mixedMoment B raw15669step2 raw15669step2Labels := by
      have ha : raw15669step2 = raw15669step1 := by apply Matrix.ext; unfold raw15669step2 raw15669step1; decide +kernel
      have hl : raw15669step1Labels = labelEmbedding9 ∘ raw15669step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15669step1 raw15669step1Labels raw15669step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw15670 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15670step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15670 raw15670Labels = mixedMoment B node5179 node5179Labels := by
  calc
    mixedMoment B raw15670 raw15670Labels = mixedMoment B raw15670step0 raw15670step0Labels := by
      have ha : raw15670step0 = (fun i j => raw15670 (permutation572 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15670step0 raw15670; decide +kernel
      have hl : raw15670step0Labels = raw15670Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15670 raw15670Labels permutation572 permutation3
    mixedMoment B raw15670step0 raw15670step0Labels = mixedMoment B raw15670step1 raw15670step1Labels := by
      have ha : raw15670step1 = raw15670step0 := by apply Matrix.ext; unfold raw15670step1 raw15670step0; decide +kernel
      have hl : raw15670step0Labels = labelEmbedding6 ∘ raw15670step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15670step0 raw15670step0Labels raw15670step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5179 node5179Labels := by rfl

def raw15671 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw15671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15671 raw15671Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw15671 raw15671Labels = mixedMoment B raw15671step0 raw15671step0Labels := by
      have ha : raw15671step0 = (fun i j => raw15671 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15671step0 raw15671; decide +kernel
      have hl : raw15671step0Labels = raw15671Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15671 raw15671Labels permutation668 permutation2
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw15672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15672step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15672step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15672step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15672 raw15672Labels = mixedMoment B node5186 node5186Labels := by
  calc
    mixedMoment B raw15672 raw15672Labels = mixedMoment B raw15672step0 raw15672step0Labels := by
      have ha : raw15672step0 = (fun i j => raw15672 (permutation227 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15672step0 raw15672; decide +kernel
      have hl : raw15672step0Labels = raw15672Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15672 raw15672Labels permutation227 permutation4
    mixedMoment B raw15672step0 raw15672step0Labels = mixedMoment B raw15672step1 raw15672step1Labels := by
      have ha : raw15672step1 = -raw15672step0 := by apply Matrix.ext; change ∀ i j, raw15672step1 i j = -(raw15672step0 i j); unfold raw15672step1 raw15672step0; decide +kernel
      have hl : raw15672step1Labels = raw15672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15672step1 raw15672step1Labels = mixedMoment B raw15672step2 raw15672step2Labels := by
      have ha : raw15672step2 = raw15672step1 := by apply Matrix.ext; unfold raw15672step2 raw15672step1; decide +kernel
      have hl : raw15672step1Labels = labelEmbedding7 ∘ raw15672step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15672step1 raw15672step1Labels raw15672step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5186 node5186Labels := by rfl

def raw15673 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15673step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15673step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15673step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15673step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15673 raw15673Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw15673 raw15673Labels = mixedMoment B raw15673step0 raw15673step0Labels := by
      have ha : raw15673step0 = (fun i j => raw15673 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15673step0 raw15673; decide +kernel
      have hl : raw15673step0Labels = raw15673Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15673 raw15673Labels permutation167 permutation4
    mixedMoment B raw15673step0 raw15673step0Labels = mixedMoment B raw15673step1 raw15673step1Labels := by
      have ha : raw15673step1 = -raw15673step0 := by apply Matrix.ext; change ∀ i j, raw15673step1 i j = -(raw15673step0 i j); unfold raw15673step1 raw15673step0; decide +kernel
      have hl : raw15673step1Labels = raw15673step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15673step1 raw15673step1Labels = mixedMoment B raw15673step2 raw15673step2Labels := by
      have ha : raw15673step2 = raw15673step1 := by apply Matrix.ext; unfold raw15673step2 raw15673step1; decide +kernel
      have hl : raw15673step1Labels = labelEmbedding7 ∘ raw15673step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15673step1 raw15673step1Labels raw15673step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5402 node5402Labels := by rfl

def raw15674 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15674step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15674step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15674 raw15674Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw15674 raw15674Labels = mixedMoment B raw15674step0 raw15674step0Labels := by
      have hz : ∀ j, raw15674 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15674step0 = (fun i j => raw15674 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15674step0 raw15674; decide +kernel
      have hl : raw15674step0Labels = raw15674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15674 raw15674Labels permutation434 hz
    mixedMoment B raw15674step0 raw15674step0Labels = mixedMoment B raw15674step1 raw15674step1Labels := by
      have ha : raw15674step1 = (fun i j => raw15674step0 (permutation87 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15674step1 raw15674step0; decide +kernel
      have hl : raw15674step1Labels = raw15674step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15674step0 raw15674step0Labels permutation87 permutation3
    mixedMoment B raw15674step1 raw15674step1Labels = mixedMoment B raw15674step2 raw15674step2Labels := by
      have ha : raw15674step2 = -raw15674step1 := by apply Matrix.ext; change ∀ i j, raw15674step2 i j = -(raw15674step1 i j); unfold raw15674step2 raw15674step1; decide +kernel
      have hl : raw15674step2Labels = raw15674step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15674step2 raw15674step2Labels = mixedMoment B raw15674step3 raw15674step3Labels := by
      have ha : raw15674step3 = raw15674step2 := by apply Matrix.ext; unfold raw15674step3 raw15674step2; decide +kernel
      have hl : raw15674step2Labels = labelEmbedding6 ∘ raw15674step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15674step2 raw15674step2Labels raw15674step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw15675 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15675step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15675step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15675 raw15675Labels = mixedMoment B node5178 node5178Labels := by
  calc
    mixedMoment B raw15675 raw15675Labels = mixedMoment B raw15675step0 raw15675step0Labels := by
      have ha : raw15675step0 = (fun i j => raw15675 (permutation570 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15675step0 raw15675; decide +kernel
      have hl : raw15675step0Labels = raw15675Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15675 raw15675Labels permutation570 permutation3
    mixedMoment B raw15675step0 raw15675step0Labels = mixedMoment B raw15675step1 raw15675step1Labels := by
      have ha : raw15675step1 = raw15675step0 := by apply Matrix.ext; unfold raw15675step1 raw15675step0; decide +kernel
      have hl : raw15675step0Labels = labelEmbedding6 ∘ raw15675step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15675step0 raw15675step0Labels raw15675step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5178 node5178Labels := by rfl

def raw15676 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15676step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15676 raw15676Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw15676 raw15676Labels = mixedMoment B raw15676step0 raw15676step0Labels := by
      have ha : raw15676step0 = (fun i j => raw15676 (permutation669 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15676step0 raw15676; decide +kernel
      have hl : raw15676step0Labels = raw15676Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15676 raw15676Labels permutation669 permutation2
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw15677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15677step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15677step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15677step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15677step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15677step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15677 raw15677Labels = mixedMoment B node5186 node5186Labels := by
  calc
    mixedMoment B raw15677 raw15677Labels = mixedMoment B raw15677step0 raw15677step0Labels := by
      have ha : raw15677step0 = (fun i j => raw15677 (permutation225 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15677step0 raw15677; decide +kernel
      have hl : raw15677step0Labels = raw15677Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15677 raw15677Labels permutation225 permutation4
    mixedMoment B raw15677step0 raw15677step0Labels = mixedMoment B raw15677step1 raw15677step1Labels := by
      have ha : raw15677step1 = -raw15677step0 := by apply Matrix.ext; change ∀ i j, raw15677step1 i j = -(raw15677step0 i j); unfold raw15677step1 raw15677step0; decide +kernel
      have hl : raw15677step1Labels = raw15677step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15677step1 raw15677step1Labels = mixedMoment B raw15677step2 raw15677step2Labels := by
      have ha : raw15677step2 = raw15677step1 := by apply Matrix.ext; unfold raw15677step2 raw15677step1; decide +kernel
      have hl : raw15677step1Labels = labelEmbedding7 ∘ raw15677step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15677step1 raw15677step1Labels raw15677step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5186 node5186Labels := by rfl

def raw15678 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15678step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15678step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15678step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15678step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15678step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15678 raw15678Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw15678 raw15678Labels = mixedMoment B raw15678step0 raw15678step0Labels := by
      have ha : raw15678step0 = (fun i j => raw15678 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15678step0 raw15678; decide +kernel
      have hl : raw15678step0Labels = raw15678Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15678 raw15678Labels permutation165 permutation4
    mixedMoment B raw15678step0 raw15678step0Labels = mixedMoment B raw15678step1 raw15678step1Labels := by
      have ha : raw15678step1 = -raw15678step0 := by apply Matrix.ext; change ∀ i j, raw15678step1 i j = -(raw15678step0 i j); unfold raw15678step1 raw15678step0; decide +kernel
      have hl : raw15678step1Labels = raw15678step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15678step1 raw15678step1Labels = mixedMoment B raw15678step2 raw15678step2Labels := by
      have ha : raw15678step2 = raw15678step1 := by apply Matrix.ext; unfold raw15678step2 raw15678step1; decide +kernel
      have hl : raw15678step1Labels = labelEmbedding7 ∘ raw15678step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15678step1 raw15678step1Labels raw15678step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5402 node5402Labels := by rfl

def raw15679 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15679step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15679 raw15679Labels = mixedMoment B node5178 node5178Labels := by
  calc
    mixedMoment B raw15679 raw15679Labels = mixedMoment B raw15679step0 raw15679step0Labels := by
      have ha : raw15679step0 = (fun i j => raw15679 (permutation569 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15679step0 raw15679; decide +kernel
      have hl : raw15679step0Labels = raw15679Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15679 raw15679Labels permutation569 permutation3
    mixedMoment B raw15679step0 raw15679step0Labels = mixedMoment B raw15679step1 raw15679step1Labels := by
      have ha : raw15679step1 = raw15679step0 := by apply Matrix.ext; unfold raw15679step1 raw15679step0; decide +kernel
      have hl : raw15679step0Labels = labelEmbedding6 ∘ raw15679step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15679step0 raw15679step0Labels raw15679step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5178 node5178Labels := by rfl

def raw15680 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw15680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15680 raw15680Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw15680 raw15680Labels = mixedMoment B raw15680step0 raw15680step0Labels := by
      have ha : raw15680step0 = (fun i j => raw15680 (permutation667 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15680step0 raw15680; decide +kernel
      have hl : raw15680step0Labels = raw15680Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15680 raw15680Labels permutation667 permutation2
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw15681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15681step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15681step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15681step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15681step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15681 raw15681Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw15681 raw15681Labels = mixedMoment B raw15681step0 raw15681step0Labels := by
      have ha : raw15681step0 = (fun i j => raw15681 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15681step0 raw15681; decide +kernel
      have hl : raw15681step0Labels = raw15681Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15681 raw15681Labels permutation224 permutation4
    mixedMoment B raw15681step0 raw15681step0Labels = mixedMoment B raw15681step1 raw15681step1Labels := by
      have ha : raw15681step1 = -raw15681step0 := by apply Matrix.ext; change ∀ i j, raw15681step1 i j = -(raw15681step0 i j); unfold raw15681step1 raw15681step0; decide +kernel
      have hl : raw15681step1Labels = raw15681step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15681step1 raw15681step1Labels = mixedMoment B raw15681step2 raw15681step2Labels := by
      have ha : raw15681step2 = raw15681step1 := by apply Matrix.ext; unfold raw15681step2 raw15681step1; decide +kernel
      have hl : raw15681step1Labels = labelEmbedding7 ∘ raw15681step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15681step1 raw15681step1Labels raw15681step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

def raw15682 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw15682step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15682step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15682step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw15682step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15682 raw15682Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw15682 raw15682Labels = mixedMoment B raw15682step0 raw15682step0Labels := by
      have ha : raw15682step0 = (fun i j => raw15682 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15682step0 raw15682; decide +kernel
      have hl : raw15682step0Labels = raw15682Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15682 raw15682Labels permutation164 permutation4
    mixedMoment B raw15682step0 raw15682step0Labels = mixedMoment B raw15682step1 raw15682step1Labels := by
      have ha : raw15682step1 = -raw15682step0 := by apply Matrix.ext; change ∀ i j, raw15682step1 i j = -(raw15682step0 i j); unfold raw15682step1 raw15682step0; decide +kernel
      have hl : raw15682step1Labels = raw15682step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15682step1 raw15682step1Labels = mixedMoment B raw15682step2 raw15682step2Labels := by
      have ha : raw15682step2 = raw15682step1 := by apply Matrix.ext; unfold raw15682step2 raw15682step1; decide +kernel
      have hl : raw15682step1Labels = labelEmbedding7 ∘ raw15682step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15682step1 raw15682step1Labels raw15682step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw15683 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15683step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15683step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15683step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15683step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15683 raw15683Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw15683 raw15683Labels = mixedMoment B raw15683step0 raw15683step0Labels := by
      have hz : ∀ j, raw15683 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15683step0 = (fun i j => raw15683 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15683step0 raw15683; decide +kernel
      have hl : raw15683step0Labels = raw15683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15683 raw15683Labels permutation434 hz
    mixedMoment B raw15683step0 raw15683step0Labels = mixedMoment B raw15683step1 raw15683step1Labels := by
      have ha : raw15683step1 = (fun i j => raw15683step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15683step1 raw15683step0; decide +kernel
      have hl : raw15683step1Labels = raw15683step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15683step0 raw15683step0Labels permutation143 permutation4
    mixedMoment B raw15683step1 raw15683step1Labels = mixedMoment B raw15683step2 raw15683step2Labels := by
      have ha : raw15683step2 = raw15683step1 := by apply Matrix.ext; unfold raw15683step2 raw15683step1; decide +kernel
      have hl : raw15683step1Labels = labelEmbedding7 ∘ raw15683step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15683step1 raw15683step1Labels raw15683step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw15684 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw15684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15684step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15684 raw15684Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw15684 raw15684Labels = mixedMoment B raw15684step0 raw15684step0Labels := by
      have ha : raw15684step0 = (fun i j => raw15684 (permutation526 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15684step0 raw15684; decide +kernel
      have hl : raw15684step0Labels = raw15684Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15684 raw15684Labels permutation526 permutation3
    mixedMoment B raw15684step0 raw15684step0Labels = mixedMoment B raw15684step1 raw15684step1Labels := by
      have ha : raw15684step1 = raw15684step0 := by apply Matrix.ext; unfold raw15684step1 raw15684step0; decide +kernel
      have hl : raw15684step0Labels = labelEmbedding6 ∘ raw15684step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15684step0 raw15684step0Labels raw15684step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw15685 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15685Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15685 raw15685Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw15685 raw15685Labels = mixedMoment B raw15685step0 raw15685step0Labels := by
      have ha : raw15685step0 = (fun i j => raw15685 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15685step0 raw15685; decide +kernel
      have hl : raw15685step0Labels = raw15685Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15685 raw15685Labels permutation152 permutation6
    _ = mixedMoment B node3976 node3976Labels := by rfl

def raw15686 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15686Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15686step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15686 raw15686Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw15686 raw15686Labels = mixedMoment B raw15686step0 raw15686step0Labels := by
      have hz : ∀ j, raw15686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15686step0 = (fun i j => raw15686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15686step0 raw15686; decide +kernel
      have hl : raw15686step0Labels = raw15686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15686 raw15686Labels permutation346 hz
    mixedMoment B raw15686step0 raw15686step0Labels = mixedMoment B raw15686step1 raw15686step1Labels := by
      have ha : raw15686step1 = (fun i j => raw15686step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15686step1 raw15686step0; decide +kernel
      have hl : raw15686step1Labels = raw15686step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15686step0 raw15686step0Labels permutation32 permutation6
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw15687 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15687Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15687step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15687 raw15687Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw15687 raw15687Labels = mixedMoment B raw15687step0 raw15687step0Labels := by
      have hz : ∀ j, raw15687 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15687step0 = (fun i j => raw15687 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15687step0 raw15687; decide +kernel
      have hl : raw15687step0Labels = raw15687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15687 raw15687Labels permutation434 hz
    mixedMoment B raw15687step0 raw15687step0Labels = mixedMoment B raw15687step1 raw15687step1Labels := by
      have ha : raw15687step1 = (fun i j => raw15687step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15687step1 raw15687step0; decide +kernel
      have hl : raw15687step1Labels = raw15687step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15687step0 raw15687step0Labels permutation32 permutation6
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw15688 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15688Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15688 raw15688Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw15688 raw15688Labels = mixedMoment B raw15688step0 raw15688step0Labels := by
      have ha : raw15688step0 = (fun i j => raw15688 (permutation569 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15688step0 raw15688; decide +kernel
      have hl : raw15688step0Labels = raw15688Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15688 raw15688Labels permutation569 permutation3
    _ = mixedMoment B node2631 node2631Labels := by rfl

def raw15689 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15689Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15689 raw15689Labels = mixedMoment B node3938 node3938Labels := by
  calc
    mixedMoment B raw15689 raw15689Labels = mixedMoment B raw15689step0 raw15689step0Labels := by
      have ha : raw15689step0 = (fun i j => raw15689 (permutation569 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15689step0 raw15689; decide +kernel
      have hl : raw15689step0Labels = raw15689Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15689 raw15689Labels permutation569 permutation3
    _ = mixedMoment B node3938 node3938Labels := by rfl

def raw15690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15690Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15690 raw15690Labels = mixedMoment B node3566 node3566Labels := by
  calc
    mixedMoment B raw15690 raw15690Labels = mixedMoment B raw15690step0 raw15690step0Labels := by
      have ha : raw15690step0 = (fun i j => raw15690 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15690step0 raw15690; decide +kernel
      have hl : raw15690step0Labels = raw15690Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15690 raw15690Labels permutation152 permutation6
    _ = mixedMoment B node3566 node3566Labels := by rfl

def raw15691 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15691Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15691step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15691 raw15691Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw15691 raw15691Labels = mixedMoment B raw15691step0 raw15691step0Labels := by
      have hz : ∀ j, raw15691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15691step0 = (fun i j => raw15691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15691step0 raw15691; decide +kernel
      have hl : raw15691step0Labels = raw15691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15691 raw15691Labels permutation346 hz
    mixedMoment B raw15691step0 raw15691step0Labels = mixedMoment B raw15691step1 raw15691step1Labels := by
      have ha : raw15691step1 = (fun i j => raw15691step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15691step1 raw15691step0; decide +kernel
      have hl : raw15691step1Labels = raw15691step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15691step0 raw15691step0Labels permutation32 permutation6
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw15692 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15692Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15692step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15692step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15692 raw15692Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw15692 raw15692Labels = mixedMoment B raw15692step0 raw15692step0Labels := by
      have hz : ∀ j, raw15692 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15692step0 = (fun i j => raw15692 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15692step0 raw15692; decide +kernel
      have hl : raw15692step0Labels = raw15692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15692 raw15692Labels permutation434 hz
    mixedMoment B raw15692step0 raw15692step0Labels = mixedMoment B raw15692step1 raw15692step1Labels := by
      have ha : raw15692step1 = (fun i j => raw15692step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15692step1 raw15692step0; decide +kernel
      have hl : raw15692step1Labels = raw15692step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15692step0 raw15692step0Labels permutation32 permutation6
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw15693 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15693Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15693 raw15693Labels = mixedMoment B node2607 node2607Labels := by
  calc
    mixedMoment B raw15693 raw15693Labels = mixedMoment B raw15693step0 raw15693step0Labels := by
      have ha : raw15693step0 = (fun i j => raw15693 (permutation572 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15693step0 raw15693; decide +kernel
      have hl : raw15693step0Labels = raw15693Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15693 raw15693Labels permutation572 permutation3
    _ = mixedMoment B node2607 node2607Labels := by rfl

def raw15694 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15694Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw15694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15694 raw15694Labels = mixedMoment B node3878 node3878Labels := by
  calc
    mixedMoment B raw15694 raw15694Labels = mixedMoment B raw15694step0 raw15694step0Labels := by
      have ha : raw15694step0 = (fun i j => raw15694 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15694step0 raw15694; decide +kernel
      have hl : raw15694step0Labels = raw15694Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15694 raw15694Labels permutation152 permutation6
    _ = mixedMoment B node3878 node3878Labels := by rfl

def raw15695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15695Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15695 raw15695Labels = mixedMoment B node3527 node3527Labels := by
  calc
    mixedMoment B raw15695 raw15695Labels = mixedMoment B raw15695step0 raw15695step0Labels := by
      have ha : raw15695step0 = (fun i j => raw15695 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15695step0 raw15695; decide +kernel
      have hl : raw15695step0Labels = raw15695Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15695 raw15695Labels permutation158 permutation6
    _ = mixedMoment B node3527 node3527Labels := by rfl

def raw15696 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15696Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15696 raw15696Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw15696 raw15696Labels = mixedMoment B raw15696step0 raw15696step0Labels := by
      have ha : raw15696step0 = (fun i j => raw15696 (permutation386 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15696step0 raw15696; decide +kernel
      have hl : raw15696step0Labels = raw15696Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15696 raw15696Labels permutation386 permutation3
    mixedMoment B raw15696step0 raw15696step0Labels = mixedMoment B raw15696step1 raw15696step1Labels := by
      have ha : raw15696step1 = -raw15696step0 := by apply Matrix.ext; change ∀ i j, raw15696step1 i j = -(raw15696step0 i j); unfold raw15696step1 raw15696step0; decide +kernel
      have hl : raw15696step1Labels = raw15696step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3802 node3802Labels := by rfl

def raw15697 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15697Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15697step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15697step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15697step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15697step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15697 raw15697Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw15697 raw15697Labels = mixedMoment B raw15697step0 raw15697step0Labels := by
      have hz : ∀ j, raw15697 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15697step0 = (fun i j => raw15697 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15697step0 raw15697; decide +kernel
      have hl : raw15697step0Labels = raw15697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15697 raw15697Labels permutation434 hz
    mixedMoment B raw15697step0 raw15697step0Labels = mixedMoment B raw15697step1 raw15697step1Labels := by
      have ha : raw15697step1 = (fun i j => raw15697step0 (permutation87 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15697step1 raw15697step0; decide +kernel
      have hl : raw15697step1Labels = raw15697step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15697step0 raw15697step0Labels permutation87 permutation3
    mixedMoment B raw15697step1 raw15697step1Labels = mixedMoment B raw15697step2 raw15697step2Labels := by
      have ha : raw15697step2 = -raw15697step1 := by apply Matrix.ext; change ∀ i j, raw15697step2 i j = -(raw15697step1 i j); unfold raw15697step2 raw15697step1; decide +kernel
      have hl : raw15697step2Labels = raw15697step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw15698 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15698Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15698 raw15698Labels = mixedMoment B node2606 node2606Labels := by
  calc
    mixedMoment B raw15698 raw15698Labels = mixedMoment B raw15698step0 raw15698step0Labels := by
      have ha : raw15698step0 = (fun i j => raw15698 (permutation570 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15698step0 raw15698; decide +kernel
      have hl : raw15698step0Labels = raw15698Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15698 raw15698Labels permutation570 permutation3
    _ = mixedMoment B node2606 node2606Labels := by rfl

def raw15699 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15699Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15699step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15699 raw15699Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw15699 raw15699Labels = mixedMoment B raw15699step0 raw15699step0Labels := by
      have ha : raw15699step0 = (fun i j => raw15699 (permutation386 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15699step0 raw15699; decide +kernel
      have hl : raw15699step0Labels = raw15699Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15699 raw15699Labels permutation386 permutation3
    mixedMoment B raw15699step0 raw15699step0Labels = mixedMoment B raw15699step1 raw15699step1Labels := by
      have ha : raw15699step1 = -raw15699step0 := by apply Matrix.ext; change ∀ i j, raw15699step1 i j = -(raw15699step0 i j); unfold raw15699step1 raw15699step0; decide +kernel
      have hl : raw15699step1Labels = raw15699step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3780 node3780Labels := by rfl

def raw15700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15700Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15700 raw15700Labels = mixedMoment B node3527 node3527Labels := by
  calc
    mixedMoment B raw15700 raw15700Labels = mixedMoment B raw15700step0 raw15700step0Labels := by
      have ha : raw15700step0 = (fun i j => raw15700 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15700step0 raw15700; decide +kernel
      have hl : raw15700step0Labels = raw15700Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15700 raw15700Labels permutation152 permutation6
    _ = mixedMoment B node3527 node3527Labels := by rfl

def raw15701 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15701Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15701step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15701step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15701step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15701 raw15701Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw15701 raw15701Labels = mixedMoment B raw15701step0 raw15701step0Labels := by
      have ha : raw15701step0 = (fun i j => raw15701 (permutation471 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15701step0 raw15701; decide +kernel
      have hl : raw15701step0Labels = raw15701Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15701 raw15701Labels permutation471 permutation3
    mixedMoment B raw15701step0 raw15701step0Labels = mixedMoment B raw15701step1 raw15701step1Labels := by
      have ha : raw15701step1 = -raw15701step0 := by apply Matrix.ext; change ∀ i j, raw15701step1 i j = -(raw15701step0 i j); unfold raw15701step1 raw15701step0; decide +kernel
      have hl : raw15701step1Labels = raw15701step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3802 node3802Labels := by rfl

def raw15702 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15702Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15702step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15702step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15702step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw15702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15702step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw15702step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15702 raw15702Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw15702 raw15702Labels = mixedMoment B raw15702step0 raw15702step0Labels := by
      have hz : ∀ j, raw15702 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15702step0 = (fun i j => raw15702 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15702step0 raw15702; decide +kernel
      have hl : raw15702step0Labels = raw15702Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15702 raw15702Labels permutation346 hz
    mixedMoment B raw15702step0 raw15702step0Labels = mixedMoment B raw15702step1 raw15702step1Labels := by
      have ha : raw15702step1 = (fun i j => raw15702step0 (permutation87 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15702step1 raw15702step0; decide +kernel
      have hl : raw15702step1Labels = raw15702step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15702step0 raw15702step0Labels permutation87 permutation3
    mixedMoment B raw15702step1 raw15702step1Labels = mixedMoment B raw15702step2 raw15702step2Labels := by
      have ha : raw15702step2 = -raw15702step1 := by apply Matrix.ext; change ∀ i j, raw15702step2 i j = -(raw15702step1 i j); unfold raw15702step2 raw15702step1; decide +kernel
      have hl : raw15702step2Labels = raw15702step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw15703 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15703Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15703step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15703step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15703 raw15703Labels = mixedMoment B node2606 node2606Labels := by
  calc
    mixedMoment B raw15703 raw15703Labels = mixedMoment B raw15703step0 raw15703step0Labels := by
      have ha : raw15703step0 = (fun i j => raw15703 (permutation569 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15703step0 raw15703; decide +kernel
      have hl : raw15703step0Labels = raw15703Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15703 raw15703Labels permutation569 permutation3
    _ = mixedMoment B node2606 node2606Labels := by rfl

def raw15704 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw15704step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw15704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15704 raw15704Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw15704 raw15704Labels = mixedMoment B raw15704step0 raw15704step0Labels := by
      have ha : raw15704step0 = (fun i j => raw15704 (permutation471 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15704step0 raw15704; decide +kernel
      have hl : raw15704step0Labels = raw15704Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15704 raw15704Labels permutation471 permutation3
    mixedMoment B raw15704step0 raw15704step0Labels = mixedMoment B raw15704step1 raw15704step1Labels := by
      have ha : raw15704step1 = -raw15704step0 := by apply Matrix.ext; change ∀ i j, raw15704step1 i j = -(raw15704step0 i j); unfold raw15704step1 raw15704step0; decide +kernel
      have hl : raw15704step1Labels = raw15704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3780 node3780Labels := by rfl

def raw15705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15705step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15705 raw15705Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw15705 raw15705Labels = mixedMoment B raw15705step0 raw15705step0Labels := by
      have ha : raw15705step0 = (fun i j => raw15705 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15705step0 raw15705; decide +kernel
      have hl : raw15705step0Labels = raw15705Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15705 raw15705Labels permutation152 permutation6
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw15706 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15706 raw15706Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw15706 raw15706Labels = mixedMoment B raw15706step0 raw15706step0Labels := by
      have ha : raw15706step0 = (fun i j => raw15706 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15706step0 raw15706; decide +kernel
      have hl : raw15706step0Labels = raw15706Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15706 raw15706Labels permutation152 permutation6
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw15707 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15707 raw15707Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw15707 raw15707Labels = mixedMoment B raw15707step0 raw15707step0Labels := by
      have hz : ∀ j, raw15707 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15707step0 = (fun i j => raw15707 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15707step0 raw15707; decide +kernel
      have hl : raw15707step0Labels = raw15707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15707 raw15707Labels permutation346 hz
    mixedMoment B raw15707step0 raw15707step0Labels = mixedMoment B raw15707step1 raw15707step1Labels := by
      have ha : raw15707step1 = (fun i j => raw15707step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15707step1 raw15707step0; decide +kernel
      have hl : raw15707step1Labels = raw15707step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15707step0 raw15707step0Labels permutation32 permutation6
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw15708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15708 raw15708Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw15708 raw15708Labels = mixedMoment B raw15708step0 raw15708step0Labels := by
      have hz : ∀ j, raw15708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15708step0 = (fun i j => raw15708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15708step0 raw15708; decide +kernel
      have hl : raw15708step0Labels = raw15708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15708 raw15708Labels permutation434 hz
    mixedMoment B raw15708step0 raw15708step0Labels = mixedMoment B raw15708step1 raw15708step1Labels := by
      have ha : raw15708step1 = (fun i j => raw15708step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15708step1 raw15708step0; decide +kernel
      have hl : raw15708step1Labels = raw15708step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15708step0 raw15708step0Labels permutation32 permutation6
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw15709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15709step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15709 raw15709Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw15709 raw15709Labels = mixedMoment B raw15709step0 raw15709step0Labels := by
      have ha : raw15709step0 = (fun i j => raw15709 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15709step0 raw15709; decide +kernel
      have hl : raw15709step0Labels = raw15709Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15709 raw15709Labels permutation152 permutation6
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw15710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15710Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15710step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15710 raw15710Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw15710 raw15710Labels = mixedMoment B raw15710step0 raw15710step0Labels := by
      have ha : raw15710step0 = (fun i j => raw15710 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15710step0 raw15710; decide +kernel
      have hl : raw15710step0Labels = raw15710Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15710 raw15710Labels permutation152 permutation6
    _ = mixedMoment B node3524 node3524Labels := by rfl

def raw15711 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15711Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15711step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15711 raw15711Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw15711 raw15711Labels = mixedMoment B raw15711step0 raw15711step0Labels := by
      have ha : raw15711step0 = (fun i j => raw15711 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15711step0 raw15711; decide +kernel
      have hl : raw15711step0Labels = raw15711Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15711 raw15711Labels permutation152 permutation6
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw15712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15712Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15712step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15712step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15712 raw15712Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15712 raw15712Labels = mixedMoment B raw15712step0 raw15712step0Labels := by
      have hz : ∀ j, raw15712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15712step0 = (fun i j => raw15712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15712step0 raw15712; decide +kernel
      have hl : raw15712step0Labels = raw15712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15712 raw15712Labels permutation346 hz
    mixedMoment B raw15712step0 raw15712step0Labels = mixedMoment B raw15712step1 raw15712step1Labels := by
      have ha : raw15712step1 = (fun i j => raw15712step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15712step1 raw15712step0; decide +kernel
      have hl : raw15712step1Labels = raw15712step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15712step0 raw15712step0Labels permutation32 permutation6
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw15713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15713Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15713step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15713step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw15713step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15713 raw15713Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw15713 raw15713Labels = mixedMoment B raw15713step0 raw15713step0Labels := by
      have hz : ∀ j, raw15713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15713step0 = (fun i j => raw15713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15713step0 raw15713; decide +kernel
      have hl : raw15713step0Labels = raw15713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15713 raw15713Labels permutation434 hz
    mixedMoment B raw15713step0 raw15713step0Labels = mixedMoment B raw15713step1 raw15713step1Labels := by
      have ha : raw15713step1 = (fun i j => raw15713step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15713step1 raw15713step0; decide +kernel
      have hl : raw15713step1Labels = raw15713step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15713step0 raw15713step0Labels permutation32 permutation6
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw15714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw15714Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15714step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15714step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15714 raw15714Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw15714 raw15714Labels = mixedMoment B raw15714step0 raw15714step0Labels := by
      have ha : raw15714step0 = (fun i j => raw15714 (permutation526 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15714step0 raw15714; decide +kernel
      have hl : raw15714step0Labels = raw15714Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15714 raw15714Labels permutation526 permutation3
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw15715 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15715step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15715step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15715 raw15715Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw15715 raw15715Labels = mixedMoment B raw15715step0 raw15715step0Labels := by
      have ha : raw15715step0 = (fun i j => raw15715 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15715step0 raw15715; decide +kernel
      have hl : raw15715step0Labels = raw15715Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15715 raw15715Labels permutation682 permutation7
    mixedMoment B raw15715step0 raw15715step0Labels = mixedMoment B raw15715step1 raw15715step1Labels := by
      have ha : raw15715step1 = -raw15715step0 := by apply Matrix.ext; change ∀ i j, raw15715step1 i j = -(raw15715step0 i j); unfold raw15715step1 raw15715step0; decide +kernel
      have hl : raw15715step1Labels = raw15715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15715step1 raw15715step1Labels = mixedMoment B raw15715step2 raw15715step2Labels := by
      have ha : raw15715step2 = raw15715step1 := by apply Matrix.ext; unfold raw15715step2 raw15715step1; decide +kernel
      have hl : raw15715step1Labels = labelEmbedding1 ∘ raw15715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15715step1 raw15715step1Labels raw15715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3953 node3953Labels := by rfl

def raw15716 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15716step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15716step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15716step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15716step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15716step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15716step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15716step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15716 raw15716Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw15716 raw15716Labels = mixedMoment B raw15716step0 raw15716step0Labels := by
      have hz : ∀ j, raw15716 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15716step0 = (fun i j => raw15716 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15716step0 raw15716; decide +kernel
      have hl : raw15716step0Labels = raw15716Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15716 raw15716Labels permutation434 hz
    mixedMoment B raw15716step0 raw15716step0Labels = mixedMoment B raw15716step1 raw15716step1Labels := by
      have ha : raw15716step1 = (fun i j => raw15716step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15716step1 raw15716step0; decide +kernel
      have hl : raw15716step1Labels = raw15716step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15716step0 raw15716step0Labels permutation151 permutation7
    mixedMoment B raw15716step1 raw15716step1Labels = mixedMoment B raw15716step2 raw15716step2Labels := by
      have ha : raw15716step2 = -raw15716step1 := by apply Matrix.ext; change ∀ i j, raw15716step2 i j = -(raw15716step1 i j); unfold raw15716step2 raw15716step1; decide +kernel
      have hl : raw15716step2Labels = raw15716step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15716step2 raw15716step2Labels = mixedMoment B raw15716step3 raw15716step3Labels := by
      have ha : raw15716step3 = raw15716step2 := by apply Matrix.ext; unfold raw15716step3 raw15716step2; decide +kernel
      have hl : raw15716step2Labels = labelEmbedding1 ∘ raw15716step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15716step2 raw15716step2Labels raw15716step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw15717 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15717step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15717step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15717 raw15717Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw15717 raw15717Labels = mixedMoment B raw15717step0 raw15717step0Labels := by
      have ha : raw15717step0 = (fun i j => raw15717 (permutation524 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15717step0 raw15717; decide +kernel
      have hl : raw15717step0Labels = raw15717Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15717 raw15717Labels permutation524 permutation5
    mixedMoment B raw15717step0 raw15717step0Labels = mixedMoment B raw15717step1 raw15717step1Labels := by
      have ha : raw15717step1 = -raw15717step0 := by apply Matrix.ext; change ∀ i j, raw15717step1 i j = -(raw15717step0 i j); unfold raw15717step1 raw15717step0; decide +kernel
      have hl : raw15717step1Labels = raw15717step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15717step1 raw15717step1Labels = mixedMoment B raw15717step2 raw15717step2Labels := by
      have ha : raw15717step2 = raw15717step1 := by apply Matrix.ext; unfold raw15717step2 raw15717step1; decide +kernel
      have hl : raw15717step1Labels = labelEmbedding1 ∘ raw15717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15717step1 raw15717step1Labels raw15717step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw15718 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15718step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15718step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15718step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15718 raw15718Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw15718 raw15718Labels = mixedMoment B raw15718step0 raw15718step0Labels := by
      have ha : raw15718step0 = (fun i j => raw15718 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15718step0 raw15718; decide +kernel
      have hl : raw15718step0Labels = raw15718Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15718 raw15718Labels permutation682 permutation7
    mixedMoment B raw15718step0 raw15718step0Labels = mixedMoment B raw15718step1 raw15718step1Labels := by
      have ha : raw15718step1 = -raw15718step0 := by apply Matrix.ext; change ∀ i j, raw15718step1 i j = -(raw15718step0 i j); unfold raw15718step1 raw15718step0; decide +kernel
      have hl : raw15718step1Labels = raw15718step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15718step1 raw15718step1Labels = mixedMoment B raw15718step2 raw15718step2Labels := by
      have ha : raw15718step2 = raw15718step1 := by apply Matrix.ext; unfold raw15718step2 raw15718step1; decide +kernel
      have hl : raw15718step1Labels = labelEmbedding1 ∘ raw15718step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15718step1 raw15718step1Labels raw15718step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw15719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15719step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15719 raw15719Labels = mixedMoment B node2874 node2874Labels := by
  calc
    mixedMoment B raw15719 raw15719Labels = mixedMoment B raw15719step0 raw15719step0Labels := by
      have ha : raw15719step0 = (fun i j => raw15719 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15719step0 raw15719; decide +kernel
      have hl : raw15719step0Labels = raw15719Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15719 raw15719Labels permutation243 permutation5
    mixedMoment B raw15719step0 raw15719step0Labels = mixedMoment B raw15719step1 raw15719step1Labels := by
      have ha : raw15719step1 = -raw15719step0 := by apply Matrix.ext; change ∀ i j, raw15719step1 i j = -(raw15719step0 i j); unfold raw15719step1 raw15719step0; decide +kernel
      have hl : raw15719step1Labels = raw15719step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15719step1 raw15719step1Labels = mixedMoment B raw15719step2 raw15719step2Labels := by
      have ha : raw15719step2 = raw15719step1 := by apply Matrix.ext; unfold raw15719step2 raw15719step1; decide +kernel
      have hl : raw15719step1Labels = labelEmbedding1 ∘ raw15719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15719step1 raw15719step1Labels raw15719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2874 node2874Labels := by rfl

def raw15720 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15720 raw15720Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw15720 raw15720Labels = mixedMoment B raw15720step0 raw15720step0Labels := by
      have hz : ∀ j, raw15720 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15720step0 = (fun i j => raw15720 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15720step0 raw15720; decide +kernel
      have hl : raw15720step0Labels = raw15720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15720 raw15720Labels permutation434 hz
    mixedMoment B raw15720step0 raw15720step0Labels = mixedMoment B raw15720step1 raw15720step1Labels := by
      have ha : raw15720step1 = (fun i j => raw15720step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15720step1 raw15720step0; decide +kernel
      have hl : raw15720step1Labels = raw15720step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15720step0 raw15720step0Labels permutation151 permutation7
    mixedMoment B raw15720step1 raw15720step1Labels = mixedMoment B raw15720step2 raw15720step2Labels := by
      have ha : raw15720step2 = -raw15720step1 := by apply Matrix.ext; change ∀ i j, raw15720step2 i j = -(raw15720step1 i j); unfold raw15720step2 raw15720step1; decide +kernel
      have hl : raw15720step2Labels = raw15720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15720step2 raw15720step2Labels = mixedMoment B raw15720step3 raw15720step3Labels := by
      have ha : raw15720step3 = raw15720step2 := by apply Matrix.ext; unfold raw15720step3 raw15720step2; decide +kernel
      have hl : raw15720step2Labels = labelEmbedding1 ∘ raw15720step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15720step2 raw15720step2Labels raw15720step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw15721 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15721 raw15721Labels = mixedMoment B node3384 node3384Labels := by
  calc
    mixedMoment B raw15721 raw15721Labels = mixedMoment B raw15721step0 raw15721step0Labels := by
      have ha : raw15721step0 = (fun i j => raw15721 (permutation528 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15721step0 raw15721; decide +kernel
      have hl : raw15721step0Labels = raw15721Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15721 raw15721Labels permutation528 permutation5
    mixedMoment B raw15721step0 raw15721step0Labels = mixedMoment B raw15721step1 raw15721step1Labels := by
      have ha : raw15721step1 = -raw15721step0 := by apply Matrix.ext; change ∀ i j, raw15721step1 i j = -(raw15721step0 i j); unfold raw15721step1 raw15721step0; decide +kernel
      have hl : raw15721step1Labels = raw15721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15721step1 raw15721step1Labels = mixedMoment B raw15721step2 raw15721step2Labels := by
      have ha : raw15721step2 = raw15721step1 := by apply Matrix.ext; unfold raw15721step2 raw15721step1; decide +kernel
      have hl : raw15721step1Labels = labelEmbedding1 ∘ raw15721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15721step1 raw15721step1Labels raw15721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3384 node3384Labels := by rfl

def raw15722 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15722step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15722step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15722step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15722step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15722step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15722 raw15722Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw15722 raw15722Labels = mixedMoment B raw15722step0 raw15722step0Labels := by
      have ha : raw15722step0 = (fun i j => raw15722 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15722step0 raw15722; decide +kernel
      have hl : raw15722step0Labels = raw15722Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15722 raw15722Labels permutation682 permutation7
    mixedMoment B raw15722step0 raw15722step0Labels = mixedMoment B raw15722step1 raw15722step1Labels := by
      have ha : raw15722step1 = -raw15722step0 := by apply Matrix.ext; change ∀ i j, raw15722step1 i j = -(raw15722step0 i j); unfold raw15722step1 raw15722step0; decide +kernel
      have hl : raw15722step1Labels = raw15722step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15722step1 raw15722step1Labels = mixedMoment B raw15722step2 raw15722step2Labels := by
      have ha : raw15722step2 = raw15722step1 := by apply Matrix.ext; unfold raw15722step2 raw15722step1; decide +kernel
      have hl : raw15722step1Labels = labelEmbedding1 ∘ raw15722step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15722step1 raw15722step1Labels raw15722step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3759 node3759Labels := by rfl

def raw15723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15723step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15723step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15723step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15723step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15723step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15723step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15723 raw15723Labels = mixedMoment B node2860 node2860Labels := by
  calc
    mixedMoment B raw15723 raw15723Labels = mixedMoment B raw15723step0 raw15723step0Labels := by
      have ha : raw15723step0 = (fun i j => raw15723 (permutation229 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15723step0 raw15723; decide +kernel
      have hl : raw15723step0Labels = raw15723Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15723 raw15723Labels permutation229 permutation5
    mixedMoment B raw15723step0 raw15723step0Labels = mixedMoment B raw15723step1 raw15723step1Labels := by
      have ha : raw15723step1 = -raw15723step0 := by apply Matrix.ext; change ∀ i j, raw15723step1 i j = -(raw15723step0 i j); unfold raw15723step1 raw15723step0; decide +kernel
      have hl : raw15723step1Labels = raw15723step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15723step1 raw15723step1Labels = mixedMoment B raw15723step2 raw15723step2Labels := by
      have ha : raw15723step2 = raw15723step1 := by apply Matrix.ext; unfold raw15723step2 raw15723step1; decide +kernel
      have hl : raw15723step1Labels = labelEmbedding1 ∘ raw15723step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15723step1 raw15723step1Labels raw15723step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2860 node2860Labels := by rfl

def raw15724 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15724step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15724step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15724step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15724step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15724 raw15724Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw15724 raw15724Labels = mixedMoment B raw15724step0 raw15724step0Labels := by
      have ha : raw15724step0 = (fun i j => raw15724 (permutation397 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15724step0 raw15724; decide +kernel
      have hl : raw15724step0Labels = raw15724Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15724 raw15724Labels permutation397 permutation5
    mixedMoment B raw15724step0 raw15724step0Labels = mixedMoment B raw15724step1 raw15724step1Labels := by
      have ha : raw15724step1 = raw15724step0 := by apply Matrix.ext; unfold raw15724step1 raw15724step0; decide +kernel
      have hl : raw15724step0Labels = labelEmbedding1 ∘ raw15724step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15724step0 raw15724step0Labels raw15724step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw15725 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15725step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15725 raw15725Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw15725 raw15725Labels = mixedMoment B raw15725step0 raw15725step0Labels := by
      have hz : ∀ j, raw15725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15725step0 = (fun i j => raw15725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15725step0 raw15725; decide +kernel
      have hl : raw15725step0Labels = raw15725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15725 raw15725Labels permutation434 hz
    mixedMoment B raw15725step0 raw15725step0Labels = mixedMoment B raw15725step1 raw15725step1Labels := by
      have ha : raw15725step1 = (fun i j => raw15725step0 (permutation101 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15725step1 raw15725step0; decide +kernel
      have hl : raw15725step1Labels = raw15725step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15725step0 raw15725step0Labels permutation101 permutation5
    mixedMoment B raw15725step1 raw15725step1Labels = mixedMoment B raw15725step2 raw15725step2Labels := by
      have ha : raw15725step2 = raw15725step1 := by apply Matrix.ext; unfold raw15725step2 raw15725step1; decide +kernel
      have hl : raw15725step1Labels = labelEmbedding1 ∘ raw15725step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15725step1 raw15725step1Labels raw15725step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw15726 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15726step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15726 raw15726Labels = mixedMoment B node3374 node3374Labels := by
  calc
    mixedMoment B raw15726 raw15726Labels = mixedMoment B raw15726step0 raw15726step0Labels := by
      have ha : raw15726step0 = (fun i j => raw15726 (permutation525 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15726step0 raw15726; decide +kernel
      have hl : raw15726step0Labels = raw15726Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15726 raw15726Labels permutation525 permutation5
    mixedMoment B raw15726step0 raw15726step0Labels = mixedMoment B raw15726step1 raw15726step1Labels := by
      have ha : raw15726step1 = -raw15726step0 := by apply Matrix.ext; change ∀ i j, raw15726step1 i j = -(raw15726step0 i j); unfold raw15726step1 raw15726step0; decide +kernel
      have hl : raw15726step1Labels = raw15726step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15726step1 raw15726step1Labels = mixedMoment B raw15726step2 raw15726step2Labels := by
      have ha : raw15726step2 = raw15726step1 := by apply Matrix.ext; unfold raw15726step2 raw15726step1; decide +kernel
      have hl : raw15726step1Labels = labelEmbedding1 ∘ raw15726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15726step1 raw15726step1Labels raw15726step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3374 node3374Labels := by rfl

def raw15727 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15727step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15727step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15727step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15727step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15727step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15727 raw15727Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw15727 raw15727Labels = mixedMoment B raw15727step0 raw15727step0Labels := by
      have ha : raw15727step0 = (fun i j => raw15727 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15727step0 raw15727; decide +kernel
      have hl : raw15727step0Labels = raw15727Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15727 raw15727Labels permutation688 permutation7
    mixedMoment B raw15727step0 raw15727step0Labels = mixedMoment B raw15727step1 raw15727step1Labels := by
      have ha : raw15727step1 = -raw15727step0 := by apply Matrix.ext; change ∀ i j, raw15727step1 i j = -(raw15727step0 i j); unfold raw15727step1 raw15727step0; decide +kernel
      have hl : raw15727step1Labels = raw15727step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15727step1 raw15727step1Labels = mixedMoment B raw15727step2 raw15727step2Labels := by
      have ha : raw15727step2 = raw15727step1 := by apply Matrix.ext; unfold raw15727step2 raw15727step1; decide +kernel
      have hl : raw15727step1Labels = labelEmbedding1 ∘ raw15727step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15727step1 raw15727step1Labels raw15727step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw15728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15728step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15728step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15728step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15728step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15728step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15728step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15728 raw15728Labels = mixedMoment B node2860 node2860Labels := by
  calc
    mixedMoment B raw15728 raw15728Labels = mixedMoment B raw15728step0 raw15728step0Labels := by
      have ha : raw15728step0 = (fun i j => raw15728 (permutation228 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15728step0 raw15728; decide +kernel
      have hl : raw15728step0Labels = raw15728Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15728 raw15728Labels permutation228 permutation5
    mixedMoment B raw15728step0 raw15728step0Labels = mixedMoment B raw15728step1 raw15728step1Labels := by
      have ha : raw15728step1 = -raw15728step0 := by apply Matrix.ext; change ∀ i j, raw15728step1 i j = -(raw15728step0 i j); unfold raw15728step1 raw15728step0; decide +kernel
      have hl : raw15728step1Labels = raw15728step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15728step1 raw15728step1Labels = mixedMoment B raw15728step2 raw15728step2Labels := by
      have ha : raw15728step2 = raw15728step1 := by apply Matrix.ext; unfold raw15728step2 raw15728step1; decide +kernel
      have hl : raw15728step1Labels = labelEmbedding1 ∘ raw15728step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15728step1 raw15728step1Labels raw15728step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2860 node2860Labels := by rfl

def raw15729 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15729step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15729step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15729step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15729step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15729 raw15729Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw15729 raw15729Labels = mixedMoment B raw15729step0 raw15729step0Labels := by
      have ha : raw15729step0 = (fun i j => raw15729 (permutation482 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15729step0 raw15729; decide +kernel
      have hl : raw15729step0Labels = raw15729Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15729 raw15729Labels permutation482 permutation5
    mixedMoment B raw15729step0 raw15729step0Labels = mixedMoment B raw15729step1 raw15729step1Labels := by
      have ha : raw15729step1 = raw15729step0 := by apply Matrix.ext; unfold raw15729step1 raw15729step0; decide +kernel
      have hl : raw15729step0Labels = labelEmbedding1 ∘ raw15729step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15729step0 raw15729step0Labels raw15729step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw15730 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15730step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15730step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15730step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15730step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw15730step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15730 raw15730Labels = mixedMoment B node3374 node3374Labels := by
  calc
    mixedMoment B raw15730 raw15730Labels = mixedMoment B raw15730step0 raw15730step0Labels := by
      have ha : raw15730step0 = (fun i j => raw15730 (permutation524 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15730step0 raw15730; decide +kernel
      have hl : raw15730step0Labels = raw15730Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15730 raw15730Labels permutation524 permutation5
    mixedMoment B raw15730step0 raw15730step0Labels = mixedMoment B raw15730step1 raw15730step1Labels := by
      have ha : raw15730step1 = -raw15730step0 := by apply Matrix.ext; change ∀ i j, raw15730step1 i j = -(raw15730step0 i j); unfold raw15730step1 raw15730step0; decide +kernel
      have hl : raw15730step1Labels = raw15730step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15730step1 raw15730step1Labels = mixedMoment B raw15730step2 raw15730step2Labels := by
      have ha : raw15730step2 = raw15730step1 := by apply Matrix.ext; unfold raw15730step2 raw15730step1; decide +kernel
      have hl : raw15730step1Labels = labelEmbedding1 ∘ raw15730step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15730step1 raw15730step1Labels raw15730step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3374 node3374Labels := by rfl

def raw15731 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15731step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15731 raw15731Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw15731 raw15731Labels = mixedMoment B raw15731step0 raw15731step0Labels := by
      have ha : raw15731step0 = (fun i j => raw15731 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15731step0 raw15731; decide +kernel
      have hl : raw15731step0Labels = raw15731Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15731 raw15731Labels permutation682 permutation7
    mixedMoment B raw15731step0 raw15731step0Labels = mixedMoment B raw15731step1 raw15731step1Labels := by
      have ha : raw15731step1 = -raw15731step0 := by apply Matrix.ext; change ∀ i j, raw15731step1 i j = -(raw15731step0 i j); unfold raw15731step1 raw15731step0; decide +kernel
      have hl : raw15731step1Labels = raw15731step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15731step1 raw15731step1Labels = mixedMoment B raw15731step2 raw15731step2Labels := by
      have ha : raw15731step2 = raw15731step1 := by apply Matrix.ext; unfold raw15731step2 raw15731step1; decide +kernel
      have hl : raw15731step1Labels = labelEmbedding1 ∘ raw15731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15731step1 raw15731step1Labels raw15731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw15732 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15732 raw15732Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw15732 raw15732Labels = mixedMoment B raw15732step0 raw15732step0Labels := by
      have hz : ∀ j, raw15732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15732step0 = (fun i j => raw15732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15732step0 raw15732; decide +kernel
      have hl : raw15732step0Labels = raw15732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15732 raw15732Labels permutation346 hz
    mixedMoment B raw15732step0 raw15732step0Labels = mixedMoment B raw15732step1 raw15732step1Labels := by
      have ha : raw15732step1 = (fun i j => raw15732step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15732step1 raw15732step0; decide +kernel
      have hl : raw15732step1Labels = raw15732step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15732step0 raw15732step0Labels permutation151 permutation7
    mixedMoment B raw15732step1 raw15732step1Labels = mixedMoment B raw15732step2 raw15732step2Labels := by
      have ha : raw15732step2 = -raw15732step1 := by apply Matrix.ext; change ∀ i j, raw15732step2 i j = -(raw15732step1 i j); unfold raw15732step2 raw15732step1; decide +kernel
      have hl : raw15732step2Labels = raw15732step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15732step2 raw15732step2Labels = mixedMoment B raw15732step3 raw15732step3Labels := by
      have ha : raw15732step3 = raw15732step2 := by apply Matrix.ext; unfold raw15732step3 raw15732step2; decide +kernel
      have hl : raw15732step2Labels = labelEmbedding1 ∘ raw15732step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15732step2 raw15732step2Labels raw15732step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw15733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15733step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15733step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15733step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15733step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15733step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15733 raw15733Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw15733 raw15733Labels = mixedMoment B raw15733step0 raw15733step0Labels := by
      have ha : raw15733step0 = (fun i j => raw15733 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15733step0 raw15733; decide +kernel
      have hl : raw15733step0Labels = raw15733Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15733 raw15733Labels permutation224 permutation5
    mixedMoment B raw15733step0 raw15733step0Labels = mixedMoment B raw15733step1 raw15733step1Labels := by
      have ha : raw15733step1 = -raw15733step0 := by apply Matrix.ext; change ∀ i j, raw15733step1 i j = -(raw15733step0 i j); unfold raw15733step1 raw15733step0; decide +kernel
      have hl : raw15733step1Labels = raw15733step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15733step1 raw15733step1Labels = mixedMoment B raw15733step2 raw15733step2Labels := by
      have ha : raw15733step2 = raw15733step1 := by apply Matrix.ext; unfold raw15733step2 raw15733step1; decide +kernel
      have hl : raw15733step1Labels = labelEmbedding1 ∘ raw15733step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15733step1 raw15733step1Labels raw15733step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2864 node2864Labels := by rfl

def raw15734 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15734step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15734step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15734step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15734step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15734step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15734 raw15734Labels = mixedMoment B node4023 node4023Labels := by
  calc
    mixedMoment B raw15734 raw15734Labels = mixedMoment B raw15734step0 raw15734step0Labels := by
      have ha : raw15734step0 = (fun i j => raw15734 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15734step0 raw15734; decide +kernel
      have hl : raw15734step0Labels = raw15734Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15734 raw15734Labels permutation224 permutation5
    mixedMoment B raw15734step0 raw15734step0Labels = mixedMoment B raw15734step1 raw15734step1Labels := by
      have ha : raw15734step1 = -raw15734step0 := by apply Matrix.ext; change ∀ i j, raw15734step1 i j = -(raw15734step0 i j); unfold raw15734step1 raw15734step0; decide +kernel
      have hl : raw15734step1Labels = raw15734step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15734step1 raw15734step1Labels = mixedMoment B raw15734step2 raw15734step2Labels := by
      have ha : raw15734step2 = raw15734step1 := by apply Matrix.ext; unfold raw15734step2 raw15734step1; decide +kernel
      have hl : raw15734step1Labels = labelEmbedding1 ∘ raw15734step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15734step1 raw15734step1Labels raw15734step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4023 node4023Labels := by rfl

def raw15735 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw15735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15735 raw15735Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw15735 raw15735Labels = mixedMoment B raw15735step0 raw15735step0Labels := by
      have hz : ∀ j, raw15735 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15735step0 = (fun i j => raw15735 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15735step0 raw15735; decide +kernel
      have hl : raw15735step0Labels = raw15735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15735 raw15735Labels permutation434 hz
    mixedMoment B raw15735step0 raw15735step0Labels = mixedMoment B raw15735step1 raw15735step1Labels := by
      have ha : raw15735step1 = (fun i j => raw15735step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15735step1 raw15735step0; decide +kernel
      have hl : raw15735step1Labels = raw15735step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15735step0 raw15735step0Labels permutation44 permutation5
    mixedMoment B raw15735step1 raw15735step1Labels = mixedMoment B raw15735step2 raw15735step2Labels := by
      have ha : raw15735step2 = -raw15735step1 := by apply Matrix.ext; change ∀ i j, raw15735step2 i j = -(raw15735step1 i j); unfold raw15735step2 raw15735step1; decide +kernel
      have hl : raw15735step2Labels = raw15735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15735step2 raw15735step2Labels = mixedMoment B raw15735step3 raw15735step3Labels := by
      have ha : raw15735step3 = raw15735step2 := by apply Matrix.ext; unfold raw15735step3 raw15735step2; decide +kernel
      have hl : raw15735step2Labels = labelEmbedding1 ∘ raw15735step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15735step2 raw15735step2Labels raw15735step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw15736 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw15736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15736 raw15736Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw15736 raw15736Labels = mixedMoment B raw15736step0 raw15736step0Labels := by
      have ha : raw15736step0 = (fun i j => raw15736 (permutation520 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15736step0 raw15736; decide +kernel
      have hl : raw15736step0Labels = raw15736Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15736 raw15736Labels permutation520 permutation5
    mixedMoment B raw15736step0 raw15736step0Labels = mixedMoment B raw15736step1 raw15736step1Labels := by
      have ha : raw15736step1 = -raw15736step0 := by apply Matrix.ext; change ∀ i j, raw15736step1 i j = -(raw15736step0 i j); unfold raw15736step1 raw15736step0; decide +kernel
      have hl : raw15736step1Labels = raw15736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15736step1 raw15736step1Labels = mixedMoment B raw15736step2 raw15736step2Labels := by
      have ha : raw15736step2 = raw15736step1 := by apply Matrix.ext; unfold raw15736step2 raw15736step1; decide +kernel
      have hl : raw15736step1Labels = labelEmbedding1 ∘ raw15736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15736step1 raw15736step1Labels raw15736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3378 node3378Labels := by rfl

def raw15737 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15737Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15737step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15737step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15737step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15737step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15737 raw15737Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw15737 raw15737Labels = mixedMoment B raw15737step0 raw15737step0Labels := by
      have ha : raw15737step0 = (fun i j => raw15737 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15737step0 raw15737; decide +kernel
      have hl : raw15737step0Labels = raw15737Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15737 raw15737Labels permutation224 permutation4
    mixedMoment B raw15737step0 raw15737step0Labels = mixedMoment B raw15737step1 raw15737step1Labels := by
      have ha : raw15737step1 = -raw15737step0 := by apply Matrix.ext; change ∀ i j, raw15737step1 i j = -(raw15737step0 i j); unfold raw15737step1 raw15737step0; decide +kernel
      have hl : raw15737step1Labels = raw15737step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw15738 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15738Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15738step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15738step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15738 raw15738Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw15738 raw15738Labels = mixedMoment B raw15738step0 raw15738step0Labels := by
      have ha : raw15738step0 = (fun i j => raw15738 (permutation577 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15738step0 raw15738; decide +kernel
      have hl : raw15738step0Labels = raw15738Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15738 raw15738Labels permutation577 permutation2
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw15739 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15739Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15739step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15739step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15739 raw15739Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw15739 raw15739Labels = mixedMoment B raw15739step0 raw15739step0Labels := by
      have hz : ∀ j, raw15739 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15739step0 = (fun i j => raw15739 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15739step0 raw15739; decide +kernel
      have hl : raw15739step0Labels = raw15739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15739 raw15739Labels permutation346 hz
    mixedMoment B raw15739step0 raw15739step0Labels = mixedMoment B raw15739step1 raw15739step1Labels := by
      have ha : raw15739step1 = (fun i j => raw15739step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15739step1 raw15739step0; decide +kernel
      have hl : raw15739step1Labels = raw15739step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15739step0 raw15739step0Labels permutation127 permutation2
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw15740 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15740 raw15740Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw15740 raw15740Labels = mixedMoment B raw15740step0 raw15740step0Labels := by
      have hz : ∀ j, raw15740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15740step0 = (fun i j => raw15740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15740step0 raw15740; decide +kernel
      have hl : raw15740step0Labels = raw15740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15740 raw15740Labels permutation434 hz
    mixedMoment B raw15740step0 raw15740step0Labels = mixedMoment B raw15740step1 raw15740step1Labels := by
      have ha : raw15740step1 = (fun i j => raw15740step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15740step1 raw15740step0; decide +kernel
      have hl : raw15740step1Labels = raw15740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15740step0 raw15740step0Labels permutation127 permutation2
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw15741 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![-1, -1, 2]]
def raw15741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15741 raw15741Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw15741 raw15741Labels = mixedMoment B raw15741step0 raw15741step0Labels := by
      have ha : raw15741step0 = (fun i j => raw15741 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15741step0 raw15741; decide +kernel
      have hl : raw15741step0Labels = raw15741Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15741 raw15741Labels permutation584 permutation2
    _ = mixedMoment B node2878 node2878Labels := by rfl

def raw15742 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw15742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15742step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15742 raw15742Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw15742 raw15742Labels = mixedMoment B raw15742step0 raw15742step0Labels := by
      have ha : raw15742step0 = (fun i j => raw15742 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15742step0 raw15742; decide +kernel
      have hl : raw15742step0Labels = raw15742Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15742 raw15742Labels permutation682 permutation2
    _ = mixedMoment B node3703 node3703Labels := by rfl

def raw15743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15743step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15743step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15743 raw15743Labels = mixedMoment B node2630 node2630Labels := by
  calc
    mixedMoment B raw15743 raw15743Labels = mixedMoment B raw15743step0 raw15743step0Labels := by
      have ha : raw15743step0 = (fun i j => raw15743 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15743step0 raw15743; decide +kernel
      have hl : raw15743step0Labels = raw15743Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15743 raw15743Labels permutation224 permutation4
    mixedMoment B raw15743step0 raw15743step0Labels = mixedMoment B raw15743step1 raw15743step1Labels := by
      have ha : raw15743step1 = -raw15743step0 := by apply Matrix.ext; change ∀ i j, raw15743step1 i j = -(raw15743step0 i j); unfold raw15743step1 raw15743step0; decide +kernel
      have hl : raw15743step1Labels = raw15743step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2630 node2630Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
