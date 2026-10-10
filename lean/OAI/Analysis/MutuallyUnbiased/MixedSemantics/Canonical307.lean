import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39296Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw39296step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39296step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39296step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39296 raw39296Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw39296 raw39296Labels = mixedMoment B raw39296step0 raw39296step0Labels := by
      have ha : raw39296step0 = (fun i j => raw39296 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39296step0 raw39296; decide +kernel
      have hl : raw39296step0Labels = raw39296Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39296 raw39296Labels permutation158 permutation7
    mixedMoment B raw39296step0 raw39296step0Labels = mixedMoment B raw39296step1 raw39296step1Labels := by
      have ha : raw39296step1 = -raw39296step0 := by apply Matrix.ext; change ∀ i j, raw39296step1 i j = -(raw39296step0 i j); unfold raw39296step1 raw39296step0; decide +kernel
      have hl : raw39296step1Labels = raw39296step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39296step1 raw39296step1Labels = mixedMoment B raw39296step2 raw39296step2Labels := by
      have ha : raw39296step2 = raw39296step1 := by apply Matrix.ext; unfold raw39296step2 raw39296step1; decide +kernel
      have hl : raw39296step1Labels = labelEmbedding4 ∘ raw39296step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39296step1 raw39296step1Labels raw39296step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw39297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39297Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39297 raw39297Labels = mixedMoment B node3692 node3692Labels := by
  calc
    mixedMoment B raw39297 raw39297Labels = mixedMoment B raw39297step0 raw39297step0Labels := by
      have ha : raw39297step0 = raw39297 := by apply Matrix.ext; unfold raw39297step0 raw39297; decide +kernel
      have hl : raw39297Labels = labelEmbedding2 ∘ raw39297step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39297 raw39297Labels raw39297step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3692 node3692Labels := by rfl

def raw39298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39298Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39298step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39298step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39298step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39298step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39298 raw39298Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw39298 raw39298Labels = mixedMoment B raw39298step0 raw39298step0Labels := by
      have ha : raw39298step0 = (fun i j => raw39298 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39298step0 raw39298; decide +kernel
      have hl : raw39298step0Labels = raw39298Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39298 raw39298Labels permutation170 permutation7
    mixedMoment B raw39298step0 raw39298step0Labels = mixedMoment B raw39298step1 raw39298step1Labels := by
      have ha : raw39298step1 = -raw39298step0 := by apply Matrix.ext; change ∀ i j, raw39298step1 i j = -(raw39298step0 i j); unfold raw39298step1 raw39298step0; decide +kernel
      have hl : raw39298step1Labels = raw39298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39298step1 raw39298step1Labels = mixedMoment B raw39298step2 raw39298step2Labels := by
      have ha : raw39298step2 = raw39298step1 := by apply Matrix.ext; unfold raw39298step2 raw39298step1; decide +kernel
      have hl : raw39298step1Labels = labelEmbedding4 ∘ raw39298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39298step1 raw39298step1Labels raw39298step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw39299 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39299Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39299 raw39299Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw39299 raw39299Labels = mixedMoment B raw39299step0 raw39299step0Labels := by
      have ha : raw39299step0 = raw39299 := by apply Matrix.ext; unfold raw39299step0 raw39299; decide +kernel
      have hl : raw39299Labels = labelEmbedding2 ∘ raw39299step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39299 raw39299Labels raw39299step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw39300 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39300Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw39300step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39300step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39300 raw39300Labels = mixedMoment B node3770 node3770Labels := by
  calc
    mixedMoment B raw39300 raw39300Labels = mixedMoment B raw39300step0 raw39300step0Labels := by
      have ha : raw39300step0 = (fun i j => raw39300 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39300step0 raw39300; decide +kernel
      have hl : raw39300step0Labels = raw39300Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39300 raw39300Labels permutation34 permutation7
    mixedMoment B raw39300step0 raw39300step0Labels = mixedMoment B raw39300step1 raw39300step1Labels := by
      have ha : raw39300step1 = -raw39300step0 := by apply Matrix.ext; change ∀ i j, raw39300step1 i j = -(raw39300step0 i j); unfold raw39300step1 raw39300step0; decide +kernel
      have hl : raw39300step1Labels = raw39300step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39300step1 raw39300step1Labels = mixedMoment B raw39300step2 raw39300step2Labels := by
      have ha : raw39300step2 = raw39300step1 := by apply Matrix.ext; unfold raw39300step2 raw39300step1; decide +kernel
      have hl : raw39300step1Labels = labelEmbedding4 ∘ raw39300step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39300step1 raw39300step1Labels raw39300step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3770 node3770Labels := by rfl

def raw39301 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39301Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39301step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39301 raw39301Labels = mixedMoment B node3694 node3694Labels := by
  calc
    mixedMoment B raw39301 raw39301Labels = mixedMoment B raw39301step0 raw39301step0Labels := by
      have ha : raw39301step0 = raw39301 := by apply Matrix.ext; unfold raw39301step0 raw39301; decide +kernel
      have hl : raw39301Labels = labelEmbedding2 ∘ raw39301step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39301 raw39301Labels raw39301step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3694 node3694Labels := by rfl

def raw39302 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39302Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw39302step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw39302step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw39302step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39302 raw39302Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw39302 raw39302Labels = mixedMoment B raw39302step0 raw39302step0Labels := by
      have ha : raw39302step0 = (fun i j => raw39302 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39302step0 raw39302; decide +kernel
      have hl : raw39302step0Labels = raw39302Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39302 raw39302Labels permutation32 permutation7
    mixedMoment B raw39302step0 raw39302step0Labels = mixedMoment B raw39302step1 raw39302step1Labels := by
      have ha : raw39302step1 = -raw39302step0 := by apply Matrix.ext; change ∀ i j, raw39302step1 i j = -(raw39302step0 i j); unfold raw39302step1 raw39302step0; decide +kernel
      have hl : raw39302step1Labels = raw39302step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39302step1 raw39302step1Labels = mixedMoment B raw39302step2 raw39302step2Labels := by
      have ha : raw39302step2 = raw39302step1 := by apply Matrix.ext; unfold raw39302step2 raw39302step1; decide +kernel
      have hl : raw39302step1Labels = labelEmbedding4 ∘ raw39302step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39302step1 raw39302step1Labels raw39302step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

def raw39303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39303Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39303 raw39303Labels = mixedMoment B node3701 node3701Labels := by
  calc
    mixedMoment B raw39303 raw39303Labels = mixedMoment B raw39303step0 raw39303step0Labels := by
      have ha : raw39303step0 = raw39303 := by apply Matrix.ext; unfold raw39303step0 raw39303; decide +kernel
      have hl : raw39303Labels = labelEmbedding2 ∘ raw39303step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39303 raw39303Labels raw39303step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3701 node3701Labels := by rfl

def raw39304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39304Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39304step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39304step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39304step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39304 raw39304Labels = mixedMoment B node3751 node3751Labels := by
  calc
    mixedMoment B raw39304 raw39304Labels = mixedMoment B raw39304step0 raw39304step0Labels := by
      have ha : raw39304step0 = (fun i j => raw39304 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39304step0 raw39304; decide +kernel
      have hl : raw39304step0Labels = raw39304Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39304 raw39304Labels permutation152 permutation7
    mixedMoment B raw39304step0 raw39304step0Labels = mixedMoment B raw39304step1 raw39304step1Labels := by
      have ha : raw39304step1 = -raw39304step0 := by apply Matrix.ext; change ∀ i j, raw39304step1 i j = -(raw39304step0 i j); unfold raw39304step1 raw39304step0; decide +kernel
      have hl : raw39304step1Labels = raw39304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39304step1 raw39304step1Labels = mixedMoment B raw39304step2 raw39304step2Labels := by
      have ha : raw39304step2 = raw39304step1 := by apply Matrix.ext; unfold raw39304step2 raw39304step1; decide +kernel
      have hl : raw39304step1Labels = labelEmbedding4 ∘ raw39304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39304step1 raw39304step1Labels raw39304step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3751 node3751Labels := by rfl

def raw39305 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39305Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39305 raw39305Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw39305 raw39305Labels = mixedMoment B raw39305step0 raw39305step0Labels := by
      have ha : raw39305step0 = raw39305 := by apply Matrix.ext; unfold raw39305step0 raw39305; decide +kernel
      have hl : raw39305Labels = labelEmbedding2 ∘ raw39305step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39305 raw39305Labels raw39305step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3702 node3702Labels := by rfl

def raw39306 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39306Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39306step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39306 raw39306Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw39306 raw39306Labels = mixedMoment B raw39306step0 raw39306step0Labels := by
      have ha : raw39306step0 = (fun i j => raw39306 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39306step0 raw39306; decide +kernel
      have hl : raw39306step0Labels = raw39306Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39306 raw39306Labels permutation151 permutation7
    mixedMoment B raw39306step0 raw39306step0Labels = mixedMoment B raw39306step1 raw39306step1Labels := by
      have ha : raw39306step1 = raw39306step0 := by apply Matrix.ext; unfold raw39306step1 raw39306step0; decide +kernel
      have hl : raw39306step0Labels = labelEmbedding4 ∘ raw39306step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39306step0 raw39306step0Labels raw39306step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3702 node3702Labels := by rfl

def raw39307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39307Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39307 raw39307Labels = mixedMoment B node3703 node3703Labels := by
  calc
    mixedMoment B raw39307 raw39307Labels = mixedMoment B raw39307step0 raw39307step0Labels := by
      have ha : raw39307step0 = raw39307 := by apply Matrix.ext; unfold raw39307step0 raw39307; decide +kernel
      have hl : raw39307Labels = labelEmbedding2 ∘ raw39307step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39307 raw39307Labels raw39307step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3703 node3703Labels := by rfl

def raw39308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39308Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39308step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39308step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39308step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39308 raw39308Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw39308 raw39308Labels = mixedMoment B raw39308step0 raw39308step0Labels := by
      have ha : raw39308step0 = (fun i j => raw39308 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39308step0 raw39308; decide +kernel
      have hl : raw39308step0Labels = raw39308Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39308 raw39308Labels permutation152 permutation7
    mixedMoment B raw39308step0 raw39308step0Labels = mixedMoment B raw39308step1 raw39308step1Labels := by
      have ha : raw39308step1 = -raw39308step0 := by apply Matrix.ext; change ∀ i j, raw39308step1 i j = -(raw39308step0 i j); unfold raw39308step1 raw39308step0; decide +kernel
      have hl : raw39308step1Labels = raw39308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39308step1 raw39308step1Labels = mixedMoment B raw39308step2 raw39308step2Labels := by
      have ha : raw39308step2 = raw39308step1 := by apply Matrix.ext; unfold raw39308step2 raw39308step1; decide +kernel
      have hl : raw39308step1Labels = labelEmbedding4 ∘ raw39308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39308step1 raw39308step1Labels raw39308step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw39309 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39309Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39309 raw39309Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw39309 raw39309Labels = mixedMoment B raw39309step0 raw39309step0Labels := by
      have ha : raw39309step0 = raw39309 := by apply Matrix.ext; unfold raw39309step0 raw39309; decide +kernel
      have hl : raw39309Labels = labelEmbedding2 ∘ raw39309step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39309 raw39309Labels raw39309step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw39310 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39310Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39310step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39310step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39310 raw39310Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw39310 raw39310Labels = mixedMoment B raw39310step0 raw39310step0Labels := by
      have ha : raw39310step0 = (fun i j => raw39310 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39310step0 raw39310; decide +kernel
      have hl : raw39310step0Labels = raw39310Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39310 raw39310Labels permutation33 permutation7
    mixedMoment B raw39310step0 raw39310step0Labels = mixedMoment B raw39310step1 raw39310step1Labels := by
      have ha : raw39310step1 = -raw39310step0 := by apply Matrix.ext; change ∀ i j, raw39310step1 i j = -(raw39310step0 i j); unfold raw39310step1 raw39310step0; decide +kernel
      have hl : raw39310step1Labels = raw39310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39310step1 raw39310step1Labels = mixedMoment B raw39310step2 raw39310step2Labels := by
      have ha : raw39310step2 = raw39310step1 := by apply Matrix.ext; unfold raw39310step2 raw39310step1; decide +kernel
      have hl : raw39310step1Labels = labelEmbedding4 ∘ raw39310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39310step1 raw39310step1Labels raw39310step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3767 node3767Labels := by rfl

def raw39311 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39311Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39311 raw39311Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw39311 raw39311Labels = mixedMoment B raw39311step0 raw39311step0Labels := by
      have ha : raw39311step0 = raw39311 := by apply Matrix.ext; unfold raw39311step0 raw39311; decide +kernel
      have hl : raw39311Labels = labelEmbedding2 ∘ raw39311step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39311 raw39311Labels raw39311step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw39312 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39312Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw39312step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw39312step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw39312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39312 raw39312Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw39312 raw39312Labels = mixedMoment B raw39312step0 raw39312step0Labels := by
      have ha : raw39312step0 = (fun i j => raw39312 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39312step0 raw39312; decide +kernel
      have hl : raw39312step0Labels = raw39312Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39312 raw39312Labels permutation36 permutation7
    mixedMoment B raw39312step0 raw39312step0Labels = mixedMoment B raw39312step1 raw39312step1Labels := by
      have ha : raw39312step1 = -raw39312step0 := by apply Matrix.ext; change ∀ i j, raw39312step1 i j = -(raw39312step0 i j); unfold raw39312step1 raw39312step0; decide +kernel
      have hl : raw39312step1Labels = raw39312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39312step1 raw39312step1Labels = mixedMoment B raw39312step2 raw39312step2Labels := by
      have ha : raw39312step2 = raw39312step1 := by apply Matrix.ext; unfold raw39312step2 raw39312step1; decide +kernel
      have hl : raw39312step1Labels = labelEmbedding4 ∘ raw39312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39312step1 raw39312step1Labels raw39312step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw39313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39313Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39313 raw39313Labels = mixedMoment B node3708 node3708Labels := by
  calc
    mixedMoment B raw39313 raw39313Labels = mixedMoment B raw39313step0 raw39313step0Labels := by
      have ha : raw39313step0 = raw39313 := by apply Matrix.ext; unfold raw39313step0 raw39313; decide +kernel
      have hl : raw39313Labels = labelEmbedding2 ∘ raw39313step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39313 raw39313Labels raw39313step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3708 node3708Labels := by rfl

def raw39314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39314Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw39314step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw39314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39314 raw39314Labels = mixedMoment B node3791 node3791Labels := by
  calc
    mixedMoment B raw39314 raw39314Labels = mixedMoment B raw39314step0 raw39314step0Labels := by
      have ha : raw39314step0 = (fun i j => raw39314 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39314step0 raw39314; decide +kernel
      have hl : raw39314step0Labels = raw39314Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39314 raw39314Labels permutation662 permutation7
    mixedMoment B raw39314step0 raw39314step0Labels = mixedMoment B raw39314step1 raw39314step1Labels := by
      have ha : raw39314step1 = raw39314step0 := by apply Matrix.ext; unfold raw39314step1 raw39314step0; decide +kernel
      have hl : raw39314step0Labels = labelEmbedding4 ∘ raw39314step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39314step0 raw39314step0Labels raw39314step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3791 node3791Labels := by rfl

def raw39315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39315Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39315 raw39315Labels = mixedMoment B node3709 node3709Labels := by
  calc
    mixedMoment B raw39315 raw39315Labels = mixedMoment B raw39315step0 raw39315step0Labels := by
      have ha : raw39315step0 = raw39315 := by apply Matrix.ext; unfold raw39315step0 raw39315; decide +kernel
      have hl : raw39315Labels = labelEmbedding2 ∘ raw39315step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39315 raw39315Labels raw39315step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3709 node3709Labels := by rfl

def raw39316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39316Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw39316step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw39316step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39316step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw39316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39316 raw39316Labels = mixedMoment B node3792 node3792Labels := by
  calc
    mixedMoment B raw39316 raw39316Labels = mixedMoment B raw39316step0 raw39316step0Labels := by
      have ha : raw39316step0 = (fun i j => raw39316 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39316step0 raw39316; decide +kernel
      have hl : raw39316step0Labels = raw39316Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39316 raw39316Labels permutation176 permutation7
    mixedMoment B raw39316step0 raw39316step0Labels = mixedMoment B raw39316step1 raw39316step1Labels := by
      have ha : raw39316step1 = -raw39316step0 := by apply Matrix.ext; change ∀ i j, raw39316step1 i j = -(raw39316step0 i j); unfold raw39316step1 raw39316step0; decide +kernel
      have hl : raw39316step1Labels = raw39316step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39316step1 raw39316step1Labels = mixedMoment B raw39316step2 raw39316step2Labels := by
      have ha : raw39316step2 = raw39316step1 := by apply Matrix.ext; unfold raw39316step2 raw39316step1; decide +kernel
      have hl : raw39316step1Labels = labelEmbedding4 ∘ raw39316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39316step1 raw39316step1Labels raw39316step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3792 node3792Labels := by rfl

def raw39317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39317Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39317 raw39317Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw39317 raw39317Labels = mixedMoment B raw39317step0 raw39317step0Labels := by
      have ha : raw39317step0 = raw39317 := by apply Matrix.ext; unfold raw39317step0 raw39317; decide +kernel
      have hl : raw39317Labels = labelEmbedding2 ∘ raw39317step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39317 raw39317Labels raw39317step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3713 node3713Labels := by rfl

def raw39318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39318Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw39318step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39318step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39318step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39318 raw39318Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw39318 raw39318Labels = mixedMoment B raw39318step0 raw39318step0Labels := by
      have ha : raw39318step0 = (fun i j => raw39318 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39318step0 raw39318; decide +kernel
      have hl : raw39318step0Labels = raw39318Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39318 raw39318Labels permutation176 permutation7
    mixedMoment B raw39318step0 raw39318step0Labels = mixedMoment B raw39318step1 raw39318step1Labels := by
      have ha : raw39318step1 = -raw39318step0 := by apply Matrix.ext; change ∀ i j, raw39318step1 i j = -(raw39318step0 i j); unfold raw39318step1 raw39318step0; decide +kernel
      have hl : raw39318step1Labels = raw39318step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39318step1 raw39318step1Labels = mixedMoment B raw39318step2 raw39318step2Labels := by
      have ha : raw39318step2 = raw39318step1 := by apply Matrix.ext; unfold raw39318step2 raw39318step1; decide +kernel
      have hl : raw39318step1Labels = labelEmbedding4 ∘ raw39318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39318step1 raw39318step1Labels raw39318step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3713 node3713Labels := by rfl

def raw39319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39319Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39319 raw39319Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw39319 raw39319Labels = mixedMoment B raw39319step0 raw39319step0Labels := by
      have ha : raw39319step0 = raw39319 := by apply Matrix.ext; unfold raw39319step0 raw39319; decide +kernel
      have hl : raw39319Labels = labelEmbedding2 ∘ raw39319step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39319 raw39319Labels raw39319step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw39320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39320Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39320step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39320 raw39320Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw39320 raw39320Labels = mixedMoment B raw39320step0 raw39320step0Labels := by
      have ha : raw39320step0 = (fun i j => raw39320 (permutation686 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39320step0 raw39320; decide +kernel
      have hl : raw39320step0Labels = raw39320Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39320 raw39320Labels permutation686 permutation7
    mixedMoment B raw39320step0 raw39320step0Labels = mixedMoment B raw39320step1 raw39320step1Labels := by
      have ha : raw39320step1 = raw39320step0 := by apply Matrix.ext; unfold raw39320step1 raw39320step0; decide +kernel
      have hl : raw39320step0Labels = labelEmbedding4 ∘ raw39320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39320step0 raw39320step0Labels raw39320step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw39321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39321Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39321 raw39321Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw39321 raw39321Labels = mixedMoment B raw39321step0 raw39321step0Labels := by
      have ha : raw39321step0 = raw39321 := by apply Matrix.ext; unfold raw39321step0 raw39321; decide +kernel
      have hl : raw39321Labels = labelEmbedding2 ∘ raw39321step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39321 raw39321Labels raw39321step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw39322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39322Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39322step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39322step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39322step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39322 raw39322Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw39322 raw39322Labels = mixedMoment B raw39322step0 raw39322step0Labels := by
      have ha : raw39322step0 = (fun i j => raw39322 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39322step0 raw39322; decide +kernel
      have hl : raw39322step0Labels = raw39322Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39322 raw39322Labels permutation176 permutation7
    mixedMoment B raw39322step0 raw39322step0Labels = mixedMoment B raw39322step1 raw39322step1Labels := by
      have ha : raw39322step1 = -raw39322step0 := by apply Matrix.ext; change ∀ i j, raw39322step1 i j = -(raw39322step0 i j); unfold raw39322step1 raw39322step0; decide +kernel
      have hl : raw39322step1Labels = raw39322step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39322step1 raw39322step1Labels = mixedMoment B raw39322step2 raw39322step2Labels := by
      have ha : raw39322step2 = raw39322step1 := by apply Matrix.ext; unfold raw39322step2 raw39322step1; decide +kernel
      have hl : raw39322step1Labels = labelEmbedding4 ∘ raw39322step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39322step1 raw39322step1Labels raw39322step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

def raw39323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39323Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39323 raw39323Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw39323 raw39323Labels = mixedMoment B raw39323step0 raw39323step0Labels := by
      have ha : raw39323step0 = raw39323 := by apply Matrix.ext; unfold raw39323step0 raw39323; decide +kernel
      have hl : raw39323Labels = labelEmbedding2 ∘ raw39323step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39323 raw39323Labels raw39323step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3731 node3731Labels := by rfl

def raw39324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39324Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw39324step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39324step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39324step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39324 raw39324Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw39324 raw39324Labels = mixedMoment B raw39324step0 raw39324step0Labels := by
      have ha : raw39324step0 = (fun i j => raw39324 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39324step0 raw39324; decide +kernel
      have hl : raw39324step0Labels = raw39324Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39324 raw39324Labels permutation176 permutation7
    mixedMoment B raw39324step0 raw39324step0Labels = mixedMoment B raw39324step1 raw39324step1Labels := by
      have ha : raw39324step1 = -raw39324step0 := by apply Matrix.ext; change ∀ i j, raw39324step1 i j = -(raw39324step0 i j); unfold raw39324step1 raw39324step0; decide +kernel
      have hl : raw39324step1Labels = raw39324step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39324step1 raw39324step1Labels = mixedMoment B raw39324step2 raw39324step2Labels := by
      have ha : raw39324step2 = raw39324step1 := by apply Matrix.ext; unfold raw39324step2 raw39324step1; decide +kernel
      have hl : raw39324step1Labels = labelEmbedding4 ∘ raw39324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39324step1 raw39324step1Labels raw39324step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3867 node3867Labels := by rfl

def raw39325 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39325Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39325 raw39325Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw39325 raw39325Labels = mixedMoment B raw39325step0 raw39325step0Labels := by
      have ha : raw39325step0 = raw39325 := by apply Matrix.ext; unfold raw39325step0 raw39325; decide +kernel
      have hl : raw39325Labels = labelEmbedding2 ∘ raw39325step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39325 raw39325Labels raw39325step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw39326 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39326Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39326step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39326 raw39326Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw39326 raw39326Labels = mixedMoment B raw39326step0 raw39326step0Labels := by
      have ha : raw39326step0 = (fun i j => raw39326 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39326step0 raw39326; decide +kernel
      have hl : raw39326step0Labels = raw39326Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39326 raw39326Labels permutation149 permutation7
    mixedMoment B raw39326step0 raw39326step0Labels = mixedMoment B raw39326step1 raw39326step1Labels := by
      have ha : raw39326step1 = raw39326step0 := by apply Matrix.ext; unfold raw39326step1 raw39326step0; decide +kernel
      have hl : raw39326step0Labels = labelEmbedding4 ∘ raw39326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39326step0 raw39326step0Labels raw39326step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw39327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39327Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39327 raw39327Labels = mixedMoment B node3735 node3735Labels := by
  calc
    mixedMoment B raw39327 raw39327Labels = mixedMoment B raw39327step0 raw39327step0Labels := by
      have ha : raw39327step0 = raw39327 := by apply Matrix.ext; unfold raw39327step0 raw39327; decide +kernel
      have hl : raw39327Labels = labelEmbedding2 ∘ raw39327step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39327 raw39327Labels raw39327step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3735 node3735Labels := by rfl

def raw39328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39328Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw39328step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39328step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39328step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39328 raw39328Labels = mixedMoment B node3890 node3890Labels := by
  calc
    mixedMoment B raw39328 raw39328Labels = mixedMoment B raw39328step0 raw39328step0Labels := by
      have ha : raw39328step0 = (fun i j => raw39328 (permutation281 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39328step0 raw39328; decide +kernel
      have hl : raw39328step0Labels = raw39328Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39328 raw39328Labels permutation281 permutation5
    mixedMoment B raw39328step0 raw39328step0Labels = mixedMoment B raw39328step1 raw39328step1Labels := by
      have ha : raw39328step1 = -raw39328step0 := by apply Matrix.ext; change ∀ i j, raw39328step1 i j = -(raw39328step0 i j); unfold raw39328step1 raw39328step0; decide +kernel
      have hl : raw39328step1Labels = raw39328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39328step1 raw39328step1Labels = mixedMoment B raw39328step2 raw39328step2Labels := by
      have ha : raw39328step2 = raw39328step1 := by apply Matrix.ext; unfold raw39328step2 raw39328step1; decide +kernel
      have hl : raw39328step1Labels = labelEmbedding4 ∘ raw39328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39328step1 raw39328step1Labels raw39328step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3890 node3890Labels := by rfl

def raw39329 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39329Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39329 raw39329Labels = mixedMoment B node3736 node3736Labels := by
  calc
    mixedMoment B raw39329 raw39329Labels = mixedMoment B raw39329step0 raw39329step0Labels := by
      have ha : raw39329step0 = raw39329 := by apply Matrix.ext; unfold raw39329step0 raw39329; decide +kernel
      have hl : raw39329Labels = labelEmbedding2 ∘ raw39329step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39329 raw39329Labels raw39329step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3736 node3736Labels := by rfl

def raw39330 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39330Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw39330step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw39330step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw39330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39330 raw39330Labels = mixedMoment B node3891 node3891Labels := by
  calc
    mixedMoment B raw39330 raw39330Labels = mixedMoment B raw39330step0 raw39330step0Labels := by
      have ha : raw39330step0 = (fun i j => raw39330 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39330step0 raw39330; decide +kernel
      have hl : raw39330step0Labels = raw39330Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39330 raw39330Labels permutation32 permutation7
    mixedMoment B raw39330step0 raw39330step0Labels = mixedMoment B raw39330step1 raw39330step1Labels := by
      have ha : raw39330step1 = -raw39330step0 := by apply Matrix.ext; change ∀ i j, raw39330step1 i j = -(raw39330step0 i j); unfold raw39330step1 raw39330step0; decide +kernel
      have hl : raw39330step1Labels = raw39330step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39330step1 raw39330step1Labels = mixedMoment B raw39330step2 raw39330step2Labels := by
      have ha : raw39330step2 = raw39330step1 := by apply Matrix.ext; unfold raw39330step2 raw39330step1; decide +kernel
      have hl : raw39330step1Labels = labelEmbedding4 ∘ raw39330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39330step1 raw39330step1Labels raw39330step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3891 node3891Labels := by rfl

def raw39331 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39331Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39331 raw39331Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw39331 raw39331Labels = mixedMoment B raw39331step0 raw39331step0Labels := by
      have ha : raw39331step0 = raw39331 := by apply Matrix.ext; unfold raw39331step0 raw39331; decide +kernel
      have hl : raw39331Labels = labelEmbedding2 ∘ raw39331step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39331 raw39331Labels raw39331step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw39332 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39332Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39332step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39332step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39332 raw39332Labels = mixedMoment B node3892 node3892Labels := by
  calc
    mixedMoment B raw39332 raw39332Labels = mixedMoment B raw39332step0 raw39332step0Labels := by
      have ha : raw39332step0 = (fun i j => raw39332 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39332step0 raw39332; decide +kernel
      have hl : raw39332step0Labels = raw39332Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39332 raw39332Labels permutation58 permutation5
    mixedMoment B raw39332step0 raw39332step0Labels = mixedMoment B raw39332step1 raw39332step1Labels := by
      have ha : raw39332step1 = -raw39332step0 := by apply Matrix.ext; change ∀ i j, raw39332step1 i j = -(raw39332step0 i j); unfold raw39332step1 raw39332step0; decide +kernel
      have hl : raw39332step1Labels = raw39332step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39332step1 raw39332step1Labels = mixedMoment B raw39332step2 raw39332step2Labels := by
      have ha : raw39332step2 = raw39332step1 := by apply Matrix.ext; unfold raw39332step2 raw39332step1; decide +kernel
      have hl : raw39332step1Labels = labelEmbedding4 ∘ raw39332step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39332step1 raw39332step1Labels raw39332step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3892 node3892Labels := by rfl

def raw39333 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39333Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39333step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39333 raw39333Labels = mixedMoment B node3740 node3740Labels := by
  calc
    mixedMoment B raw39333 raw39333Labels = mixedMoment B raw39333step0 raw39333step0Labels := by
      have ha : raw39333step0 = raw39333 := by apply Matrix.ext; unfold raw39333step0 raw39333; decide +kernel
      have hl : raw39333Labels = labelEmbedding2 ∘ raw39333step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39333 raw39333Labels raw39333step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3740 node3740Labels := by rfl

def raw39334 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39334Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39334step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]
def raw39334step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]
def raw39334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39334 raw39334Labels = mixedMoment B node3893 node3893Labels := by
  calc
    mixedMoment B raw39334 raw39334Labels = mixedMoment B raw39334step0 raw39334step0Labels := by
      have ha : raw39334step0 = (fun i j => raw39334 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39334step0 raw39334; decide +kernel
      have hl : raw39334step0Labels = raw39334Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39334 raw39334Labels permutation24 permutation5
    mixedMoment B raw39334step0 raw39334step0Labels = mixedMoment B raw39334step1 raw39334step1Labels := by
      have ha : raw39334step1 = raw39334step0 := by apply Matrix.ext; unfold raw39334step1 raw39334step0; decide +kernel
      have hl : raw39334step0Labels = labelEmbedding4 ∘ raw39334step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39334step0 raw39334step0Labels raw39334step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3893 node3893Labels := by rfl

def raw39335 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39335Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39335step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39335 raw39335Labels = mixedMoment B node3741 node3741Labels := by
  calc
    mixedMoment B raw39335 raw39335Labels = mixedMoment B raw39335step0 raw39335step0Labels := by
      have ha : raw39335step0 = raw39335 := by apply Matrix.ext; unfold raw39335step0 raw39335; decide +kernel
      have hl : raw39335Labels = labelEmbedding2 ∘ raw39335step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39335 raw39335Labels raw39335step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3741 node3741Labels := by rfl

def raw39336 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39336Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39336step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw39336step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39336step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39336 raw39336Labels = mixedMoment B node3894 node3894Labels := by
  calc
    mixedMoment B raw39336 raw39336Labels = mixedMoment B raw39336step0 raw39336step0Labels := by
      have ha : raw39336step0 = (fun i j => raw39336 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39336step0 raw39336; decide +kernel
      have hl : raw39336step0Labels = raw39336Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39336 raw39336Labels permutation14 permutation5
    mixedMoment B raw39336step0 raw39336step0Labels = mixedMoment B raw39336step1 raw39336step1Labels := by
      have ha : raw39336step1 = -raw39336step0 := by apply Matrix.ext; change ∀ i j, raw39336step1 i j = -(raw39336step0 i j); unfold raw39336step1 raw39336step0; decide +kernel
      have hl : raw39336step1Labels = raw39336step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39336step1 raw39336step1Labels = mixedMoment B raw39336step2 raw39336step2Labels := by
      have ha : raw39336step2 = raw39336step1 := by apply Matrix.ext; unfold raw39336step2 raw39336step1; decide +kernel
      have hl : raw39336step1Labels = labelEmbedding4 ∘ raw39336step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39336step1 raw39336step1Labels raw39336step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3894 node3894Labels := by rfl

def raw39337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39337Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39337 raw39337Labels = mixedMoment B node3776 node3776Labels := by
  calc
    mixedMoment B raw39337 raw39337Labels = mixedMoment B raw39337step0 raw39337step0Labels := by
      have ha : raw39337step0 = raw39337 := by apply Matrix.ext; unfold raw39337step0 raw39337; decide +kernel
      have hl : raw39337Labels = labelEmbedding2 ∘ raw39337step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39337 raw39337Labels raw39337step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3776 node3776Labels := by rfl

def raw39338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39338Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw39338step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39338step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39338step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw39338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39338 raw39338Labels = mixedMoment B node3778 node3778Labels := by
  calc
    mixedMoment B raw39338 raw39338Labels = mixedMoment B raw39338step0 raw39338step0Labels := by
      have ha : raw39338step0 = (fun i j => raw39338 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39338step0 raw39338; decide +kernel
      have hl : raw39338step0Labels = raw39338Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39338 raw39338Labels permutation155 permutation7
    mixedMoment B raw39338step0 raw39338step0Labels = mixedMoment B raw39338step1 raw39338step1Labels := by
      have ha : raw39338step1 = -raw39338step0 := by apply Matrix.ext; change ∀ i j, raw39338step1 i j = -(raw39338step0 i j); unfold raw39338step1 raw39338step0; decide +kernel
      have hl : raw39338step1Labels = raw39338step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39338step1 raw39338step1Labels = mixedMoment B raw39338step2 raw39338step2Labels := by
      have ha : raw39338step2 = raw39338step1 := by apply Matrix.ext; unfold raw39338step2 raw39338step1; decide +kernel
      have hl : raw39338step1Labels = labelEmbedding4 ∘ raw39338step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39338step1 raw39338step1Labels raw39338step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3778 node3778Labels := by rfl

def raw39339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39339Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39339 raw39339Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw39339 raw39339Labels = mixedMoment B raw39339step0 raw39339step0Labels := by
      have ha : raw39339step0 = raw39339 := by apply Matrix.ext; unfold raw39339step0 raw39339; decide +kernel
      have hl : raw39339Labels = labelEmbedding2 ∘ raw39339step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39339 raw39339Labels raw39339step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw39340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39340Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw39340step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw39340step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39340step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw39340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39340 raw39340Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw39340 raw39340Labels = mixedMoment B raw39340step0 raw39340step0Labels := by
      have ha : raw39340step0 = (fun i j => raw39340 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39340step0 raw39340; decide +kernel
      have hl : raw39340step0Labels = raw39340Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39340 raw39340Labels permutation152 permutation7
    mixedMoment B raw39340step0 raw39340step0Labels = mixedMoment B raw39340step1 raw39340step1Labels := by
      have ha : raw39340step1 = -raw39340step0 := by apply Matrix.ext; change ∀ i j, raw39340step1 i j = -(raw39340step0 i j); unfold raw39340step1 raw39340step0; decide +kernel
      have hl : raw39340step1Labels = raw39340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39340step1 raw39340step1Labels = mixedMoment B raw39340step2 raw39340step2Labels := by
      have ha : raw39340step2 = raw39340step1 := by apply Matrix.ext; unfold raw39340step2 raw39340step1; decide +kernel
      have hl : raw39340step1Labels = labelEmbedding4 ∘ raw39340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39340step1 raw39340step1Labels raw39340step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

def raw39341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39341Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39341 raw39341Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw39341 raw39341Labels = mixedMoment B raw39341step0 raw39341step0Labels := by
      have ha : raw39341step0 = raw39341 := by apply Matrix.ext; unfold raw39341step0 raw39341; decide +kernel
      have hl : raw39341Labels = labelEmbedding2 ∘ raw39341step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39341 raw39341Labels raw39341step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3781 node3781Labels := by rfl

def raw39342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39342Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39342step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39342step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39342step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39342step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39342 raw39342Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw39342 raw39342Labels = mixedMoment B raw39342step0 raw39342step0Labels := by
      have ha : raw39342step0 = (fun i j => raw39342 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39342step0 raw39342; decide +kernel
      have hl : raw39342step0Labels = raw39342Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39342 raw39342Labels permutation153 permutation7
    mixedMoment B raw39342step0 raw39342step0Labels = mixedMoment B raw39342step1 raw39342step1Labels := by
      have ha : raw39342step1 = -raw39342step0 := by apply Matrix.ext; change ∀ i j, raw39342step1 i j = -(raw39342step0 i j); unfold raw39342step1 raw39342step0; decide +kernel
      have hl : raw39342step1Labels = raw39342step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39342step1 raw39342step1Labels = mixedMoment B raw39342step2 raw39342step2Labels := by
      have ha : raw39342step2 = raw39342step1 := by apply Matrix.ext; unfold raw39342step2 raw39342step1; decide +kernel
      have hl : raw39342step1Labels = labelEmbedding4 ∘ raw39342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39342step1 raw39342step1Labels raw39342step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw39343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39343Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39343 raw39343Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw39343 raw39343Labels = mixedMoment B raw39343step0 raw39343step0Labels := by
      have ha : raw39343step0 = raw39343 := by apply Matrix.ext; unfold raw39343step0 raw39343; decide +kernel
      have hl : raw39343Labels = labelEmbedding2 ∘ raw39343step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39343 raw39343Labels raw39343step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw39344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39344Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw39344step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39344step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw39344step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39344step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw39344step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39344 raw39344Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw39344 raw39344Labels = mixedMoment B raw39344step0 raw39344step0Labels := by
      have ha : raw39344step0 = (fun i j => raw39344 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39344step0 raw39344; decide +kernel
      have hl : raw39344step0Labels = raw39344Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39344 raw39344Labels permutation156 permutation7
    mixedMoment B raw39344step0 raw39344step0Labels = mixedMoment B raw39344step1 raw39344step1Labels := by
      have ha : raw39344step1 = -raw39344step0 := by apply Matrix.ext; change ∀ i j, raw39344step1 i j = -(raw39344step0 i j); unfold raw39344step1 raw39344step0; decide +kernel
      have hl : raw39344step1Labels = raw39344step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39344step1 raw39344step1Labels = mixedMoment B raw39344step2 raw39344step2Labels := by
      have ha : raw39344step2 = raw39344step1 := by apply Matrix.ext; unfold raw39344step2 raw39344step1; decide +kernel
      have hl : raw39344step1Labels = labelEmbedding4 ∘ raw39344step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39344step1 raw39344step1Labels raw39344step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw39345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39345Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39345 raw39345Labels = mixedMoment B node3784 node3784Labels := by
  calc
    mixedMoment B raw39345 raw39345Labels = mixedMoment B raw39345step0 raw39345step0Labels := by
      have ha : raw39345step0 = raw39345 := by apply Matrix.ext; unfold raw39345step0 raw39345; decide +kernel
      have hl : raw39345Labels = labelEmbedding2 ∘ raw39345step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39345 raw39345Labels raw39345step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3784 node3784Labels := by rfl

def raw39346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39346Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39346step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39346 raw39346Labels = mixedMoment B node3784 node3784Labels := by
  calc
    mixedMoment B raw39346 raw39346Labels = mixedMoment B raw39346step0 raw39346step0Labels := by
      have ha : raw39346step0 = (fun i j => raw39346 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39346step0 raw39346; decide +kernel
      have hl : raw39346step0Labels = raw39346Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39346 raw39346Labels permutation682 permutation7
    mixedMoment B raw39346step0 raw39346step0Labels = mixedMoment B raw39346step1 raw39346step1Labels := by
      have ha : raw39346step1 = raw39346step0 := by apply Matrix.ext; unfold raw39346step1 raw39346step0; decide +kernel
      have hl : raw39346step0Labels = labelEmbedding4 ∘ raw39346step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39346step0 raw39346step0Labels raw39346step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3784 node3784Labels := by rfl

def raw39347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39347Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39347 raw39347Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw39347 raw39347Labels = mixedMoment B raw39347step0 raw39347step0Labels := by
      have ha : raw39347step0 = raw39347 := by apply Matrix.ext; unfold raw39347step0 raw39347; decide +kernel
      have hl : raw39347Labels = labelEmbedding2 ∘ raw39347step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39347 raw39347Labels raw39347step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3786 node3786Labels := by rfl

def raw39348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39348Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw39348step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39348step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39348step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39348step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39348 raw39348Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw39348 raw39348Labels = mixedMoment B raw39348step0 raw39348step0Labels := by
      have ha : raw39348step0 = (fun i j => raw39348 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39348step0 raw39348; decide +kernel
      have hl : raw39348step0Labels = raw39348Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39348 raw39348Labels permutation160 permutation7
    mixedMoment B raw39348step0 raw39348step0Labels = mixedMoment B raw39348step1 raw39348step1Labels := by
      have ha : raw39348step1 = -raw39348step0 := by apply Matrix.ext; change ∀ i j, raw39348step1 i j = -(raw39348step0 i j); unfold raw39348step1 raw39348step0; decide +kernel
      have hl : raw39348step1Labels = raw39348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39348step1 raw39348step1Labels = mixedMoment B raw39348step2 raw39348step2Labels := by
      have ha : raw39348step2 = raw39348step1 := by apply Matrix.ext; unfold raw39348step2 raw39348step1; decide +kernel
      have hl : raw39348step1Labels = labelEmbedding4 ∘ raw39348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39348step1 raw39348step1Labels raw39348step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw39349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39349Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39349 raw39349Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw39349 raw39349Labels = mixedMoment B raw39349step0 raw39349step0Labels := by
      have ha : raw39349step0 = raw39349 := by apply Matrix.ext; unfold raw39349step0 raw39349; decide +kernel
      have hl : raw39349Labels = labelEmbedding2 ∘ raw39349step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39349 raw39349Labels raw39349step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw39350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39350Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39350step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39350step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39350step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39350step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39350 raw39350Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw39350 raw39350Labels = mixedMoment B raw39350step0 raw39350step0Labels := by
      have ha : raw39350step0 = (fun i j => raw39350 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39350step0 raw39350; decide +kernel
      have hl : raw39350step0Labels = raw39350Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39350 raw39350Labels permutation158 permutation7
    mixedMoment B raw39350step0 raw39350step0Labels = mixedMoment B raw39350step1 raw39350step1Labels := by
      have ha : raw39350step1 = -raw39350step0 := by apply Matrix.ext; change ∀ i j, raw39350step1 i j = -(raw39350step0 i j); unfold raw39350step1 raw39350step0; decide +kernel
      have hl : raw39350step1Labels = raw39350step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39350step1 raw39350step1Labels = mixedMoment B raw39350step2 raw39350step2Labels := by
      have ha : raw39350step2 = raw39350step1 := by apply Matrix.ext; unfold raw39350step2 raw39350step1; decide +kernel
      have hl : raw39350step1Labels = labelEmbedding4 ∘ raw39350step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39350step1 raw39350step1Labels raw39350step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw39351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39351Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39351 raw39351Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw39351 raw39351Labels = mixedMoment B raw39351step0 raw39351step0Labels := by
      have ha : raw39351step0 = raw39351 := by apply Matrix.ext; unfold raw39351step0 raw39351; decide +kernel
      have hl : raw39351Labels = labelEmbedding2 ∘ raw39351step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39351 raw39351Labels raw39351step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3789 node3789Labels := by rfl

def raw39352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39352Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw39352step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39352step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39352step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39352 raw39352Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw39352 raw39352Labels = mixedMoment B raw39352step0 raw39352step0Labels := by
      have ha : raw39352step0 = (fun i j => raw39352 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39352step0 raw39352; decide +kernel
      have hl : raw39352step0Labels = raw39352Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39352 raw39352Labels permutation170 permutation7
    mixedMoment B raw39352step0 raw39352step0Labels = mixedMoment B raw39352step1 raw39352step1Labels := by
      have ha : raw39352step1 = -raw39352step0 := by apply Matrix.ext; change ∀ i j, raw39352step1 i j = -(raw39352step0 i j); unfold raw39352step1 raw39352step0; decide +kernel
      have hl : raw39352step1Labels = raw39352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39352step1 raw39352step1Labels = mixedMoment B raw39352step2 raw39352step2Labels := by
      have ha : raw39352step2 = raw39352step1 := by apply Matrix.ext; unfold raw39352step2 raw39352step1; decide +kernel
      have hl : raw39352step1Labels = labelEmbedding4 ∘ raw39352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39352step1 raw39352step1Labels raw39352step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

def raw39353 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39353Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39353 raw39353Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw39353 raw39353Labels = mixedMoment B raw39353step0 raw39353step0Labels := by
      have ha : raw39353step0 = raw39353 := by apply Matrix.ext; unfold raw39353step0 raw39353; decide +kernel
      have hl : raw39353Labels = labelEmbedding2 ∘ raw39353step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39353 raw39353Labels raw39353step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw39354 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39354Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw39354step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw39354step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39354step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw39354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39354 raw39354Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw39354 raw39354Labels = mixedMoment B raw39354step0 raw39354step0Labels := by
      have ha : raw39354step0 = (fun i j => raw39354 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39354step0 raw39354; decide +kernel
      have hl : raw39354step0Labels = raw39354Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39354 raw39354Labels permutation32 permutation7
    mixedMoment B raw39354step0 raw39354step0Labels = mixedMoment B raw39354step1 raw39354step1Labels := by
      have ha : raw39354step1 = -raw39354step0 := by apply Matrix.ext; change ∀ i j, raw39354step1 i j = -(raw39354step0 i j); unfold raw39354step1 raw39354step0; decide +kernel
      have hl : raw39354step1Labels = raw39354step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39354step1 raw39354step1Labels = mixedMoment B raw39354step2 raw39354step2Labels := by
      have ha : raw39354step2 = raw39354step1 := by apply Matrix.ext; unfold raw39354step2 raw39354step1; decide +kernel
      have hl : raw39354step1Labels = labelEmbedding4 ∘ raw39354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39354step1 raw39354step1Labels raw39354step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

def raw39355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39355Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39355 raw39355Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw39355 raw39355Labels = mixedMoment B raw39355step0 raw39355step0Labels := by
      have ha : raw39355step0 = raw39355 := by apply Matrix.ext; unfold raw39355step0 raw39355; decide +kernel
      have hl : raw39355Labels = labelEmbedding2 ∘ raw39355step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39355 raw39355Labels raw39355step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw39356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39356Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw39356step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39356step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39356step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39356 raw39356Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw39356 raw39356Labels = mixedMoment B raw39356step0 raw39356step0Labels := by
      have ha : raw39356step0 = (fun i j => raw39356 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39356step0 raw39356; decide +kernel
      have hl : raw39356step0Labels = raw39356Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39356 raw39356Labels permutation164 permutation7
    mixedMoment B raw39356step0 raw39356step0Labels = mixedMoment B raw39356step1 raw39356step1Labels := by
      have ha : raw39356step1 = -raw39356step0 := by apply Matrix.ext; change ∀ i j, raw39356step1 i j = -(raw39356step0 i j); unfold raw39356step1 raw39356step0; decide +kernel
      have hl : raw39356step1Labels = raw39356step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39356step1 raw39356step1Labels = mixedMoment B raw39356step2 raw39356step2Labels := by
      have ha : raw39356step2 = raw39356step1 := by apply Matrix.ext; unfold raw39356step2 raw39356step1; decide +kernel
      have hl : raw39356step1Labels = labelEmbedding4 ∘ raw39356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39356step1 raw39356step1Labels raw39356step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw39357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39357Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39357 raw39357Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw39357 raw39357Labels = mixedMoment B raw39357step0 raw39357step0Labels := by
      have ha : raw39357step0 = raw39357 := by apply Matrix.ext; unfold raw39357step0 raw39357; decide +kernel
      have hl : raw39357Labels = labelEmbedding2 ∘ raw39357step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39357 raw39357Labels raw39357step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw39358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39358Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw39358step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39358step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39358 raw39358Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw39358 raw39358Labels = mixedMoment B raw39358step0 raw39358step0Labels := by
      have ha : raw39358step0 = (fun i j => raw39358 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39358step0 raw39358; decide +kernel
      have hl : raw39358step0Labels = raw39358Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39358 raw39358Labels permutation170 permutation7
    mixedMoment B raw39358step0 raw39358step0Labels = mixedMoment B raw39358step1 raw39358step1Labels := by
      have ha : raw39358step1 = -raw39358step0 := by apply Matrix.ext; change ∀ i j, raw39358step1 i j = -(raw39358step0 i j); unfold raw39358step1 raw39358step0; decide +kernel
      have hl : raw39358step1Labels = raw39358step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39358step1 raw39358step1Labels = mixedMoment B raw39358step2 raw39358step2Labels := by
      have ha : raw39358step2 = raw39358step1 := by apply Matrix.ext; unfold raw39358step2 raw39358step1; decide +kernel
      have hl : raw39358step1Labels = labelEmbedding4 ∘ raw39358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39358step1 raw39358step1Labels raw39358step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw39359 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39359Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39359 raw39359Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw39359 raw39359Labels = mixedMoment B raw39359step0 raw39359step0Labels := by
      have ha : raw39359step0 = raw39359 := by apply Matrix.ext; unfold raw39359step0 raw39359; decide +kernel
      have hl : raw39359Labels = labelEmbedding2 ∘ raw39359step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39359 raw39359Labels raw39359step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw39360 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39360Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw39360step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39360step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39360 raw39360Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw39360 raw39360Labels = mixedMoment B raw39360step0 raw39360step0Labels := by
      have ha : raw39360step0 = (fun i j => raw39360 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39360step0 raw39360; decide +kernel
      have hl : raw39360step0Labels = raw39360Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39360 raw39360Labels permutation36 permutation7
    mixedMoment B raw39360step0 raw39360step0Labels = mixedMoment B raw39360step1 raw39360step1Labels := by
      have ha : raw39360step1 = -raw39360step0 := by apply Matrix.ext; change ∀ i j, raw39360step1 i j = -(raw39360step0 i j); unfold raw39360step1 raw39360step0; decide +kernel
      have hl : raw39360step1Labels = raw39360step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39360step1 raw39360step1Labels = mixedMoment B raw39360step2 raw39360step2Labels := by
      have ha : raw39360step2 = raw39360step1 := by apply Matrix.ext; unfold raw39360step2 raw39360step1; decide +kernel
      have hl : raw39360step1Labels = labelEmbedding4 ∘ raw39360step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39360step1 raw39360step1Labels raw39360step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw39361 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39361Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39361 raw39361Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw39361 raw39361Labels = mixedMoment B raw39361step0 raw39361step0Labels := by
      have ha : raw39361step0 = raw39361 := by apply Matrix.ext; unfold raw39361step0 raw39361; decide +kernel
      have hl : raw39361Labels = labelEmbedding2 ∘ raw39361step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39361 raw39361Labels raw39361step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw39362 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39362Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw39362step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39362step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39362 raw39362Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw39362 raw39362Labels = mixedMoment B raw39362step0 raw39362step0Labels := by
      have ha : raw39362step0 = (fun i j => raw39362 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39362step0 raw39362; decide +kernel
      have hl : raw39362step0Labels = raw39362Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39362 raw39362Labels permutation37 permutation7
    mixedMoment B raw39362step0 raw39362step0Labels = mixedMoment B raw39362step1 raw39362step1Labels := by
      have ha : raw39362step1 = -raw39362step0 := by apply Matrix.ext; change ∀ i j, raw39362step1 i j = -(raw39362step0 i j); unfold raw39362step1 raw39362step0; decide +kernel
      have hl : raw39362step1Labels = raw39362step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39362step1 raw39362step1Labels = mixedMoment B raw39362step2 raw39362step2Labels := by
      have ha : raw39362step2 = raw39362step1 := by apply Matrix.ext; unfold raw39362step2 raw39362step1; decide +kernel
      have hl : raw39362step1Labels = labelEmbedding4 ∘ raw39362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39362step1 raw39362step1Labels raw39362step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw39363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39363Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39363 raw39363Labels = mixedMoment B node3820 node3820Labels := by
  calc
    mixedMoment B raw39363 raw39363Labels = mixedMoment B raw39363step0 raw39363step0Labels := by
      have ha : raw39363step0 = raw39363 := by apply Matrix.ext; unfold raw39363step0 raw39363; decide +kernel
      have hl : raw39363Labels = labelEmbedding2 ∘ raw39363step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39363 raw39363Labels raw39363step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3820 node3820Labels := by rfl

def raw39364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39364Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw39364step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw39364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39364 raw39364Labels = mixedMoment B node3895 node3895Labels := by
  calc
    mixedMoment B raw39364 raw39364Labels = mixedMoment B raw39364step0 raw39364step0Labels := by
      have ha : raw39364step0 = (fun i j => raw39364 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39364step0 raw39364; decide +kernel
      have hl : raw39364step0Labels = raw39364Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39364 raw39364Labels permutation662 permutation7
    mixedMoment B raw39364step0 raw39364step0Labels = mixedMoment B raw39364step1 raw39364step1Labels := by
      have ha : raw39364step1 = raw39364step0 := by apply Matrix.ext; unfold raw39364step1 raw39364step0; decide +kernel
      have hl : raw39364step0Labels = labelEmbedding4 ∘ raw39364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39364step0 raw39364step0Labels raw39364step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3895 node3895Labels := by rfl

def raw39365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39365Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39365 raw39365Labels = mixedMoment B node3821 node3821Labels := by
  calc
    mixedMoment B raw39365 raw39365Labels = mixedMoment B raw39365step0 raw39365step0Labels := by
      have ha : raw39365step0 = raw39365 := by apply Matrix.ext; unfold raw39365step0 raw39365; decide +kernel
      have hl : raw39365Labels = labelEmbedding2 ∘ raw39365step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39365 raw39365Labels raw39365step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3821 node3821Labels := by rfl

def raw39366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39366Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39366step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39366step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39366step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39366 raw39366Labels = mixedMoment B node3896 node3896Labels := by
  calc
    mixedMoment B raw39366 raw39366Labels = mixedMoment B raw39366step0 raw39366step0Labels := by
      have ha : raw39366step0 = (fun i j => raw39366 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39366step0 raw39366; decide +kernel
      have hl : raw39366step0Labels = raw39366Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39366 raw39366Labels permutation152 permutation7
    mixedMoment B raw39366step0 raw39366step0Labels = mixedMoment B raw39366step1 raw39366step1Labels := by
      have ha : raw39366step1 = -raw39366step0 := by apply Matrix.ext; change ∀ i j, raw39366step1 i j = -(raw39366step0 i j); unfold raw39366step1 raw39366step0; decide +kernel
      have hl : raw39366step1Labels = raw39366step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39366step1 raw39366step1Labels = mixedMoment B raw39366step2 raw39366step2Labels := by
      have ha : raw39366step2 = raw39366step1 := by apply Matrix.ext; unfold raw39366step2 raw39366step1; decide +kernel
      have hl : raw39366step1Labels = labelEmbedding4 ∘ raw39366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39366step1 raw39366step1Labels raw39366step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3896 node3896Labels := by rfl

def raw39367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39367Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39367 raw39367Labels = mixedMoment B node3823 node3823Labels := by
  calc
    mixedMoment B raw39367 raw39367Labels = mixedMoment B raw39367step0 raw39367step0Labels := by
      have ha : raw39367step0 = raw39367 := by apply Matrix.ext; unfold raw39367step0 raw39367; decide +kernel
      have hl : raw39367Labels = labelEmbedding2 ∘ raw39367step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39367 raw39367Labels raw39367step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3823 node3823Labels := by rfl

def raw39368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39368Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw39368step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw39368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39368 raw39368Labels = mixedMoment B node3897 node3897Labels := by
  calc
    mixedMoment B raw39368 raw39368Labels = mixedMoment B raw39368step0 raw39368step0Labels := by
      have ha : raw39368step0 = (fun i j => raw39368 (permutation659 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39368step0 raw39368; decide +kernel
      have hl : raw39368step0Labels = raw39368Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39368 raw39368Labels permutation659 permutation5
    mixedMoment B raw39368step0 raw39368step0Labels = mixedMoment B raw39368step1 raw39368step1Labels := by
      have ha : raw39368step1 = raw39368step0 := by apply Matrix.ext; unfold raw39368step1 raw39368step0; decide +kernel
      have hl : raw39368step0Labels = labelEmbedding4 ∘ raw39368step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39368step0 raw39368step0Labels raw39368step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3897 node3897Labels := by rfl

def raw39369 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39369Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39369 raw39369Labels = mixedMoment B node3824 node3824Labels := by
  calc
    mixedMoment B raw39369 raw39369Labels = mixedMoment B raw39369step0 raw39369step0Labels := by
      have ha : raw39369step0 = raw39369 := by apply Matrix.ext; unfold raw39369step0 raw39369; decide +kernel
      have hl : raw39369Labels = labelEmbedding2 ∘ raw39369step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39369 raw39369Labels raw39369step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3824 node3824Labels := by rfl

def raw39370 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw39370Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw39370step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw39370step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw39370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39370 raw39370Labels = mixedMoment B node3898 node3898Labels := by
  calc
    mixedMoment B raw39370 raw39370Labels = mixedMoment B raw39370step0 raw39370step0Labels := by
      have ha : raw39370step0 = (fun i j => raw39370 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39370step0 raw39370; decide +kernel
      have hl : raw39370step0Labels = raw39370Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39370 raw39370Labels permutation32 permutation7
    mixedMoment B raw39370step0 raw39370step0Labels = mixedMoment B raw39370step1 raw39370step1Labels := by
      have ha : raw39370step1 = -raw39370step0 := by apply Matrix.ext; change ∀ i j, raw39370step1 i j = -(raw39370step0 i j); unfold raw39370step1 raw39370step0; decide +kernel
      have hl : raw39370step1Labels = raw39370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39370step1 raw39370step1Labels = mixedMoment B raw39370step2 raw39370step2Labels := by
      have ha : raw39370step2 = raw39370step1 := by apply Matrix.ext; unfold raw39370step2 raw39370step1; decide +kernel
      have hl : raw39370step1Labels = labelEmbedding4 ∘ raw39370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39370step1 raw39370step1Labels raw39370step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3898 node3898Labels := by rfl

def raw39371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39371Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw39371step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw39371step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39371step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw39371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39371 raw39371Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw39371 raw39371Labels = mixedMoment B raw39371step0 raw39371step0Labels := by
      have ha : raw39371step0 = (fun i j => raw39371 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39371step0 raw39371; decide +kernel
      have hl : raw39371step0Labels = raw39371Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39371 raw39371Labels permutation160 permutation7
    mixedMoment B raw39371step0 raw39371step0Labels = mixedMoment B raw39371step1 raw39371step1Labels := by
      have ha : raw39371step1 = -raw39371step0 := by apply Matrix.ext; change ∀ i j, raw39371step1 i j = -(raw39371step0 i j); unfold raw39371step1 raw39371step0; decide +kernel
      have hl : raw39371step1Labels = raw39371step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39371step1 raw39371step1Labels = mixedMoment B raw39371step2 raw39371step2Labels := by
      have ha : raw39371step2 = raw39371step1 := by apply Matrix.ext; unfold raw39371step2 raw39371step1; decide +kernel
      have hl : raw39371step1Labels = labelEmbedding1 ∘ raw39371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39371step1 raw39371step1Labels raw39371step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3900 node3900Labels := by rfl

def raw39372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39372Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39372 raw39372Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw39372 raw39372Labels = mixedMoment B raw39372step0 raw39372step0Labels := by
      have ha : raw39372step0 = raw39372 := by apply Matrix.ext; unfold raw39372step0 raw39372; decide +kernel
      have hl : raw39372Labels = labelEmbedding2 ∘ raw39372step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39372 raw39372Labels raw39372step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw39373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39373Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39373step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39373 raw39373Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw39373 raw39373Labels = mixedMoment B raw39373step0 raw39373step0Labels := by
      have ha : raw39373step0 = (fun i j => raw39373 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39373step0 raw39373; decide +kernel
      have hl : raw39373step0Labels = raw39373Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39373 raw39373Labels permutation662 permutation7
    mixedMoment B raw39373step0 raw39373step0Labels = mixedMoment B raw39373step1 raw39373step1Labels := by
      have ha : raw39373step1 = raw39373step0 := by apply Matrix.ext; unfold raw39373step1 raw39373step0; decide +kernel
      have hl : raw39373step0Labels = labelEmbedding4 ∘ raw39373step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39373step0 raw39373step0Labels raw39373step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw39374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39374Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39374 raw39374Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw39374 raw39374Labels = mixedMoment B raw39374step0 raw39374step0Labels := by
      have ha : raw39374step0 = raw39374 := by apply Matrix.ext; unfold raw39374step0 raw39374; decide +kernel
      have hl : raw39374Labels = labelEmbedding2 ∘ raw39374step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39374 raw39374Labels raw39374step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw39375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39375Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw39375step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39375step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39375step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39375 raw39375Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw39375 raw39375Labels = mixedMoment B raw39375step0 raw39375step0Labels := by
      have ha : raw39375step0 = (fun i j => raw39375 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39375step0 raw39375; decide +kernel
      have hl : raw39375step0Labels = raw39375Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39375 raw39375Labels permutation176 permutation7
    mixedMoment B raw39375step0 raw39375step0Labels = mixedMoment B raw39375step1 raw39375step1Labels := by
      have ha : raw39375step1 = -raw39375step0 := by apply Matrix.ext; change ∀ i j, raw39375step1 i j = -(raw39375step0 i j); unfold raw39375step1 raw39375step0; decide +kernel
      have hl : raw39375step1Labels = raw39375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39375step1 raw39375step1Labels = mixedMoment B raw39375step2 raw39375step2Labels := by
      have ha : raw39375step2 = raw39375step1 := by apply Matrix.ext; unfold raw39375step2 raw39375step1; decide +kernel
      have hl : raw39375step1Labels = labelEmbedding4 ∘ raw39375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39375step1 raw39375step1Labels raw39375step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw39376 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39376Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39376 raw39376Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw39376 raw39376Labels = mixedMoment B raw39376step0 raw39376step0Labels := by
      have ha : raw39376step0 = raw39376 := by apply Matrix.ext; unfold raw39376step0 raw39376; decide +kernel
      have hl : raw39376Labels = labelEmbedding2 ∘ raw39376step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39376 raw39376Labels raw39376step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw39377 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39377Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39377step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39377step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39377step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw39377step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39377 raw39377Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw39377 raw39377Labels = mixedMoment B raw39377step0 raw39377step0Labels := by
      have ha : raw39377step0 = (fun i j => raw39377 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39377step0 raw39377; decide +kernel
      have hl : raw39377step0Labels = raw39377Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39377 raw39377Labels permutation39 permutation7
    mixedMoment B raw39377step0 raw39377step0Labels = mixedMoment B raw39377step1 raw39377step1Labels := by
      have ha : raw39377step1 = -raw39377step0 := by apply Matrix.ext; change ∀ i j, raw39377step1 i j = -(raw39377step0 i j); unfold raw39377step1 raw39377step0; decide +kernel
      have hl : raw39377step1Labels = raw39377step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39377step1 raw39377step1Labels = mixedMoment B raw39377step2 raw39377step2Labels := by
      have ha : raw39377step2 = raw39377step1 := by apply Matrix.ext; unfold raw39377step2 raw39377step1; decide +kernel
      have hl : raw39377step1Labels = labelEmbedding4 ∘ raw39377step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39377step1 raw39377step1Labels raw39377step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw39378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39378Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39378 raw39378Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw39378 raw39378Labels = mixedMoment B raw39378step0 raw39378step0Labels := by
      have ha : raw39378step0 = raw39378 := by apply Matrix.ext; unfold raw39378step0 raw39378; decide +kernel
      have hl : raw39378Labels = labelEmbedding2 ∘ raw39378step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39378 raw39378Labels raw39378step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw39379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39379Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39379step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39379step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39379step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39379 raw39379Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw39379 raw39379Labels = mixedMoment B raw39379step0 raw39379step0Labels := by
      have ha : raw39379step0 = (fun i j => raw39379 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39379step0 raw39379; decide +kernel
      have hl : raw39379step0Labels = raw39379Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39379 raw39379Labels permutation200 permutation7
    mixedMoment B raw39379step0 raw39379step0Labels = mixedMoment B raw39379step1 raw39379step1Labels := by
      have ha : raw39379step1 = -raw39379step0 := by apply Matrix.ext; change ∀ i j, raw39379step1 i j = -(raw39379step0 i j); unfold raw39379step1 raw39379step0; decide +kernel
      have hl : raw39379step1Labels = raw39379step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39379step1 raw39379step1Labels = mixedMoment B raw39379step2 raw39379step2Labels := by
      have ha : raw39379step2 = raw39379step1 := by apply Matrix.ext; unfold raw39379step2 raw39379step1; decide +kernel
      have hl : raw39379step1Labels = labelEmbedding4 ∘ raw39379step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39379step1 raw39379step1Labels raw39379step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw39380 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39380Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39380 raw39380Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw39380 raw39380Labels = mixedMoment B raw39380step0 raw39380step0Labels := by
      have ha : raw39380step0 = raw39380 := by apply Matrix.ext; unfold raw39380step0 raw39380; decide +kernel
      have hl : raw39380Labels = labelEmbedding2 ∘ raw39380step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39380 raw39380Labels raw39380step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw39381 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39381Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39381step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39381 raw39381Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw39381 raw39381Labels = mixedMoment B raw39381step0 raw39381step0Labels := by
      have ha : raw39381step0 = (fun i j => raw39381 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39381step0 raw39381; decide +kernel
      have hl : raw39381step0Labels = raw39381Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39381 raw39381Labels permutation143 permutation7
    mixedMoment B raw39381step0 raw39381step0Labels = mixedMoment B raw39381step1 raw39381step1Labels := by
      have ha : raw39381step1 = raw39381step0 := by apply Matrix.ext; unfold raw39381step1 raw39381step0; decide +kernel
      have hl : raw39381step0Labels = labelEmbedding4 ∘ raw39381step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39381step0 raw39381step0Labels raw39381step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw39382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39382Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39382 raw39382Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw39382 raw39382Labels = mixedMoment B raw39382step0 raw39382step0Labels := by
      have ha : raw39382step0 = raw39382 := by apply Matrix.ext; unfold raw39382step0 raw39382; decide +kernel
      have hl : raw39382Labels = labelEmbedding2 ∘ raw39382step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39382 raw39382Labels raw39382step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw39383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39383Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39383step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39383step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39383step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39383step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39383 raw39383Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw39383 raw39383Labels = mixedMoment B raw39383step0 raw39383step0Labels := by
      have ha : raw39383step0 = (fun i j => raw39383 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39383step0 raw39383; decide +kernel
      have hl : raw39383step0Labels = raw39383Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39383 raw39383Labels permutation160 permutation7
    mixedMoment B raw39383step0 raw39383step0Labels = mixedMoment B raw39383step1 raw39383step1Labels := by
      have ha : raw39383step1 = -raw39383step0 := by apply Matrix.ext; change ∀ i j, raw39383step1 i j = -(raw39383step0 i j); unfold raw39383step1 raw39383step0; decide +kernel
      have hl : raw39383step1Labels = raw39383step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39383step1 raw39383step1Labels = mixedMoment B raw39383step2 raw39383step2Labels := by
      have ha : raw39383step2 = raw39383step1 := by apply Matrix.ext; unfold raw39383step2 raw39383step1; decide +kernel
      have hl : raw39383step1Labels = labelEmbedding4 ∘ raw39383step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39383step1 raw39383step1Labels raw39383step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3901 node3901Labels := by rfl

def raw39384 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39384Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39384 raw39384Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw39384 raw39384Labels = mixedMoment B raw39384step0 raw39384step0Labels := by
      have ha : raw39384step0 = raw39384 := by apply Matrix.ext; unfold raw39384step0 raw39384; decide +kernel
      have hl : raw39384Labels = labelEmbedding2 ∘ raw39384step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39384 raw39384Labels raw39384step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw39385 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39385Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw39385step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw39385step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw39385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39385 raw39385Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw39385 raw39385Labels = mixedMoment B raw39385step0 raw39385step0Labels := by
      have ha : raw39385step0 = (fun i j => raw39385 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39385step0 raw39385; decide +kernel
      have hl : raw39385step0Labels = raw39385Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39385 raw39385Labels permutation34 permutation7
    mixedMoment B raw39385step0 raw39385step0Labels = mixedMoment B raw39385step1 raw39385step1Labels := by
      have ha : raw39385step1 = -raw39385step0 := by apply Matrix.ext; change ∀ i j, raw39385step1 i j = -(raw39385step0 i j); unfold raw39385step1 raw39385step0; decide +kernel
      have hl : raw39385step1Labels = raw39385step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39385step1 raw39385step1Labels = mixedMoment B raw39385step2 raw39385step2Labels := by
      have ha : raw39385step2 = raw39385step1 := by apply Matrix.ext; unfold raw39385step2 raw39385step1; decide +kernel
      have hl : raw39385step1Labels = labelEmbedding4 ∘ raw39385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39385step1 raw39385step1Labels raw39385step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3903 node3903Labels := by rfl

def raw39386 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39386Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39386 raw39386Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw39386 raw39386Labels = mixedMoment B raw39386step0 raw39386step0Labels := by
      have ha : raw39386step0 = raw39386 := by apply Matrix.ext; unfold raw39386step0 raw39386; decide +kernel
      have hl : raw39386Labels = labelEmbedding2 ∘ raw39386step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39386 raw39386Labels raw39386step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw39387 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39387Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw39387step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw39387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39387 raw39387Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw39387 raw39387Labels = mixedMoment B raw39387step0 raw39387step0Labels := by
      have ha : raw39387step0 = (fun i j => raw39387 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39387step0 raw39387; decide +kernel
      have hl : raw39387step0Labels = raw39387Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39387 raw39387Labels permutation147 permutation5
    mixedMoment B raw39387step0 raw39387step0Labels = mixedMoment B raw39387step1 raw39387step1Labels := by
      have ha : raw39387step1 = raw39387step0 := by apply Matrix.ext; unfold raw39387step1 raw39387step0; decide +kernel
      have hl : raw39387step0Labels = labelEmbedding4 ∘ raw39387step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39387step0 raw39387step0Labels raw39387step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3906 node3906Labels := by rfl

def raw39388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39388Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw39388step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39388step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39388step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39388step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39388 raw39388Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw39388 raw39388Labels = mixedMoment B raw39388step0 raw39388step0Labels := by
      have ha : raw39388step0 = (fun i j => raw39388 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39388step0 raw39388; decide +kernel
      have hl : raw39388step0Labels = raw39388Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39388 raw39388Labels permutation161 permutation7
    mixedMoment B raw39388step0 raw39388step0Labels = mixedMoment B raw39388step1 raw39388step1Labels := by
      have ha : raw39388step1 = -raw39388step0 := by apply Matrix.ext; change ∀ i j, raw39388step1 i j = -(raw39388step0 i j); unfold raw39388step1 raw39388step0; decide +kernel
      have hl : raw39388step1Labels = raw39388step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39388step1 raw39388step1Labels = mixedMoment B raw39388step2 raw39388step2Labels := by
      have ha : raw39388step2 = raw39388step1 := by apply Matrix.ext; unfold raw39388step2 raw39388step1; decide +kernel
      have hl : raw39388step1Labels = labelEmbedding1 ∘ raw39388step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39388step1 raw39388step1Labels raw39388step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw39389 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39389Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39389 raw39389Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw39389 raw39389Labels = mixedMoment B raw39389step0 raw39389step0Labels := by
      have ha : raw39389step0 = raw39389 := by apply Matrix.ext; unfold raw39389step0 raw39389; decide +kernel
      have hl : raw39389Labels = labelEmbedding2 ∘ raw39389step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39389 raw39389Labels raw39389step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw39390 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39390Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39390step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw39390step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw39390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39390 raw39390Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw39390 raw39390Labels = mixedMoment B raw39390step0 raw39390step0Labels := by
      have ha : raw39390step0 = (fun i j => raw39390 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39390step0 raw39390; decide +kernel
      have hl : raw39390step0Labels = raw39390Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39390 raw39390Labels permutation38 permutation7
    mixedMoment B raw39390step0 raw39390step0Labels = mixedMoment B raw39390step1 raw39390step1Labels := by
      have ha : raw39390step1 = -raw39390step0 := by apply Matrix.ext; change ∀ i j, raw39390step1 i j = -(raw39390step0 i j); unfold raw39390step1 raw39390step0; decide +kernel
      have hl : raw39390step1Labels = raw39390step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39390step1 raw39390step1Labels = mixedMoment B raw39390step2 raw39390step2Labels := by
      have ha : raw39390step2 = raw39390step1 := by apply Matrix.ext; unfold raw39390step2 raw39390step1; decide +kernel
      have hl : raw39390step1Labels = labelEmbedding4 ∘ raw39390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39390step1 raw39390step1Labels raw39390step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw39391 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39391Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39391 raw39391Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw39391 raw39391Labels = mixedMoment B raw39391step0 raw39391step0Labels := by
      have ha : raw39391step0 = raw39391 := by apply Matrix.ext; unfold raw39391step0 raw39391; decide +kernel
      have hl : raw39391Labels = labelEmbedding2 ∘ raw39391step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39391 raw39391Labels raw39391step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw39392 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39392Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw39392step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw39392step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39392step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw39392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39392 raw39392Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw39392 raw39392Labels = mixedMoment B raw39392step0 raw39392step0Labels := by
      have ha : raw39392step0 = (fun i j => raw39392 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39392step0 raw39392; decide +kernel
      have hl : raw39392step0Labels = raw39392Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39392 raw39392Labels permutation32 permutation7
    mixedMoment B raw39392step0 raw39392step0Labels = mixedMoment B raw39392step1 raw39392step1Labels := by
      have ha : raw39392step1 = -raw39392step0 := by apply Matrix.ext; change ∀ i j, raw39392step1 i j = -(raw39392step0 i j); unfold raw39392step1 raw39392step0; decide +kernel
      have hl : raw39392step1Labels = raw39392step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39392step1 raw39392step1Labels = mixedMoment B raw39392step2 raw39392step2Labels := by
      have ha : raw39392step2 = raw39392step1 := by apply Matrix.ext; unfold raw39392step2 raw39392step1; decide +kernel
      have hl : raw39392step1Labels = labelEmbedding4 ∘ raw39392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39392step1 raw39392step1Labels raw39392step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw39393 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39393Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39393step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39393 raw39393Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw39393 raw39393Labels = mixedMoment B raw39393step0 raw39393step0Labels := by
      have ha : raw39393step0 = raw39393 := by apply Matrix.ext; unfold raw39393step0 raw39393; decide +kernel
      have hl : raw39393Labels = labelEmbedding2 ∘ raw39393step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39393 raw39393Labels raw39393step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw39394 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39394Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39394step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw39394step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw39394step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw39394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39394 raw39394Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw39394 raw39394Labels = mixedMoment B raw39394step0 raw39394step0Labels := by
      have ha : raw39394step0 = (fun i j => raw39394 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39394step0 raw39394; decide +kernel
      have hl : raw39394step0Labels = raw39394Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39394 raw39394Labels permutation9 permutation7
    mixedMoment B raw39394step0 raw39394step0Labels = mixedMoment B raw39394step1 raw39394step1Labels := by
      have ha : raw39394step1 = -raw39394step0 := by apply Matrix.ext; change ∀ i j, raw39394step1 i j = -(raw39394step0 i j); unfold raw39394step1 raw39394step0; decide +kernel
      have hl : raw39394step1Labels = raw39394step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39394step1 raw39394step1Labels = mixedMoment B raw39394step2 raw39394step2Labels := by
      have ha : raw39394step2 = raw39394step1 := by apply Matrix.ext; unfold raw39394step2 raw39394step1; decide +kernel
      have hl : raw39394step1Labels = labelEmbedding4 ∘ raw39394step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39394step1 raw39394step1Labels raw39394step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw39395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39395Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw39395step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw39395step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39395step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw39395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39395 raw39395Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw39395 raw39395Labels = mixedMoment B raw39395step0 raw39395step0Labels := by
      have ha : raw39395step0 = (fun i j => raw39395 (permutation216 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39395step0 raw39395; decide +kernel
      have hl : raw39395step0Labels = raw39395Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39395 raw39395Labels permutation216 permutation7
    mixedMoment B raw39395step0 raw39395step0Labels = mixedMoment B raw39395step1 raw39395step1Labels := by
      have ha : raw39395step1 = -raw39395step0 := by apply Matrix.ext; change ∀ i j, raw39395step1 i j = -(raw39395step0 i j); unfold raw39395step1 raw39395step0; decide +kernel
      have hl : raw39395step1Labels = raw39395step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39395step1 raw39395step1Labels = mixedMoment B raw39395step2 raw39395step2Labels := by
      have ha : raw39395step2 = raw39395step1 := by apply Matrix.ext; unfold raw39395step2 raw39395step1; decide +kernel
      have hl : raw39395step1Labels = labelEmbedding1 ∘ raw39395step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39395step1 raw39395step1Labels raw39395step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw39396 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39396Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39396 raw39396Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw39396 raw39396Labels = mixedMoment B raw39396step0 raw39396step0Labels := by
      have ha : raw39396step0 = raw39396 := by apply Matrix.ext; unfold raw39396step0 raw39396; decide +kernel
      have hl : raw39396Labels = labelEmbedding2 ∘ raw39396step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39396 raw39396Labels raw39396step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw39397 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39397Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw39397step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39397step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39397 raw39397Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw39397 raw39397Labels = mixedMoment B raw39397step0 raw39397step0Labels := by
      have ha : raw39397step0 = (fun i j => raw39397 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39397step0 raw39397; decide +kernel
      have hl : raw39397step0Labels = raw39397Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39397 raw39397Labels permutation38 permutation7
    mixedMoment B raw39397step0 raw39397step0Labels = mixedMoment B raw39397step1 raw39397step1Labels := by
      have ha : raw39397step1 = -raw39397step0 := by apply Matrix.ext; change ∀ i j, raw39397step1 i j = -(raw39397step0 i j); unfold raw39397step1 raw39397step0; decide +kernel
      have hl : raw39397step1Labels = raw39397step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39397step1 raw39397step1Labels = mixedMoment B raw39397step2 raw39397step2Labels := by
      have ha : raw39397step2 = raw39397step1 := by apply Matrix.ext; unfold raw39397step2 raw39397step1; decide +kernel
      have hl : raw39397step1Labels = labelEmbedding4 ∘ raw39397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39397step1 raw39397step1Labels raw39397step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw39398 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39398Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39398step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39398 raw39398Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw39398 raw39398Labels = mixedMoment B raw39398step0 raw39398step0Labels := by
      have ha : raw39398step0 = raw39398 := by apply Matrix.ext; unfold raw39398step0 raw39398; decide +kernel
      have hl : raw39398Labels = labelEmbedding2 ∘ raw39398step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39398 raw39398Labels raw39398step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw39399 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39399Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39399step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39399step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39399 raw39399Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw39399 raw39399Labels = mixedMoment B raw39399step0 raw39399step0Labels := by
      have ha : raw39399step0 = (fun i j => raw39399 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39399step0 raw39399; decide +kernel
      have hl : raw39399step0Labels = raw39399Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39399 raw39399Labels permutation29 permutation7
    mixedMoment B raw39399step0 raw39399step0Labels = mixedMoment B raw39399step1 raw39399step1Labels := by
      have ha : raw39399step1 = raw39399step0 := by apply Matrix.ext; unfold raw39399step1 raw39399step0; decide +kernel
      have hl : raw39399step0Labels = labelEmbedding4 ∘ raw39399step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39399step0 raw39399step0Labels raw39399step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw39400 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39400Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39400 raw39400Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw39400 raw39400Labels = mixedMoment B raw39400step0 raw39400step0Labels := by
      have ha : raw39400step0 = raw39400 := by apply Matrix.ext; unfold raw39400step0 raw39400; decide +kernel
      have hl : raw39400Labels = labelEmbedding2 ∘ raw39400step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39400 raw39400Labels raw39400step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw39401 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39401Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw39401step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw39401step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw39401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39401 raw39401Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw39401 raw39401Labels = mixedMoment B raw39401step0 raw39401step0Labels := by
      have ha : raw39401step0 = (fun i j => raw39401 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39401step0 raw39401; decide +kernel
      have hl : raw39401step0Labels = raw39401Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39401 raw39401Labels permutation40 permutation7
    mixedMoment B raw39401step0 raw39401step0Labels = mixedMoment B raw39401step1 raw39401step1Labels := by
      have ha : raw39401step1 = -raw39401step0 := by apply Matrix.ext; change ∀ i j, raw39401step1 i j = -(raw39401step0 i j); unfold raw39401step1 raw39401step0; decide +kernel
      have hl : raw39401step1Labels = raw39401step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39401step1 raw39401step1Labels = mixedMoment B raw39401step2 raw39401step2Labels := by
      have ha : raw39401step2 = raw39401step1 := by apply Matrix.ext; unfold raw39401step2 raw39401step1; decide +kernel
      have hl : raw39401step1Labels = labelEmbedding4 ∘ raw39401step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39401step1 raw39401step1Labels raw39401step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw39402 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39402Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39402step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39402 raw39402Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw39402 raw39402Labels = mixedMoment B raw39402step0 raw39402step0Labels := by
      have ha : raw39402step0 = raw39402 := by apply Matrix.ext; unfold raw39402step0 raw39402; decide +kernel
      have hl : raw39402Labels = labelEmbedding2 ∘ raw39402step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39402 raw39402Labels raw39402step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw39403 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39403Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39403step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw39403step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw39403step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39403step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw39403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39403 raw39403Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw39403 raw39403Labels = mixedMoment B raw39403step0 raw39403step0Labels := by
      have ha : raw39403step0 = (fun i j => raw39403 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39403step0 raw39403; decide +kernel
      have hl : raw39403step0Labels = raw39403Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39403 raw39403Labels permutation10 permutation7
    mixedMoment B raw39403step0 raw39403step0Labels = mixedMoment B raw39403step1 raw39403step1Labels := by
      have ha : raw39403step1 = -raw39403step0 := by apply Matrix.ext; change ∀ i j, raw39403step1 i j = -(raw39403step0 i j); unfold raw39403step1 raw39403step0; decide +kernel
      have hl : raw39403step1Labels = raw39403step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39403step1 raw39403step1Labels = mixedMoment B raw39403step2 raw39403step2Labels := by
      have ha : raw39403step2 = raw39403step1 := by apply Matrix.ext; unfold raw39403step2 raw39403step1; decide +kernel
      have hl : raw39403step1Labels = labelEmbedding4 ∘ raw39403step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39403step1 raw39403step1Labels raw39403step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw39404 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39404Labels : Fin 3 → Fin 3 := ![1, 1, 2]

def raw39404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39404 raw39404Labels = mixedMoment B node3911 node3911Labels := by
  calc
    mixedMoment B raw39404 raw39404Labels = mixedMoment B raw39404step0 raw39404step0Labels := by
      have ha : raw39404step0 = raw39404 := by apply Matrix.ext; unfold raw39404step0 raw39404; decide +kernel
      have hl : raw39404Labels = labelEmbedding3 ∘ raw39404step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39404 raw39404Labels raw39404step0Labels labelEmbedding3 hl
    _ = mixedMoment B node3911 node3911Labels := by rfl

def raw39405 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39405Labels : Fin 3 → Fin 3 := ![2, 1, 2]

def raw39405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39405step0Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39405 raw39405Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw39405 raw39405Labels = mixedMoment B raw39405step0 raw39405step0Labels := by
      have ha : raw39405step0 = (fun i j => raw39405 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39405step0 raw39405; decide +kernel
      have hl : raw39405step0Labels = raw39405Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39405 raw39405Labels permutation32 permutation3
    mixedMoment B raw39405step0 raw39405step0Labels = mixedMoment B raw39405step1 raw39405step1Labels := by
      have ha : raw39405step1 = raw39405step0 := by apply Matrix.ext; unfold raw39405step1 raw39405step0; decide +kernel
      have hl : raw39405step0Labels = labelEmbedding5 ∘ raw39405step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39405step0 raw39405step0Labels raw39405step1Labels labelEmbedding5 hl
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw39406 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39406Labels : Fin 3 → Fin 3 := ![1, 1, 2]

def raw39406step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39406 raw39406Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw39406 raw39406Labels = mixedMoment B raw39406step0 raw39406step0Labels := by
      have ha : raw39406step0 = raw39406 := by apply Matrix.ext; unfold raw39406step0 raw39406; decide +kernel
      have hl : raw39406Labels = labelEmbedding3 ∘ raw39406step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39406 raw39406Labels raw39406step0Labels labelEmbedding3 hl
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw39407 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39407Labels : Fin 3 → Fin 3 := ![2, 1, 2]

def raw39407step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw39407step0Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39407step1Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39407step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw39407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39407 raw39407Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw39407 raw39407Labels = mixedMoment B raw39407step0 raw39407step0Labels := by
      have ha : raw39407step0 = (fun i j => raw39407 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39407step0 raw39407; decide +kernel
      have hl : raw39407step0Labels = raw39407Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39407 raw39407Labels permutation29 permutation3
    mixedMoment B raw39407step0 raw39407step0Labels = mixedMoment B raw39407step1 raw39407step1Labels := by
      have ha : raw39407step1 = -raw39407step0 := by apply Matrix.ext; change ∀ i j, raw39407step1 i j = -(raw39407step0 i j); unfold raw39407step1 raw39407step0; decide +kernel
      have hl : raw39407step1Labels = raw39407step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39407step1 raw39407step1Labels = mixedMoment B raw39407step2 raw39407step2Labels := by
      have ha : raw39407step2 = raw39407step1 := by apply Matrix.ext; unfold raw39407step2 raw39407step1; decide +kernel
      have hl : raw39407step1Labels = labelEmbedding5 ∘ raw39407step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39407step1 raw39407step1Labels raw39407step2Labels labelEmbedding5 hl
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw39408 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw39408Labels : Fin 3 → Fin 3 := ![1, 1, 2]

def raw39408step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw39408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39408 raw39408Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw39408 raw39408Labels = mixedMoment B raw39408step0 raw39408step0Labels := by
      have ha : raw39408step0 = raw39408 := by apply Matrix.ext; unfold raw39408step0 raw39408; decide +kernel
      have hl : raw39408Labels = labelEmbedding3 ∘ raw39408step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39408 raw39408Labels raw39408step0Labels labelEmbedding3 hl
    _ = mixedMoment B node3916 node3916Labels := by rfl

def raw39409 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw39409Labels : Fin 3 → Fin 3 := ![2, 1, 2]

def raw39409step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw39409step0Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39409step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw39409step1Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39409step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw39409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39409 raw39409Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw39409 raw39409Labels = mixedMoment B raw39409step0 raw39409step0Labels := by
      have ha : raw39409step0 = (fun i j => raw39409 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39409step0 raw39409; decide +kernel
      have hl : raw39409step0Labels = raw39409Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39409 raw39409Labels permutation7 permutation3
    mixedMoment B raw39409step0 raw39409step0Labels = mixedMoment B raw39409step1 raw39409step1Labels := by
      have ha : raw39409step1 = -raw39409step0 := by apply Matrix.ext; change ∀ i j, raw39409step1 i j = -(raw39409step0 i j); unfold raw39409step1 raw39409step0; decide +kernel
      have hl : raw39409step1Labels = raw39409step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39409step1 raw39409step1Labels = mixedMoment B raw39409step2 raw39409step2Labels := by
      have ha : raw39409step2 = raw39409step1 := by apply Matrix.ext; unfold raw39409step2 raw39409step1; decide +kernel
      have hl : raw39409step1Labels = labelEmbedding5 ∘ raw39409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39409step1 raw39409step1Labels raw39409step2Labels labelEmbedding5 hl
    _ = mixedMoment B node3916 node3916Labels := by rfl

def raw39410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39410Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39410 raw39410Labels = mixedMoment B node3930 node3930Labels := by
  calc
    mixedMoment B raw39410 raw39410Labels = mixedMoment B raw39410step0 raw39410step0Labels := by
      have ha : raw39410step0 = raw39410 := by apply Matrix.ext; unfold raw39410step0 raw39410; decide +kernel
      have hl : raw39410Labels = labelEmbedding2 ∘ raw39410step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39410 raw39410Labels raw39410step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3930 node3930Labels := by rfl

def raw39411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39411Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw39411step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39411step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39411step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39411 raw39411Labels = mixedMoment B node4041 node4041Labels := by
  calc
    mixedMoment B raw39411 raw39411Labels = mixedMoment B raw39411step0 raw39411step0Labels := by
      have ha : raw39411step0 = (fun i j => raw39411 (permutation168 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39411step0 raw39411; decide +kernel
      have hl : raw39411step0Labels = raw39411Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39411 raw39411Labels permutation168 permutation5
    mixedMoment B raw39411step0 raw39411step0Labels = mixedMoment B raw39411step1 raw39411step1Labels := by
      have ha : raw39411step1 = -raw39411step0 := by apply Matrix.ext; change ∀ i j, raw39411step1 i j = -(raw39411step0 i j); unfold raw39411step1 raw39411step0; decide +kernel
      have hl : raw39411step1Labels = raw39411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39411step1 raw39411step1Labels = mixedMoment B raw39411step2 raw39411step2Labels := by
      have ha : raw39411step2 = raw39411step1 := by apply Matrix.ext; unfold raw39411step2 raw39411step1; decide +kernel
      have hl : raw39411step1Labels = labelEmbedding4 ∘ raw39411step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39411step1 raw39411step1Labels raw39411step2Labels labelEmbedding4 hl
    _ = mixedMoment B node4041 node4041Labels := by rfl

def raw39412 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39412Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39412 raw39412Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw39412 raw39412Labels = mixedMoment B raw39412step0 raw39412step0Labels := by
      have ha : raw39412step0 = raw39412 := by apply Matrix.ext; unfold raw39412step0 raw39412; decide +kernel
      have hl : raw39412Labels = labelEmbedding2 ∘ raw39412step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39412 raw39412Labels raw39412step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw39413 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39413Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39413step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39413step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39413 raw39413Labels = mixedMoment B node4042 node4042Labels := by
  calc
    mixedMoment B raw39413 raw39413Labels = mixedMoment B raw39413step0 raw39413step0Labels := by
      have ha : raw39413step0 = (fun i j => raw39413 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39413step0 raw39413; decide +kernel
      have hl : raw39413step0Labels = raw39413Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39413 raw39413Labels permutation34 permutation5
    mixedMoment B raw39413step0 raw39413step0Labels = mixedMoment B raw39413step1 raw39413step1Labels := by
      have ha : raw39413step1 = -raw39413step0 := by apply Matrix.ext; change ∀ i j, raw39413step1 i j = -(raw39413step0 i j); unfold raw39413step1 raw39413step0; decide +kernel
      have hl : raw39413step1Labels = raw39413step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39413step1 raw39413step1Labels = mixedMoment B raw39413step2 raw39413step2Labels := by
      have ha : raw39413step2 = raw39413step1 := by apply Matrix.ext; unfold raw39413step2 raw39413step1; decide +kernel
      have hl : raw39413step1Labels = labelEmbedding4 ∘ raw39413step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39413step1 raw39413step1Labels raw39413step2Labels labelEmbedding4 hl
    _ = mixedMoment B node4042 node4042Labels := by rfl

def raw39414 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw39414Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39414step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw39414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39414 raw39414Labels = mixedMoment B node3934 node3934Labels := by
  calc
    mixedMoment B raw39414 raw39414Labels = mixedMoment B raw39414step0 raw39414step0Labels := by
      have ha : raw39414step0 = raw39414 := by apply Matrix.ext; unfold raw39414step0 raw39414; decide +kernel
      have hl : raw39414Labels = labelEmbedding2 ∘ raw39414step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39414 raw39414Labels raw39414step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3934 node3934Labels := by rfl

def raw39415 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw39415Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39415step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39415step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39415 raw39415Labels = mixedMoment B node4043 node4043Labels := by
  calc
    mixedMoment B raw39415 raw39415Labels = mixedMoment B raw39415step0 raw39415step0Labels := by
      have ha : raw39415step0 = (fun i j => raw39415 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39415step0 raw39415; decide +kernel
      have hl : raw39415step0Labels = raw39415Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39415 raw39415Labels permutation24 permutation5
    mixedMoment B raw39415step0 raw39415step0Labels = mixedMoment B raw39415step1 raw39415step1Labels := by
      have ha : raw39415step1 = raw39415step0 := by apply Matrix.ext; unfold raw39415step1 raw39415step0; decide +kernel
      have hl : raw39415step0Labels = labelEmbedding4 ∘ raw39415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39415step0 raw39415step0Labels raw39415step1Labels labelEmbedding4 hl
    _ = mixedMoment B node4043 node4043Labels := by rfl

def raw39416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39416Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39416 raw39416Labels = mixedMoment B node3942 node3942Labels := by
  calc
    mixedMoment B raw39416 raw39416Labels = mixedMoment B raw39416step0 raw39416step0Labels := by
      have ha : raw39416step0 = raw39416 := by apply Matrix.ext; unfold raw39416step0 raw39416; decide +kernel
      have hl : raw39416Labels = labelEmbedding2 ∘ raw39416step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39416 raw39416Labels raw39416step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3942 node3942Labels := by rfl

def raw39417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39417Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39417step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39417 raw39417Labels = mixedMoment B node3942 node3942Labels := by
  calc
    mixedMoment B raw39417 raw39417Labels = mixedMoment B raw39417step0 raw39417step0Labels := by
      have ha : raw39417step0 = (fun i j => raw39417 (permutation588 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39417step0 raw39417; decide +kernel
      have hl : raw39417step0Labels = raw39417Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39417 raw39417Labels permutation588 permutation7
    mixedMoment B raw39417step0 raw39417step0Labels = mixedMoment B raw39417step1 raw39417step1Labels := by
      have ha : raw39417step1 = raw39417step0 := by apply Matrix.ext; unfold raw39417step1 raw39417step0; decide +kernel
      have hl : raw39417step0Labels = labelEmbedding4 ∘ raw39417step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39417step0 raw39417step0Labels raw39417step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3942 node3942Labels := by rfl

def raw39418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39418Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39418 raw39418Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw39418 raw39418Labels = mixedMoment B raw39418step0 raw39418step0Labels := by
      have ha : raw39418step0 = raw39418 := by apply Matrix.ext; unfold raw39418step0 raw39418; decide +kernel
      have hl : raw39418Labels = labelEmbedding2 ∘ raw39418step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39418 raw39418Labels raw39418step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3945 node3945Labels := by rfl

def raw39419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39419Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39419step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39419step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39419step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39419 raw39419Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw39419 raw39419Labels = mixedMoment B raw39419step0 raw39419step0Labels := by
      have ha : raw39419step0 = (fun i j => raw39419 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39419step0 raw39419; decide +kernel
      have hl : raw39419step0Labels = raw39419Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39419 raw39419Labels permutation265 permutation7
    mixedMoment B raw39419step0 raw39419step0Labels = mixedMoment B raw39419step1 raw39419step1Labels := by
      have ha : raw39419step1 = -raw39419step0 := by apply Matrix.ext; change ∀ i j, raw39419step1 i j = -(raw39419step0 i j); unfold raw39419step1 raw39419step0; decide +kernel
      have hl : raw39419step1Labels = raw39419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39419step1 raw39419step1Labels = mixedMoment B raw39419step2 raw39419step2Labels := by
      have ha : raw39419step2 = raw39419step1 := by apply Matrix.ext; unfold raw39419step2 raw39419step1; decide +kernel
      have hl : raw39419step1Labels = labelEmbedding4 ∘ raw39419step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39419step1 raw39419step1Labels raw39419step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

def raw39420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39420Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39420 raw39420Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw39420 raw39420Labels = mixedMoment B raw39420step0 raw39420step0Labels := by
      have ha : raw39420step0 = raw39420 := by apply Matrix.ext; unfold raw39420step0 raw39420; decide +kernel
      have hl : raw39420Labels = labelEmbedding2 ∘ raw39420step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39420 raw39420Labels raw39420step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw39421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39421Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39421step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39421step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39421step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39421 raw39421Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw39421 raw39421Labels = mixedMoment B raw39421step0 raw39421step0Labels := by
      have ha : raw39421step0 = (fun i j => raw39421 (permutation271 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39421step0 raw39421; decide +kernel
      have hl : raw39421step0Labels = raw39421Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39421 raw39421Labels permutation271 permutation7
    mixedMoment B raw39421step0 raw39421step0Labels = mixedMoment B raw39421step1 raw39421step1Labels := by
      have ha : raw39421step1 = -raw39421step0 := by apply Matrix.ext; change ∀ i j, raw39421step1 i j = -(raw39421step0 i j); unfold raw39421step1 raw39421step0; decide +kernel
      have hl : raw39421step1Labels = raw39421step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39421step1 raw39421step1Labels = mixedMoment B raw39421step2 raw39421step2Labels := by
      have ha : raw39421step2 = raw39421step1 := by apply Matrix.ext; unfold raw39421step2 raw39421step1; decide +kernel
      have hl : raw39421step1Labels = labelEmbedding4 ∘ raw39421step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39421step1 raw39421step1Labels raw39421step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw39422 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39422Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39422 raw39422Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw39422 raw39422Labels = mixedMoment B raw39422step0 raw39422step0Labels := by
      have ha : raw39422step0 = raw39422 := by apply Matrix.ext; unfold raw39422step0 raw39422; decide +kernel
      have hl : raw39422Labels = labelEmbedding2 ∘ raw39422step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39422 raw39422Labels raw39422step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw39423 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39423Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw39423step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39423step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39423 raw39423Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw39423 raw39423Labels = mixedMoment B raw39423step0 raw39423step0Labels := by
      have ha : raw39423step0 = (fun i j => raw39423 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39423step0 raw39423; decide +kernel
      have hl : raw39423step0Labels = raw39423Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39423 raw39423Labels permutation56 permutation7
    mixedMoment B raw39423step0 raw39423step0Labels = mixedMoment B raw39423step1 raw39423step1Labels := by
      have ha : raw39423step1 = -raw39423step0 := by apply Matrix.ext; change ∀ i j, raw39423step1 i j = -(raw39423step0 i j); unfold raw39423step1 raw39423step0; decide +kernel
      have hl : raw39423step1Labels = raw39423step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39423step1 raw39423step1Labels = mixedMoment B raw39423step2 raw39423step2Labels := by
      have ha : raw39423step2 = raw39423step1 := by apply Matrix.ext; unfold raw39423step2 raw39423step1; decide +kernel
      have hl : raw39423step1Labels = labelEmbedding4 ∘ raw39423step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39423step1 raw39423step1Labels raw39423step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
