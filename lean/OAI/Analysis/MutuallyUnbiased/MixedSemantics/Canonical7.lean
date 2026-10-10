import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw896 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw896Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw896step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw896 raw896Labels = mixedMoment B node753 node753Labels := by
  calc
    mixedMoment B raw896 raw896Labels = mixedMoment B raw896step0 raw896step0Labels := by
      have ha : raw896step0 = (fun i j => raw896 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw896step0 raw896; decide +kernel
      have hl : raw896step0Labels = raw896Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw896 raw896Labels permutation32 permutation6
    mixedMoment B raw896step0 raw896step0Labels = mixedMoment B raw896step1 raw896step1Labels := by
      have ha : raw896step1 = -raw896step0 := by apply Matrix.ext; change ∀ i j, raw896step1 i j = -(raw896step0 i j); unfold raw896step1 raw896step0; decide +kernel
      have hl : raw896step1Labels = raw896step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw896step1 raw896step1Labels = mixedMoment B raw896step2 raw896step2Labels := by
      have ha : raw896step2 = raw896step1 := by apply Matrix.ext; unfold raw896step2 raw896step1; decide +kernel
      have hl : raw896step1Labels = labelEmbedding1 ∘ raw896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw896step1 raw896step1Labels raw896step2Labels labelEmbedding1 hl
    _ = mixedMoment B node753 node753Labels := by rfl

def raw897 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw897step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw897 raw897Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw897 raw897Labels = mixedMoment B raw897step0 raw897step0Labels := by
      have ha : raw897step0 = (fun i j => raw897 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw897step0 raw897; decide +kernel
      have hl : raw897step0Labels = raw897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw897 raw897Labels permutation32 permutation4
    mixedMoment B raw897step0 raw897step0Labels = mixedMoment B raw897step1 raw897step1Labels := by
      have ha : raw897step1 = raw897step0 := by apply Matrix.ext; unfold raw897step1 raw897step0; decide +kernel
      have hl : raw897step0Labels = labelEmbedding7 ∘ raw897step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw897step0 raw897step0Labels raw897step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

def raw898 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw898 raw898Labels = mixedMoment B node716 node716Labels := by
  calc
    mixedMoment B raw898 raw898Labels = mixedMoment B raw898step0 raw898step0Labels := by
      have ha : raw898step0 = (fun i j => raw898 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw898step0 raw898; decide +kernel
      have hl : raw898step0Labels = raw898Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw898 raw898Labels permutation32 permutation4
    _ = mixedMoment B node716 node716Labels := by rfl

def raw899 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw899Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw899step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw899 raw899Labels = mixedMoment B node752 node752Labels := by
  calc
    mixedMoment B raw899 raw899Labels = mixedMoment B raw899step0 raw899step0Labels := by
      have ha : raw899step0 = (fun i j => raw899 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw899step0 raw899; decide +kernel
      have hl : raw899step0Labels = raw899Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw899 raw899Labels permutation32 permutation6
    mixedMoment B raw899step0 raw899step0Labels = mixedMoment B raw899step1 raw899step1Labels := by
      have ha : raw899step1 = -raw899step0 := by apply Matrix.ext; change ∀ i j, raw899step1 i j = -(raw899step0 i j); unfold raw899step1 raw899step0; decide +kernel
      have hl : raw899step1Labels = raw899step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw899step1 raw899step1Labels = mixedMoment B raw899step2 raw899step2Labels := by
      have ha : raw899step2 = raw899step1 := by apply Matrix.ext; unfold raw899step2 raw899step1; decide +kernel
      have hl : raw899step1Labels = labelEmbedding1 ∘ raw899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw899step1 raw899step1Labels raw899step2Labels labelEmbedding1 hl
    _ = mixedMoment B node752 node752Labels := by rfl

def raw900 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw900step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw900 raw900Labels = mixedMoment B node4217 node4217Labels := by
  calc
    mixedMoment B raw900 raw900Labels = mixedMoment B raw900step0 raw900step0Labels := by
      have ha : raw900step0 = (fun i j => raw900 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw900step0 raw900; decide +kernel
      have hl : raw900step0Labels = raw900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw900 raw900Labels permutation152 permutation4
    mixedMoment B raw900step0 raw900step0Labels = mixedMoment B raw900step1 raw900step1Labels := by
      have ha : raw900step1 = raw900step0 := by apply Matrix.ext; unfold raw900step1 raw900step0; decide +kernel
      have hl : raw900step0Labels = labelEmbedding7 ∘ raw900step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw900step0 raw900step0Labels raw900step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4217 node4217Labels := by rfl

def raw901 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw901Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw901 raw901Labels = mixedMoment B node719 node719Labels := by
  calc
    mixedMoment B raw901 raw901Labels = mixedMoment B raw901step0 raw901step0Labels := by
      have ha : raw901step0 = (fun i j => raw901 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw901step0 raw901; decide +kernel
      have hl : raw901step0Labels = raw901Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw901 raw901Labels permutation152 permutation4
    _ = mixedMoment B node719 node719Labels := by rfl

def raw902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw902Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw902step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw902step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw902 raw902Labels = mixedMoment B node756 node756Labels := by
  calc
    mixedMoment B raw902 raw902Labels = mixedMoment B raw902step0 raw902step0Labels := by
      have ha : raw902step0 = (fun i j => raw902 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw902step0 raw902; decide +kernel
      have hl : raw902step0Labels = raw902Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw902 raw902Labels permutation170 permutation6
    mixedMoment B raw902step0 raw902step0Labels = mixedMoment B raw902step1 raw902step1Labels := by
      have ha : raw902step1 = -raw902step0 := by apply Matrix.ext; change ∀ i j, raw902step1 i j = -(raw902step0 i j); unfold raw902step1 raw902step0; decide +kernel
      have hl : raw902step1Labels = raw902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw902step1 raw902step1Labels = mixedMoment B raw902step2 raw902step2Labels := by
      have ha : raw902step2 = raw902step1 := by apply Matrix.ext; unfold raw902step2 raw902step1; decide +kernel
      have hl : raw902step1Labels = labelEmbedding1 ∘ raw902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw902step1 raw902step1Labels raw902step2Labels labelEmbedding1 hl
    _ = mixedMoment B node756 node756Labels := by rfl

def raw903 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw903step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw903 raw903Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw903 raw903Labels = mixedMoment B raw903step0 raw903step0Labels := by
      have ha : raw903step0 = (fun i j => raw903 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw903step0 raw903; decide +kernel
      have hl : raw903step0Labels = raw903Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw903 raw903Labels permutation32 permutation4
    mixedMoment B raw903step0 raw903step0Labels = mixedMoment B raw903step1 raw903step1Labels := by
      have ha : raw903step1 = raw903step0 := by apply Matrix.ext; unfold raw903step1 raw903step0; decide +kernel
      have hl : raw903step0Labels = labelEmbedding7 ∘ raw903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw903step0 raw903step0Labels raw903step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4219 node4219Labels := by rfl

def raw904 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw904 raw904Labels = mixedMoment B node720 node720Labels := by
  calc
    mixedMoment B raw904 raw904Labels = mixedMoment B raw904step0 raw904step0Labels := by
      have ha : raw904step0 = (fun i j => raw904 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw904step0 raw904; decide +kernel
      have hl : raw904step0Labels = raw904Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw904 raw904Labels permutation32 permutation4
    _ = mixedMoment B node720 node720Labels := by rfl

def raw905 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw905Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw905step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw905step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw905 raw905Labels = mixedMoment B node769 node769Labels := by
  calc
    mixedMoment B raw905 raw905Labels = mixedMoment B raw905step0 raw905step0Labels := by
      have ha : raw905step0 = (fun i j => raw905 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw905step0 raw905; decide +kernel
      have hl : raw905step0Labels = raw905Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw905 raw905Labels permutation33 permutation6
    mixedMoment B raw905step0 raw905step0Labels = mixedMoment B raw905step1 raw905step1Labels := by
      have ha : raw905step1 = -raw905step0 := by apply Matrix.ext; change ∀ i j, raw905step1 i j = -(raw905step0 i j); unfold raw905step1 raw905step0; decide +kernel
      have hl : raw905step1Labels = raw905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw905step1 raw905step1Labels = mixedMoment B raw905step2 raw905step2Labels := by
      have ha : raw905step2 = raw905step1 := by apply Matrix.ext; unfold raw905step2 raw905step1; decide +kernel
      have hl : raw905step1Labels = labelEmbedding1 ∘ raw905step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw905step1 raw905step1Labels raw905step2Labels labelEmbedding1 hl
    _ = mixedMoment B node769 node769Labels := by rfl

def raw906 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw906step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw906 raw906Labels = mixedMoment B node4220 node4220Labels := by
  calc
    mixedMoment B raw906 raw906Labels = mixedMoment B raw906step0 raw906step0Labels := by
      have ha : raw906step0 = (fun i j => raw906 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw906step0 raw906; decide +kernel
      have hl : raw906step0Labels = raw906Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw906 raw906Labels permutation32 permutation4
    mixedMoment B raw906step0 raw906step0Labels = mixedMoment B raw906step1 raw906step1Labels := by
      have ha : raw906step1 = raw906step0 := by apply Matrix.ext; unfold raw906step1 raw906step0; decide +kernel
      have hl : raw906step0Labels = labelEmbedding7 ∘ raw906step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw906step0 raw906step0Labels raw906step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4220 node4220Labels := by rfl

def raw907 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw907 raw907Labels = mixedMoment B node721 node721Labels := by
  calc
    mixedMoment B raw907 raw907Labels = mixedMoment B raw907step0 raw907step0Labels := by
      have ha : raw907step0 = (fun i j => raw907 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw907step0 raw907; decide +kernel
      have hl : raw907step0Labels = raw907Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw907 raw907Labels permutation32 permutation4
    _ = mixedMoment B node721 node721Labels := by rfl

def raw908 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw908Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw908step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw908step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw908 raw908Labels = mixedMoment B node757 node757Labels := by
  calc
    mixedMoment B raw908 raw908Labels = mixedMoment B raw908step0 raw908step0Labels := by
      have ha : raw908step0 = (fun i j => raw908 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw908step0 raw908; decide +kernel
      have hl : raw908step0Labels = raw908Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw908 raw908Labels permutation34 permutation6
    mixedMoment B raw908step0 raw908step0Labels = mixedMoment B raw908step1 raw908step1Labels := by
      have ha : raw908step1 = -raw908step0 := by apply Matrix.ext; change ∀ i j, raw908step1 i j = -(raw908step0 i j); unfold raw908step1 raw908step0; decide +kernel
      have hl : raw908step1Labels = raw908step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw908step1 raw908step1Labels = mixedMoment B raw908step2 raw908step2Labels := by
      have ha : raw908step2 = raw908step1 := by apply Matrix.ext; unfold raw908step2 raw908step1; decide +kernel
      have hl : raw908step1Labels = labelEmbedding1 ∘ raw908step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw908step1 raw908step1Labels raw908step2Labels labelEmbedding1 hl
    _ = mixedMoment B node757 node757Labels := by rfl

def raw909 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw909step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw909 raw909Labels = mixedMoment B node4223 node4223Labels := by
  calc
    mixedMoment B raw909 raw909Labels = mixedMoment B raw909step0 raw909step0Labels := by
      have ha : raw909step0 = (fun i j => raw909 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw909step0 raw909; decide +kernel
      have hl : raw909step0Labels = raw909Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw909 raw909Labels permutation32 permutation4
    mixedMoment B raw909step0 raw909step0Labels = mixedMoment B raw909step1 raw909step1Labels := by
      have ha : raw909step1 = raw909step0 := by apply Matrix.ext; unfold raw909step1 raw909step0; decide +kernel
      have hl : raw909step0Labels = labelEmbedding7 ∘ raw909step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw909step0 raw909step0Labels raw909step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4223 node4223Labels := by rfl

def raw910 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw910 raw910Labels = mixedMoment B node724 node724Labels := by
  calc
    mixedMoment B raw910 raw910Labels = mixedMoment B raw910step0 raw910step0Labels := by
      have ha : raw910step0 = (fun i j => raw910 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw910step0 raw910; decide +kernel
      have hl : raw910step0Labels = raw910Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw910 raw910Labels permutation32 permutation4
    _ = mixedMoment B node724 node724Labels := by rfl

def raw911 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw911Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw911step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw911step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw911 raw911Labels = mixedMoment B node758 node758Labels := by
  calc
    mixedMoment B raw911 raw911Labels = mixedMoment B raw911step0 raw911step0Labels := by
      have ha : raw911step0 = (fun i j => raw911 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw911step0 raw911; decide +kernel
      have hl : raw911step0Labels = raw911Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw911 raw911Labels permutation34 permutation6
    mixedMoment B raw911step0 raw911step0Labels = mixedMoment B raw911step1 raw911step1Labels := by
      have ha : raw911step1 = -raw911step0 := by apply Matrix.ext; change ∀ i j, raw911step1 i j = -(raw911step0 i j); unfold raw911step1 raw911step0; decide +kernel
      have hl : raw911step1Labels = raw911step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw911step1 raw911step1Labels = mixedMoment B raw911step2 raw911step2Labels := by
      have ha : raw911step2 = raw911step1 := by apply Matrix.ext; unfold raw911step2 raw911step1; decide +kernel
      have hl : raw911step1Labels = labelEmbedding1 ∘ raw911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw911step1 raw911step1Labels raw911step2Labels labelEmbedding1 hl
    _ = mixedMoment B node758 node758Labels := by rfl

def raw912 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw912step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw912 raw912Labels = mixedMoment B node4224 node4224Labels := by
  calc
    mixedMoment B raw912 raw912Labels = mixedMoment B raw912step0 raw912step0Labels := by
      have ha : raw912step0 = (fun i j => raw912 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw912step0 raw912; decide +kernel
      have hl : raw912step0Labels = raw912Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw912 raw912Labels permutation32 permutation4
    mixedMoment B raw912step0 raw912step0Labels = mixedMoment B raw912step1 raw912step1Labels := by
      have ha : raw912step1 = raw912step0 := by apply Matrix.ext; unfold raw912step1 raw912step0; decide +kernel
      have hl : raw912step0Labels = labelEmbedding7 ∘ raw912step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw912step0 raw912step0Labels raw912step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4224 node4224Labels := by rfl

def raw913 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw913 raw913Labels = mixedMoment B node725 node725Labels := by
  calc
    mixedMoment B raw913 raw913Labels = mixedMoment B raw913step0 raw913step0Labels := by
      have ha : raw913step0 = (fun i j => raw913 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw913step0 raw913; decide +kernel
      have hl : raw913step0Labels = raw913Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw913 raw913Labels permutation32 permutation4
    _ = mixedMoment B node725 node725Labels := by rfl

def raw914 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw914Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw914step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw914step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw914 raw914Labels = mixedMoment B node771 node771Labels := by
  calc
    mixedMoment B raw914 raw914Labels = mixedMoment B raw914step0 raw914step0Labels := by
      have ha : raw914step0 = (fun i j => raw914 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw914step0 raw914; decide +kernel
      have hl : raw914step0Labels = raw914Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw914 raw914Labels permutation35 permutation6
    mixedMoment B raw914step0 raw914step0Labels = mixedMoment B raw914step1 raw914step1Labels := by
      have ha : raw914step1 = -raw914step0 := by apply Matrix.ext; change ∀ i j, raw914step1 i j = -(raw914step0 i j); unfold raw914step1 raw914step0; decide +kernel
      have hl : raw914step1Labels = raw914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw914step1 raw914step1Labels = mixedMoment B raw914step2 raw914step2Labels := by
      have ha : raw914step2 = raw914step1 := by apply Matrix.ext; unfold raw914step2 raw914step1; decide +kernel
      have hl : raw914step1Labels = labelEmbedding1 ∘ raw914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw914step1 raw914step1Labels raw914step2Labels labelEmbedding1 hl
    _ = mixedMoment B node771 node771Labels := by rfl

def raw915 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 4, -2]]
def raw915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw915step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw915step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw915 raw915Labels = mixedMoment B node4225 node4225Labels := by
  calc
    mixedMoment B raw915 raw915Labels = mixedMoment B raw915step0 raw915step0Labels := by
      have ha : raw915step0 = (fun i j => raw915 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw915step0 raw915; decide +kernel
      have hl : raw915step0Labels = raw915Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw915 raw915Labels permutation8 permutation4
    mixedMoment B raw915step0 raw915step0Labels = mixedMoment B raw915step1 raw915step1Labels := by
      have ha : raw915step1 = raw915step0 := by apply Matrix.ext; unfold raw915step1 raw915step0; decide +kernel
      have hl : raw915step0Labels = labelEmbedding7 ∘ raw915step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw915step0 raw915step0Labels raw915step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4225 node4225Labels := by rfl

def raw916 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 4, -2]]
def raw916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw916step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw916 raw916Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw916 raw916Labels = mixedMoment B raw916step0 raw916step0Labels := by
      have ha : raw916step0 = (fun i j => raw916 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw916step0 raw916; decide +kernel
      have hl : raw916step0Labels = raw916Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw916 raw916Labels permutation8 permutation4
    _ = mixedMoment B node726 node726Labels := by rfl

def raw917 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 1, -2], ![-2, 4, -2]]
def raw917Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw917step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-2, 1, 1], ![-2, -2, 4]]
def raw917step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw917step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw917 raw917Labels = mixedMoment B node774 node774Labels := by
  calc
    mixedMoment B raw917 raw917Labels = mixedMoment B raw917step0 raw917step0Labels := by
      have ha : raw917step0 = (fun i j => raw917 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw917step0 raw917; decide +kernel
      have hl : raw917step0Labels = raw917Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw917 raw917Labels permutation8 permutation6
    mixedMoment B raw917step0 raw917step0Labels = mixedMoment B raw917step1 raw917step1Labels := by
      have ha : raw917step1 = -raw917step0 := by apply Matrix.ext; change ∀ i j, raw917step1 i j = -(raw917step0 i j); unfold raw917step1 raw917step0; decide +kernel
      have hl : raw917step1Labels = raw917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw917step1 raw917step1Labels = mixedMoment B raw917step2 raw917step2Labels := by
      have ha : raw917step2 = raw917step1 := by apply Matrix.ext; unfold raw917step2 raw917step1; decide +kernel
      have hl : raw917step1Labels = labelEmbedding1 ∘ raw917step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw917step1 raw917step1Labels raw917step2Labels labelEmbedding1 hl
    _ = mixedMoment B node774 node774Labels := by rfl

def raw918 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-2, 2, 0], ![1, 3, -4]]
def raw918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw918step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw918step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw918step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw918 raw918Labels = mixedMoment B node4226 node4226Labels := by
  calc
    mixedMoment B raw918 raw918Labels = mixedMoment B raw918step0 raw918step0Labels := by
      have ha : raw918step0 = (fun i j => raw918 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw918step0 raw918; decide +kernel
      have hl : raw918step0Labels = raw918Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw918 raw918Labels permutation8 permutation4
    mixedMoment B raw918step0 raw918step0Labels = mixedMoment B raw918step1 raw918step1Labels := by
      have ha : raw918step1 = raw918step0 := by apply Matrix.ext; unfold raw918step1 raw918step0; decide +kernel
      have hl : raw918step0Labels = labelEmbedding7 ∘ raw918step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw918step0 raw918step0Labels raw918step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4226 node4226Labels := by rfl

def raw919 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-2, 2, 0], ![1, 3, -4]]
def raw919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw919step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw919 raw919Labels = mixedMoment B node727 node727Labels := by
  calc
    mixedMoment B raw919 raw919Labels = mixedMoment B raw919step0 raw919step0Labels := by
      have ha : raw919step0 = (fun i j => raw919 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw919step0 raw919; decide +kernel
      have hl : raw919step0Labels = raw919Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw919 raw919Labels permutation8 permutation4
    _ = mixedMoment B node727 node727Labels := by rfl

def raw920 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![-2, 2, 0], ![1, 3, -4]]
def raw920Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw920step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-4, 1, 3]]
def raw920step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![4, -1, -3]]
def raw920step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw920step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![4, -1, -3]]
def raw920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw920 raw920Labels = mixedMoment B node759 node759Labels := by
  calc
    mixedMoment B raw920 raw920Labels = mixedMoment B raw920step0 raw920step0Labels := by
      have ha : raw920step0 = (fun i j => raw920 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw920step0 raw920; decide +kernel
      have hl : raw920step0Labels = raw920Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw920 raw920Labels permutation8 permutation6
    mixedMoment B raw920step0 raw920step0Labels = mixedMoment B raw920step1 raw920step1Labels := by
      have ha : raw920step1 = -raw920step0 := by apply Matrix.ext; change ∀ i j, raw920step1 i j = -(raw920step0 i j); unfold raw920step1 raw920step0; decide +kernel
      have hl : raw920step1Labels = raw920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw920step1 raw920step1Labels = mixedMoment B raw920step2 raw920step2Labels := by
      have ha : raw920step2 = raw920step1 := by apply Matrix.ext; unfold raw920step2 raw920step1; decide +kernel
      have hl : raw920step1Labels = labelEmbedding1 ∘ raw920step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw920step1 raw920step1Labels raw920step2Labels labelEmbedding1 hl
    _ = mixedMoment B node759 node759Labels := by rfl

def raw921 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw921step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw921step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw921 raw921Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw921 raw921Labels = mixedMoment B raw921step0 raw921step0Labels := by
      have ha : raw921step0 = (fun i j => raw921 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw921step0 raw921; decide +kernel
      have hl : raw921step0Labels = raw921Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw921 raw921Labels permutation8 permutation4
    mixedMoment B raw921step0 raw921step0Labels = mixedMoment B raw921step1 raw921step1Labels := by
      have ha : raw921step1 = raw921step0 := by apply Matrix.ext; unfold raw921step1 raw921step0; decide +kernel
      have hl : raw921step0Labels = labelEmbedding7 ∘ raw921step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw921step0 raw921step0Labels raw921step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

def raw922 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw922step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw922 raw922Labels = mixedMoment B node729 node729Labels := by
  calc
    mixedMoment B raw922 raw922Labels = mixedMoment B raw922step0 raw922step0Labels := by
      have ha : raw922step0 = (fun i j => raw922 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw922step0 raw922; decide +kernel
      have hl : raw922step0Labels = raw922Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw922 raw922Labels permutation8 permutation4
    _ = mixedMoment B node729 node729Labels := by rfl

def raw923 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, -1, 0], ![1, 2, -3], ![-2, 3, -1]]
def raw923Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw923step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, -2, 3], ![-3, 1, 2]]
def raw923step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw923step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw923step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw923step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw923step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw923 raw923Labels = mixedMoment B node773 node773Labels := by
  calc
    mixedMoment B raw923 raw923Labels = mixedMoment B raw923step0 raw923step0Labels := by
      have ha : raw923step0 = (fun i j => raw923 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw923step0 raw923; decide +kernel
      have hl : raw923step0Labels = raw923Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw923 raw923Labels permutation9 permutation6
    mixedMoment B raw923step0 raw923step0Labels = mixedMoment B raw923step1 raw923step1Labels := by
      have ha : raw923step1 = -raw923step0 := by apply Matrix.ext; change ∀ i j, raw923step1 i j = -(raw923step0 i j); unfold raw923step1 raw923step0; decide +kernel
      have hl : raw923step1Labels = raw923step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw923step1 raw923step1Labels = mixedMoment B raw923step2 raw923step2Labels := by
      have ha : raw923step2 = raw923step1 := by apply Matrix.ext; unfold raw923step2 raw923step1; decide +kernel
      have hl : raw923step1Labels = labelEmbedding1 ∘ raw923step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw923step1 raw923step1Labels raw923step2Labels labelEmbedding1 hl
    _ = mixedMoment B node773 node773Labels := by rfl

def raw924 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw924step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw924step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw924 raw924Labels = mixedMoment B node4230 node4230Labels := by
  calc
    mixedMoment B raw924 raw924Labels = mixedMoment B raw924step0 raw924step0Labels := by
      have ha : raw924step0 = (fun i j => raw924 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw924step0 raw924; decide +kernel
      have hl : raw924step0Labels = raw924Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw924 raw924Labels permutation152 permutation4
    mixedMoment B raw924step0 raw924step0Labels = mixedMoment B raw924step1 raw924step1Labels := by
      have ha : raw924step1 = raw924step0 := by apply Matrix.ext; unfold raw924step1 raw924step0; decide +kernel
      have hl : raw924step0Labels = labelEmbedding7 ∘ raw924step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw924step0 raw924step0Labels raw924step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4230 node4230Labels := by rfl

def raw925 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw925 raw925Labels = mixedMoment B node730 node730Labels := by
  calc
    mixedMoment B raw925 raw925Labels = mixedMoment B raw925step0 raw925step0Labels := by
      have ha : raw925step0 = (fun i j => raw925 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw925step0 raw925; decide +kernel
      have hl : raw925step0Labels = raw925Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw925 raw925Labels permutation152 permutation4
    _ = mixedMoment B node730 node730Labels := by rfl

def raw926 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw926Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw926step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw926step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw926step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw926step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw926 raw926Labels = mixedMoment B node780 node780Labels := by
  calc
    mixedMoment B raw926 raw926Labels = mixedMoment B raw926step0 raw926step0Labels := by
      have ha : raw926step0 = (fun i j => raw926 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw926step0 raw926; decide +kernel
      have hl : raw926step0Labels = raw926Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw926 raw926Labels permutation182 permutation6
    mixedMoment B raw926step0 raw926step0Labels = mixedMoment B raw926step1 raw926step1Labels := by
      have ha : raw926step1 = -raw926step0 := by apply Matrix.ext; change ∀ i j, raw926step1 i j = -(raw926step0 i j); unfold raw926step1 raw926step0; decide +kernel
      have hl : raw926step1Labels = raw926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw926step1 raw926step1Labels = mixedMoment B raw926step2 raw926step2Labels := by
      have ha : raw926step2 = raw926step1 := by apply Matrix.ext; unfold raw926step2 raw926step1; decide +kernel
      have hl : raw926step1Labels = labelEmbedding1 ∘ raw926step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw926step1 raw926step1Labels raw926step2Labels labelEmbedding1 hl
    _ = mixedMoment B node780 node780Labels := by rfl

def raw927 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw927step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw927 raw927Labels = mixedMoment B node4231 node4231Labels := by
  calc
    mixedMoment B raw927 raw927Labels = mixedMoment B raw927step0 raw927step0Labels := by
      have ha : raw927step0 = (fun i j => raw927 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw927step0 raw927; decide +kernel
      have hl : raw927step0Labels = raw927Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw927 raw927Labels permutation32 permutation4
    mixedMoment B raw927step0 raw927step0Labels = mixedMoment B raw927step1 raw927step1Labels := by
      have ha : raw927step1 = raw927step0 := by apply Matrix.ext; unfold raw927step1 raw927step0; decide +kernel
      have hl : raw927step0Labels = labelEmbedding7 ∘ raw927step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw927step0 raw927step0Labels raw927step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4231 node4231Labels := by rfl

def raw928 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw928 raw928Labels = mixedMoment B node731 node731Labels := by
  calc
    mixedMoment B raw928 raw928Labels = mixedMoment B raw928step0 raw928step0Labels := by
      have ha : raw928step0 = (fun i j => raw928 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw928step0 raw928; decide +kernel
      have hl : raw928step0Labels = raw928Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw928 raw928Labels permutation32 permutation4
    _ = mixedMoment B node731 node731Labels := by rfl

def raw929 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw929Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw929step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw929step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw929step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw929step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw929 raw929Labels = mixedMoment B node781 node781Labels := by
  calc
    mixedMoment B raw929 raw929Labels = mixedMoment B raw929step0 raw929step0Labels := by
      have ha : raw929step0 = (fun i j => raw929 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw929step0 raw929; decide +kernel
      have hl : raw929step0Labels = raw929Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw929 raw929Labels permutation40 permutation6
    mixedMoment B raw929step0 raw929step0Labels = mixedMoment B raw929step1 raw929step1Labels := by
      have ha : raw929step1 = -raw929step0 := by apply Matrix.ext; change ∀ i j, raw929step1 i j = -(raw929step0 i j); unfold raw929step1 raw929step0; decide +kernel
      have hl : raw929step1Labels = raw929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw929step1 raw929step1Labels = mixedMoment B raw929step2 raw929step2Labels := by
      have ha : raw929step2 = raw929step1 := by apply Matrix.ext; unfold raw929step2 raw929step1; decide +kernel
      have hl : raw929step1Labels = labelEmbedding1 ∘ raw929step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw929step1 raw929step1Labels raw929step2Labels labelEmbedding1 hl
    _ = mixedMoment B node781 node781Labels := by rfl

def raw930 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw930step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw930 raw930Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw930 raw930Labels = mixedMoment B raw930step0 raw930step0Labels := by
      have ha : raw930step0 = (fun i j => raw930 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw930step0 raw930; decide +kernel
      have hl : raw930step0Labels = raw930Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw930 raw930Labels permutation152 permutation4
    mixedMoment B raw930step0 raw930step0Labels = mixedMoment B raw930step1 raw930step1Labels := by
      have ha : raw930step1 = raw930step0 := by apply Matrix.ext; unfold raw930step1 raw930step0; decide +kernel
      have hl : raw930step0Labels = labelEmbedding7 ∘ raw930step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw930step0 raw930step0Labels raw930step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4232 node4232Labels := by rfl

def raw931 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw931Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw931step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw931step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw931 raw931Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw931 raw931Labels = mixedMoment B raw931step0 raw931step0Labels := by
      have ha : raw931step0 = (fun i j => raw931 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw931step0 raw931; decide +kernel
      have hl : raw931step0Labels = raw931Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw931 raw931Labels permutation152 permutation4
    _ = mixedMoment B node732 node732Labels := by rfl

def raw932 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw932Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw932step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw932step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw932step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw932step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw932 raw932Labels = mixedMoment B node798 node798Labels := by
  calc
    mixedMoment B raw932 raw932Labels = mixedMoment B raw932step0 raw932step0Labels := by
      have ha : raw932step0 = (fun i j => raw932 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw932step0 raw932; decide +kernel
      have hl : raw932step0Labels = raw932Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw932 raw932Labels permutation176 permutation6
    mixedMoment B raw932step0 raw932step0Labels = mixedMoment B raw932step1 raw932step1Labels := by
      have ha : raw932step1 = -raw932step0 := by apply Matrix.ext; change ∀ i j, raw932step1 i j = -(raw932step0 i j); unfold raw932step1 raw932step0; decide +kernel
      have hl : raw932step1Labels = raw932step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw932step1 raw932step1Labels = mixedMoment B raw932step2 raw932step2Labels := by
      have ha : raw932step2 = raw932step1 := by apply Matrix.ext; unfold raw932step2 raw932step1; decide +kernel
      have hl : raw932step1Labels = labelEmbedding1 ∘ raw932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw932step1 raw932step1Labels raw932step2Labels labelEmbedding1 hl
    _ = mixedMoment B node798 node798Labels := by rfl

def raw933 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw933step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw933 raw933Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw933 raw933Labels = mixedMoment B raw933step0 raw933step0Labels := by
      have ha : raw933step0 = (fun i j => raw933 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw933step0 raw933; decide +kernel
      have hl : raw933step0Labels = raw933Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw933 raw933Labels permutation32 permutation4
    mixedMoment B raw933step0 raw933step0Labels = mixedMoment B raw933step1 raw933step1Labels := by
      have ha : raw933step1 = raw933step0 := by apply Matrix.ext; unfold raw933step1 raw933step0; decide +kernel
      have hl : raw933step0Labels = labelEmbedding7 ∘ raw933step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw933step0 raw933step0Labels raw933step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4233 node4233Labels := by rfl

def raw934 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw934Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw934 raw934Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw934 raw934Labels = mixedMoment B raw934step0 raw934step0Labels := by
      have ha : raw934step0 = (fun i j => raw934 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw934step0 raw934; decide +kernel
      have hl : raw934step0Labels = raw934Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw934 raw934Labels permutation32 permutation4
    _ = mixedMoment B node733 node733Labels := by rfl

def raw935 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw935Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw935step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw935step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw935step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw935 raw935Labels = mixedMoment B node799 node799Labels := by
  calc
    mixedMoment B raw935 raw935Labels = mixedMoment B raw935step0 raw935step0Labels := by
      have ha : raw935step0 = (fun i j => raw935 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw935step0 raw935; decide +kernel
      have hl : raw935step0Labels = raw935Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw935 raw935Labels permutation38 permutation6
    mixedMoment B raw935step0 raw935step0Labels = mixedMoment B raw935step1 raw935step1Labels := by
      have ha : raw935step1 = -raw935step0 := by apply Matrix.ext; change ∀ i j, raw935step1 i j = -(raw935step0 i j); unfold raw935step1 raw935step0; decide +kernel
      have hl : raw935step1Labels = raw935step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw935step1 raw935step1Labels = mixedMoment B raw935step2 raw935step2Labels := by
      have ha : raw935step2 = raw935step1 := by apply Matrix.ext; unfold raw935step2 raw935step1; decide +kernel
      have hl : raw935step1Labels = labelEmbedding1 ∘ raw935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw935step1 raw935step1Labels raw935step2Labels labelEmbedding1 hl
    _ = mixedMoment B node799 node799Labels := by rfl

def raw936 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw936step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw936 raw936Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw936 raw936Labels = mixedMoment B raw936step0 raw936step0Labels := by
      have ha : raw936step0 = (fun i j => raw936 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw936step0 raw936; decide +kernel
      have hl : raw936step0Labels = raw936Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw936 raw936Labels permutation32 permutation4
    mixedMoment B raw936step0 raw936step0Labels = mixedMoment B raw936step1 raw936step1Labels := by
      have ha : raw936step1 = raw936step0 := by apply Matrix.ext; unfold raw936step1 raw936step0; decide +kernel
      have hl : raw936step0Labels = labelEmbedding7 ∘ raw936step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw936step0 raw936step0Labels raw936step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4234 node4234Labels := by rfl

def raw937 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw937Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw937 raw937Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw937 raw937Labels = mixedMoment B raw937step0 raw937step0Labels := by
      have ha : raw937step0 = (fun i j => raw937 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw937step0 raw937; decide +kernel
      have hl : raw937step0Labels = raw937Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw937 raw937Labels permutation32 permutation4
    _ = mixedMoment B node734 node734Labels := by rfl

def raw938 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw938Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw938step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw938step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw938step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw938 raw938Labels = mixedMoment B node800 node800Labels := by
  calc
    mixedMoment B raw938 raw938Labels = mixedMoment B raw938step0 raw938step0Labels := by
      have ha : raw938step0 = (fun i j => raw938 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw938step0 raw938; decide +kernel
      have hl : raw938step0Labels = raw938Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw938 raw938Labels permutation38 permutation6
    mixedMoment B raw938step0 raw938step0Labels = mixedMoment B raw938step1 raw938step1Labels := by
      have ha : raw938step1 = -raw938step0 := by apply Matrix.ext; change ∀ i j, raw938step1 i j = -(raw938step0 i j); unfold raw938step1 raw938step0; decide +kernel
      have hl : raw938step1Labels = raw938step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw938step1 raw938step1Labels = mixedMoment B raw938step2 raw938step2Labels := by
      have ha : raw938step2 = raw938step1 := by apply Matrix.ext; unfold raw938step2 raw938step1; decide +kernel
      have hl : raw938step1Labels = labelEmbedding1 ∘ raw938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw938step1 raw938step1Labels raw938step2Labels labelEmbedding1 hl
    _ = mixedMoment B node800 node800Labels := by rfl

def raw939 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw939step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw939step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw939 raw939Labels = mixedMoment B node4235 node4235Labels := by
  calc
    mixedMoment B raw939 raw939Labels = mixedMoment B raw939step0 raw939step0Labels := by
      have ha : raw939step0 = (fun i j => raw939 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw939step0 raw939; decide +kernel
      have hl : raw939step0Labels = raw939Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw939 raw939Labels permutation8 permutation4
    mixedMoment B raw939step0 raw939step0Labels = mixedMoment B raw939step1 raw939step1Labels := by
      have ha : raw939step1 = raw939step0 := by apply Matrix.ext; unfold raw939step1 raw939step0; decide +kernel
      have hl : raw939step0Labels = labelEmbedding7 ∘ raw939step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw939step0 raw939step0Labels raw939step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4235 node4235Labels := by rfl

def raw940 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw940Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw940step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw940step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw940 raw940Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw940 raw940Labels = mixedMoment B raw940step0 raw940step0Labels := by
      have ha : raw940step0 = (fun i j => raw940 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw940step0 raw940; decide +kernel
      have hl : raw940step0Labels = raw940Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw940 raw940Labels permutation8 permutation4
    _ = mixedMoment B node735 node735Labels := by rfl

def raw941 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 1, 0], ![-1, 4, -3]]
def raw941Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw941step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-3, -1, 4]]
def raw941step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw941step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw941step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw941step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw941 raw941Labels = mixedMoment B node801 node801Labels := by
  calc
    mixedMoment B raw941 raw941Labels = mixedMoment B raw941step0 raw941step0Labels := by
      have ha : raw941step0 = (fun i j => raw941 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw941step0 raw941; decide +kernel
      have hl : raw941step0Labels = raw941Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw941 raw941Labels permutation10 permutation6
    mixedMoment B raw941step0 raw941step0Labels = mixedMoment B raw941step1 raw941step1Labels := by
      have ha : raw941step1 = -raw941step0 := by apply Matrix.ext; change ∀ i j, raw941step1 i j = -(raw941step0 i j); unfold raw941step1 raw941step0; decide +kernel
      have hl : raw941step1Labels = raw941step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw941step1 raw941step1Labels = mixedMoment B raw941step2 raw941step2Labels := by
      have ha : raw941step2 = raw941step1 := by apply Matrix.ext; unfold raw941step2 raw941step1; decide +kernel
      have hl : raw941step1Labels = labelEmbedding1 ∘ raw941step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw941step1 raw941step1Labels raw941step2Labels labelEmbedding1 hl
    _ = mixedMoment B node801 node801Labels := by rfl

def raw942 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw942step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw942 raw942Labels = mixedMoment B node4236 node4236Labels := by
  calc
    mixedMoment B raw942 raw942Labels = mixedMoment B raw942step0 raw942step0Labels := by
      have ha : raw942step0 = (fun i j => raw942 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw942step0 raw942; decide +kernel
      have hl : raw942step0Labels = raw942Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw942 raw942Labels permutation152 permutation4
    mixedMoment B raw942step0 raw942step0Labels = mixedMoment B raw942step1 raw942step1Labels := by
      have ha : raw942step1 = raw942step0 := by apply Matrix.ext; unfold raw942step1 raw942step0; decide +kernel
      have hl : raw942step0Labels = labelEmbedding7 ∘ raw942step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw942step0 raw942step0Labels raw942step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4236 node4236Labels := by rfl

def raw943 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw943Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw943 raw943Labels = mixedMoment B node736 node736Labels := by
  calc
    mixedMoment B raw943 raw943Labels = mixedMoment B raw943step0 raw943step0Labels := by
      have ha : raw943step0 = (fun i j => raw943 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw943step0 raw943; decide +kernel
      have hl : raw943step0Labels = raw943Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw943 raw943Labels permutation152 permutation4
    _ = mixedMoment B node736 node736Labels := by rfl

def raw944 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw944Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw944step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw944 raw944Labels = mixedMoment B node818 node818Labels := by
  calc
    mixedMoment B raw944 raw944Labels = mixedMoment B raw944step0 raw944step0Labels := by
      have ha : raw944step0 = (fun i j => raw944 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw944step0 raw944; decide +kernel
      have hl : raw944step0Labels = raw944Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw944 raw944Labels permutation246 permutation6
    mixedMoment B raw944step0 raw944step0Labels = mixedMoment B raw944step1 raw944step1Labels := by
      have ha : raw944step1 = -raw944step0 := by apply Matrix.ext; change ∀ i j, raw944step1 i j = -(raw944step0 i j); unfold raw944step1 raw944step0; decide +kernel
      have hl : raw944step1Labels = raw944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw944step1 raw944step1Labels = mixedMoment B raw944step2 raw944step2Labels := by
      have ha : raw944step2 = raw944step1 := by apply Matrix.ext; unfold raw944step2 raw944step1; decide +kernel
      have hl : raw944step1Labels = labelEmbedding1 ∘ raw944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw944step1 raw944step1Labels raw944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node818 node818Labels := by rfl

def raw945 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw945step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw945 raw945Labels = mixedMoment B node4237 node4237Labels := by
  calc
    mixedMoment B raw945 raw945Labels = mixedMoment B raw945step0 raw945step0Labels := by
      have ha : raw945step0 = (fun i j => raw945 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw945step0 raw945; decide +kernel
      have hl : raw945step0Labels = raw945Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw945 raw945Labels permutation32 permutation4
    mixedMoment B raw945step0 raw945step0Labels = mixedMoment B raw945step1 raw945step1Labels := by
      have ha : raw945step1 = raw945step0 := by apply Matrix.ext; unfold raw945step1 raw945step0; decide +kernel
      have hl : raw945step0Labels = labelEmbedding7 ∘ raw945step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw945step0 raw945step0Labels raw945step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4237 node4237Labels := by rfl

def raw946 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw946Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw946 raw946Labels = mixedMoment B node737 node737Labels := by
  calc
    mixedMoment B raw946 raw946Labels = mixedMoment B raw946step0 raw946step0Labels := by
      have ha : raw946step0 = (fun i j => raw946 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw946step0 raw946; decide +kernel
      have hl : raw946step0Labels = raw946Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw946 raw946Labels permutation32 permutation4
    _ = mixedMoment B node737 node737Labels := by rfl

def raw947 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw947Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw947step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw947 raw947Labels = mixedMoment B node840 node840Labels := by
  calc
    mixedMoment B raw947 raw947Labels = mixedMoment B raw947step0 raw947step0Labels := by
      have ha : raw947step0 = (fun i j => raw947 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw947step0 raw947; decide +kernel
      have hl : raw947step0Labels = raw947Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw947 raw947Labels permutation32 permutation6
    mixedMoment B raw947step0 raw947step0Labels = mixedMoment B raw947step1 raw947step1Labels := by
      have ha : raw947step1 = -raw947step0 := by apply Matrix.ext; change ∀ i j, raw947step1 i j = -(raw947step0 i j); unfold raw947step1 raw947step0; decide +kernel
      have hl : raw947step1Labels = raw947step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw947step1 raw947step1Labels = mixedMoment B raw947step2 raw947step2Labels := by
      have ha : raw947step2 = raw947step1 := by apply Matrix.ext; unfold raw947step2 raw947step1; decide +kernel
      have hl : raw947step1Labels = labelEmbedding1 ∘ raw947step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw947step1 raw947step1Labels raw947step2Labels labelEmbedding1 hl
    _ = mixedMoment B node840 node840Labels := by rfl

def raw948 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw948step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw948 raw948Labels = mixedMoment B node4238 node4238Labels := by
  calc
    mixedMoment B raw948 raw948Labels = mixedMoment B raw948step0 raw948step0Labels := by
      have ha : raw948step0 = (fun i j => raw948 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw948step0 raw948; decide +kernel
      have hl : raw948step0Labels = raw948Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw948 raw948Labels permutation32 permutation4
    mixedMoment B raw948step0 raw948step0Labels = mixedMoment B raw948step1 raw948step1Labels := by
      have ha : raw948step1 = raw948step0 := by apply Matrix.ext; unfold raw948step1 raw948step0; decide +kernel
      have hl : raw948step0Labels = labelEmbedding7 ∘ raw948step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw948step0 raw948step0Labels raw948step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4238 node4238Labels := by rfl

def raw949 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw949Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw949 raw949Labels = mixedMoment B node738 node738Labels := by
  calc
    mixedMoment B raw949 raw949Labels = mixedMoment B raw949step0 raw949step0Labels := by
      have ha : raw949step0 = (fun i j => raw949 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw949step0 raw949; decide +kernel
      have hl : raw949step0Labels = raw949Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw949 raw949Labels permutation32 permutation4
    _ = mixedMoment B node738 node738Labels := by rfl

def raw950 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw950Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw950 raw950Labels = mixedMoment B node819 node819Labels := by
  calc
    mixedMoment B raw950 raw950Labels = mixedMoment B raw950step0 raw950step0Labels := by
      have ha : raw950step0 = (fun i j => raw950 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw950step0 raw950; decide +kernel
      have hl : raw950step0Labels = raw950Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw950 raw950Labels permutation44 permutation6
    mixedMoment B raw950step0 raw950step0Labels = mixedMoment B raw950step1 raw950step1Labels := by
      have ha : raw950step1 = -raw950step0 := by apply Matrix.ext; change ∀ i j, raw950step1 i j = -(raw950step0 i j); unfold raw950step1 raw950step0; decide +kernel
      have hl : raw950step1Labels = raw950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw950step1 raw950step1Labels = mixedMoment B raw950step2 raw950step2Labels := by
      have ha : raw950step2 = raw950step1 := by apply Matrix.ext; unfold raw950step2 raw950step1; decide +kernel
      have hl : raw950step1Labels = labelEmbedding1 ∘ raw950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw950step1 raw950step1Labels raw950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node819 node819Labels := by rfl

def raw951 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw951step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw951step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw951 raw951Labels = mixedMoment B node4239 node4239Labels := by
  calc
    mixedMoment B raw951 raw951Labels = mixedMoment B raw951step0 raw951step0Labels := by
      have ha : raw951step0 = (fun i j => raw951 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw951step0 raw951; decide +kernel
      have hl : raw951step0Labels = raw951Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw951 raw951Labels permutation32 permutation4
    mixedMoment B raw951step0 raw951step0Labels = mixedMoment B raw951step1 raw951step1Labels := by
      have ha : raw951step1 = raw951step0 := by apply Matrix.ext; unfold raw951step1 raw951step0; decide +kernel
      have hl : raw951step0Labels = labelEmbedding7 ∘ raw951step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw951step0 raw951step0Labels raw951step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4239 node4239Labels := by rfl

def raw952 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw952Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw952 raw952Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw952 raw952Labels = mixedMoment B raw952step0 raw952step0Labels := by
      have ha : raw952step0 = (fun i j => raw952 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw952step0 raw952; decide +kernel
      have hl : raw952step0Labels = raw952Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw952 raw952Labels permutation32 permutation4
    _ = mixedMoment B node739 node739Labels := by rfl

def raw953 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw953Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw953 raw953Labels = mixedMoment B node841 node841Labels := by
  calc
    mixedMoment B raw953 raw953Labels = mixedMoment B raw953step0 raw953step0Labels := by
      have ha : raw953step0 = (fun i j => raw953 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw953step0 raw953; decide +kernel
      have hl : raw953step0Labels = raw953Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw953 raw953Labels permutation32 permutation6
    mixedMoment B raw953step0 raw953step0Labels = mixedMoment B raw953step1 raw953step1Labels := by
      have ha : raw953step1 = -raw953step0 := by apply Matrix.ext; change ∀ i j, raw953step1 i j = -(raw953step0 i j); unfold raw953step1 raw953step0; decide +kernel
      have hl : raw953step1Labels = raw953step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw953step1 raw953step1Labels = mixedMoment B raw953step2 raw953step2Labels := by
      have ha : raw953step2 = raw953step1 := by apply Matrix.ext; unfold raw953step2 raw953step1; decide +kernel
      have hl : raw953step1Labels = labelEmbedding1 ∘ raw953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw953step1 raw953step1Labels raw953step2Labels labelEmbedding1 hl
    _ = mixedMoment B node841 node841Labels := by rfl

def raw954 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw954step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw954step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw954step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw954step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw954 raw954Labels = mixedMoment B node4240 node4240Labels := by
  calc
    mixedMoment B raw954 raw954Labels = mixedMoment B raw954step0 raw954step0Labels := by
      have ha : raw954step0 = (fun i j => raw954 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw954step0 raw954; decide +kernel
      have hl : raw954step0Labels = raw954Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw954 raw954Labels permutation8 permutation4
    mixedMoment B raw954step0 raw954step0Labels = mixedMoment B raw954step1 raw954step1Labels := by
      have ha : raw954step1 = raw954step0 := by apply Matrix.ext; unfold raw954step1 raw954step0; decide +kernel
      have hl : raw954step0Labels = labelEmbedding7 ∘ raw954step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw954step0 raw954step0Labels raw954step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4240 node4240Labels := by rfl

def raw955 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw955Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw955step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw955 raw955Labels = mixedMoment B node740 node740Labels := by
  calc
    mixedMoment B raw955 raw955Labels = mixedMoment B raw955step0 raw955step0Labels := by
      have ha : raw955step0 = (fun i j => raw955 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw955step0 raw955; decide +kernel
      have hl : raw955step0Labels = raw955Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw955 raw955Labels permutation8 permutation4
    _ = mixedMoment B node740 node740Labels := by rfl

def raw956 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 1, -1], ![-2, 4, -2]]
def raw956Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw956step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw956step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw956 raw956Labels = mixedMoment B node842 node842Labels := by
  calc
    mixedMoment B raw956 raw956Labels = mixedMoment B raw956step0 raw956step0Labels := by
      have ha : raw956step0 = (fun i j => raw956 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw956step0 raw956; decide +kernel
      have hl : raw956step0Labels = raw956Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw956 raw956Labels permutation8 permutation6
    mixedMoment B raw956step0 raw956step0Labels = mixedMoment B raw956step1 raw956step1Labels := by
      have ha : raw956step1 = -raw956step0 := by apply Matrix.ext; change ∀ i j, raw956step1 i j = -(raw956step0 i j); unfold raw956step1 raw956step0; decide +kernel
      have hl : raw956step1Labels = raw956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw956step1 raw956step1Labels = mixedMoment B raw956step2 raw956step2Labels := by
      have ha : raw956step2 = raw956step1 := by apply Matrix.ext; unfold raw956step2 raw956step1; decide +kernel
      have hl : raw956step1Labels = labelEmbedding1 ∘ raw956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw956step1 raw956step1Labels raw956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node842 node842Labels := by rfl

def raw957 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw957step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw957step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw957step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw957 raw957Labels = mixedMoment B node4241 node4241Labels := by
  calc
    mixedMoment B raw957 raw957Labels = mixedMoment B raw957step0 raw957step0Labels := by
      have ha : raw957step0 = (fun i j => raw957 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw957step0 raw957; decide +kernel
      have hl : raw957step0Labels = raw957Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw957 raw957Labels permutation8 permutation4
    mixedMoment B raw957step0 raw957step0Labels = mixedMoment B raw957step1 raw957step1Labels := by
      have ha : raw957step1 = raw957step0 := by apply Matrix.ext; unfold raw957step1 raw957step0; decide +kernel
      have hl : raw957step0Labels = labelEmbedding7 ∘ raw957step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw957step0 raw957step0Labels raw957step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4241 node4241Labels := by rfl

def raw958 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw958Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw958step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw958 raw958Labels = mixedMoment B node741 node741Labels := by
  calc
    mixedMoment B raw958 raw958Labels = mixedMoment B raw958step0 raw958step0Labels := by
      have ha : raw958step0 = (fun i j => raw958 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw958step0 raw958; decide +kernel
      have hl : raw958step0Labels = raw958Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw958 raw958Labels permutation8 permutation4
    _ = mixedMoment B node741 node741Labels := by rfl

def raw959 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw959Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw959step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 2, -1], ![-3, 0, 3]]
def raw959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw959 raw959Labels = mixedMoment B node820 node820Labels := by
  calc
    mixedMoment B raw959 raw959Labels = mixedMoment B raw959step0 raw959step0Labels := by
      have ha : raw959step0 = (fun i j => raw959 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw959step0 raw959; decide +kernel
      have hl : raw959step0Labels = raw959Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw959 raw959Labels permutation10 permutation6
    mixedMoment B raw959step0 raw959step0Labels = mixedMoment B raw959step1 raw959step1Labels := by
      have ha : raw959step1 = -raw959step0 := by apply Matrix.ext; change ∀ i j, raw959step1 i j = -(raw959step0 i j); unfold raw959step1 raw959step0; decide +kernel
      have hl : raw959step1Labels = raw959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw959step1 raw959step1Labels = mixedMoment B raw959step2 raw959step2Labels := by
      have ha : raw959step2 = raw959step1 := by apply Matrix.ext; unfold raw959step2 raw959step1; decide +kernel
      have hl : raw959step1Labels = labelEmbedding1 ∘ raw959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw959step1 raw959step1Labels raw959step2Labels labelEmbedding1 hl
    _ = mixedMoment B node820 node820Labels := by rfl

def raw960 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw960step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw960step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw960 raw960Labels = mixedMoment B node4242 node4242Labels := by
  calc
    mixedMoment B raw960 raw960Labels = mixedMoment B raw960step0 raw960step0Labels := by
      have ha : raw960step0 = (fun i j => raw960 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw960step0 raw960; decide +kernel
      have hl : raw960step0Labels = raw960Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw960 raw960Labels permutation8 permutation4
    mixedMoment B raw960step0 raw960step0Labels = mixedMoment B raw960step1 raw960step1Labels := by
      have ha : raw960step1 = raw960step0 := by apply Matrix.ext; unfold raw960step1 raw960step0; decide +kernel
      have hl : raw960step0Labels = labelEmbedding7 ∘ raw960step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw960step0 raw960step0Labels raw960step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4242 node4242Labels := by rfl

def raw961 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw961step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw961 raw961Labels = mixedMoment B node742 node742Labels := by
  calc
    mixedMoment B raw961 raw961Labels = mixedMoment B raw961step0 raw961step0Labels := by
      have ha : raw961step0 = (fun i j => raw961 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw961step0 raw961; decide +kernel
      have hl : raw961step0Labels = raw961Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw961 raw961Labels permutation8 permutation4
    _ = mixedMoment B node742 node742Labels := by rfl

def raw962 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw962Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw962step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw962step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw962step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw962step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw962 raw962Labels = mixedMoment B node843 node843Labels := by
  calc
    mixedMoment B raw962 raw962Labels = mixedMoment B raw962step0 raw962step0Labels := by
      have ha : raw962step0 = (fun i j => raw962 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw962step0 raw962; decide +kernel
      have hl : raw962step0Labels = raw962Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw962 raw962Labels permutation8 permutation6
    mixedMoment B raw962step0 raw962step0Labels = mixedMoment B raw962step1 raw962step1Labels := by
      have ha : raw962step1 = -raw962step0 := by apply Matrix.ext; change ∀ i j, raw962step1 i j = -(raw962step0 i j); unfold raw962step1 raw962step0; decide +kernel
      have hl : raw962step1Labels = raw962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw962step1 raw962step1Labels = mixedMoment B raw962step2 raw962step2Labels := by
      have ha : raw962step2 = raw962step1 := by apply Matrix.ext; unfold raw962step2 raw962step1; decide +kernel
      have hl : raw962step1Labels = labelEmbedding1 ∘ raw962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw962step1 raw962step1Labels raw962step2Labels labelEmbedding1 hl
    _ = mixedMoment B node843 node843Labels := by rfl

def raw963 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw963step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw963step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw963step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw963 raw963Labels = mixedMoment B node4243 node4243Labels := by
  calc
    mixedMoment B raw963 raw963Labels = mixedMoment B raw963step0 raw963step0Labels := by
      have ha : raw963step0 = (fun i j => raw963 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw963step0 raw963; decide +kernel
      have hl : raw963step0Labels = raw963Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw963 raw963Labels permutation8 permutation4
    mixedMoment B raw963step0 raw963step0Labels = mixedMoment B raw963step1 raw963step1Labels := by
      have ha : raw963step1 = raw963step0 := by apply Matrix.ext; unfold raw963step1 raw963step0; decide +kernel
      have hl : raw963step0Labels = labelEmbedding7 ∘ raw963step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw963step0 raw963step0Labels raw963step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4243 node4243Labels := by rfl

def raw964 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw964step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw964 raw964Labels = mixedMoment B node743 node743Labels := by
  calc
    mixedMoment B raw964 raw964Labels = mixedMoment B raw964step0 raw964step0Labels := by
      have ha : raw964step0 = (fun i j => raw964 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw964step0 raw964; decide +kernel
      have hl : raw964step0Labels = raw964Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw964 raw964Labels permutation8 permutation4
    _ = mixedMoment B node743 node743Labels := by rfl

def raw965 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, -1, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw965Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw965step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw965step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw965step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw965step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw965 raw965Labels = mixedMoment B node844 node844Labels := by
  calc
    mixedMoment B raw965 raw965Labels = mixedMoment B raw965step0 raw965step0Labels := by
      have ha : raw965step0 = (fun i j => raw965 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw965step0 raw965; decide +kernel
      have hl : raw965step0Labels = raw965Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw965 raw965Labels permutation9 permutation6
    mixedMoment B raw965step0 raw965step0Labels = mixedMoment B raw965step1 raw965step1Labels := by
      have ha : raw965step1 = -raw965step0 := by apply Matrix.ext; change ∀ i j, raw965step1 i j = -(raw965step0 i j); unfold raw965step1 raw965step0; decide +kernel
      have hl : raw965step1Labels = raw965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw965step1 raw965step1Labels = mixedMoment B raw965step2 raw965step2Labels := by
      have ha : raw965step2 = raw965step1 := by apply Matrix.ext; unfold raw965step2 raw965step1; decide +kernel
      have hl : raw965step1Labels = labelEmbedding1 ∘ raw965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw965step1 raw965step1Labels raw965step2Labels labelEmbedding1 hl
    _ = mixedMoment B node844 node844Labels := by rfl

def raw966 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw966step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw966step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw966step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw966 raw966Labels = mixedMoment B node4248 node4248Labels := by
  calc
    mixedMoment B raw966 raw966Labels = mixedMoment B raw966step0 raw966step0Labels := by
      have ha : raw966step0 = (fun i j => raw966 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw966step0 raw966; decide +kernel
      have hl : raw966step0Labels = raw966Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw966 raw966Labels permutation152 permutation4
    mixedMoment B raw966step0 raw966step0Labels = mixedMoment B raw966step1 raw966step1Labels := by
      have ha : raw966step1 = raw966step0 := by apply Matrix.ext; unfold raw966step1 raw966step0; decide +kernel
      have hl : raw966step0Labels = labelEmbedding7 ∘ raw966step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw966step0 raw966step0Labels raw966step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4248 node4248Labels := by rfl

def raw967 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw967 raw967Labels = mixedMoment B node782 node782Labels := by
  calc
    mixedMoment B raw967 raw967Labels = mixedMoment B raw967step0 raw967step0Labels := by
      have ha : raw967step0 = (fun i j => raw967 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw967step0 raw967; decide +kernel
      have hl : raw967step0Labels = raw967Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw967 raw967Labels permutation152 permutation4
    _ = mixedMoment B node782 node782Labels := by rfl

def raw968 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw968Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw968step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw968step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw968 raw968Labels = mixedMoment B node782 node782Labels := by
  calc
    mixedMoment B raw968 raw968Labels = mixedMoment B raw968step0 raw968step0Labels := by
      have ha : raw968step0 = (fun i j => raw968 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw968step0 raw968; decide +kernel
      have hl : raw968step0Labels = raw968Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw968 raw968Labels permutation212 permutation6
    mixedMoment B raw968step0 raw968step0Labels = mixedMoment B raw968step1 raw968step1Labels := by
      have ha : raw968step1 = -raw968step0 := by apply Matrix.ext; change ∀ i j, raw968step1 i j = -(raw968step0 i j); unfold raw968step1 raw968step0; decide +kernel
      have hl : raw968step1Labels = raw968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw968step1 raw968step1Labels = mixedMoment B raw968step2 raw968step2Labels := by
      have ha : raw968step2 = raw968step1 := by apply Matrix.ext; unfold raw968step2 raw968step1; decide +kernel
      have hl : raw968step1Labels = labelEmbedding1 ∘ raw968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw968step1 raw968step1Labels raw968step2Labels labelEmbedding1 hl
    _ = mixedMoment B node782 node782Labels := by rfl

def raw969 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw969step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw969step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw969 raw969Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw969 raw969Labels = mixedMoment B raw969step0 raw969step0Labels := by
      have ha : raw969step0 = (fun i j => raw969 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw969step0 raw969; decide +kernel
      have hl : raw969step0Labels = raw969Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw969 raw969Labels permutation152 permutation4
    mixedMoment B raw969step0 raw969step0Labels = mixedMoment B raw969step1 raw969step1Labels := by
      have ha : raw969step1 = raw969step0 := by apply Matrix.ext; unfold raw969step1 raw969step0; decide +kernel
      have hl : raw969step0Labels = labelEmbedding7 ∘ raw969step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw969step0 raw969step0Labels raw969step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw970 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw970 raw970Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw970 raw970Labels = mixedMoment B raw970step0 raw970step0Labels := by
      have ha : raw970step0 = (fun i j => raw970 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw970step0 raw970; decide +kernel
      have hl : raw970step0Labels = raw970Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw970 raw970Labels permutation152 permutation4
    _ = mixedMoment B node783 node783Labels := by rfl

def raw971 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw971Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw971step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw971step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw971step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw971 raw971Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw971 raw971Labels = mixedMoment B raw971step0 raw971step0Labels := by
      have ha : raw971step0 = (fun i j => raw971 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw971step0 raw971; decide +kernel
      have hl : raw971step0Labels = raw971Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw971 raw971Labels permutation200 permutation6
    mixedMoment B raw971step0 raw971step0Labels = mixedMoment B raw971step1 raw971step1Labels := by
      have ha : raw971step1 = -raw971step0 := by apply Matrix.ext; change ∀ i j, raw971step1 i j = -(raw971step0 i j); unfold raw971step1 raw971step0; decide +kernel
      have hl : raw971step1Labels = raw971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw971step1 raw971step1Labels = mixedMoment B raw971step2 raw971step2Labels := by
      have ha : raw971step2 = raw971step1 := by apply Matrix.ext; unfold raw971step2 raw971step1; decide +kernel
      have hl : raw971step1Labels = labelEmbedding1 ∘ raw971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw971step1 raw971step1Labels raw971step2Labels labelEmbedding1 hl
    _ = mixedMoment B node803 node803Labels := by rfl

def raw972 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw972step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw972step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw972 raw972Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw972 raw972Labels = mixedMoment B raw972step0 raw972step0Labels := by
      have ha : raw972step0 = (fun i j => raw972 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw972step0 raw972; decide +kernel
      have hl : raw972step0Labels = raw972Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw972 raw972Labels permutation32 permutation4
    mixedMoment B raw972step0 raw972step0Labels = mixedMoment B raw972step1 raw972step1Labels := by
      have ha : raw972step1 = raw972step0 := by apply Matrix.ext; unfold raw972step1 raw972step0; decide +kernel
      have hl : raw972step0Labels = labelEmbedding7 ∘ raw972step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw972step0 raw972step0Labels raw972step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw973 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw973 raw973Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw973 raw973Labels = mixedMoment B raw973step0 raw973step0Labels := by
      have ha : raw973step0 = (fun i j => raw973 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw973step0 raw973; decide +kernel
      have hl : raw973step0Labels = raw973Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw973 raw973Labels permutation32 permutation4
    _ = mixedMoment B node785 node785Labels := by rfl

def raw974 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 3, -2]]
def raw974Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw974step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw974 raw974Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw974 raw974Labels = mixedMoment B raw974step0 raw974step0Labels := by
      have ha : raw974step0 = (fun i j => raw974 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw974step0 raw974; decide +kernel
      have hl : raw974step0Labels = raw974Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw974 raw974Labels permutation44 permutation6
    mixedMoment B raw974step0 raw974step0Labels = mixedMoment B raw974step1 raw974step1Labels := by
      have ha : raw974step1 = -raw974step0 := by apply Matrix.ext; change ∀ i j, raw974step1 i j = -(raw974step0 i j); unfold raw974step1 raw974step0; decide +kernel
      have hl : raw974step1Labels = raw974step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw974step1 raw974step1Labels = mixedMoment B raw974step2 raw974step2Labels := by
      have ha : raw974step2 = raw974step1 := by apply Matrix.ext; unfold raw974step2 raw974step1; decide +kernel
      have hl : raw974step1Labels = labelEmbedding1 ∘ raw974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw974step1 raw974step1Labels raw974step2Labels labelEmbedding1 hl
    _ = mixedMoment B node804 node804Labels := by rfl

def raw975 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw975step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw975 raw975Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw975 raw975Labels = mixedMoment B raw975step0 raw975step0Labels := by
      have ha : raw975step0 = (fun i j => raw975 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw975step0 raw975; decide +kernel
      have hl : raw975step0Labels = raw975Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw975 raw975Labels permutation152 permutation4
    mixedMoment B raw975step0 raw975step0Labels = mixedMoment B raw975step1 raw975step1Labels := by
      have ha : raw975step1 = raw975step0 := by apply Matrix.ext; unfold raw975step1 raw975step0; decide +kernel
      have hl : raw975step0Labels = labelEmbedding7 ∘ raw975step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw975step0 raw975step0Labels raw975step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

def raw976 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw976 raw976Labels = mixedMoment B node786 node786Labels := by
  calc
    mixedMoment B raw976 raw976Labels = mixedMoment B raw976step0 raw976step0Labels := by
      have ha : raw976step0 = (fun i j => raw976 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw976step0 raw976; decide +kernel
      have hl : raw976step0Labels = raw976Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw976 raw976Labels permutation152 permutation4
    _ = mixedMoment B node786 node786Labels := by rfl

def raw977 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw977Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw977step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw977step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw977 raw977Labels = mixedMoment B node822 node822Labels := by
  calc
    mixedMoment B raw977 raw977Labels = mixedMoment B raw977step0 raw977step0Labels := by
      have ha : raw977step0 = (fun i j => raw977 (permutation246 i) (permutation6 j)) := by apply Matrix.ext; unfold raw977step0 raw977; decide +kernel
      have hl : raw977step0Labels = raw977Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw977 raw977Labels permutation246 permutation6
    mixedMoment B raw977step0 raw977step0Labels = mixedMoment B raw977step1 raw977step1Labels := by
      have ha : raw977step1 = -raw977step0 := by apply Matrix.ext; change ∀ i j, raw977step1 i j = -(raw977step0 i j); unfold raw977step1 raw977step0; decide +kernel
      have hl : raw977step1Labels = raw977step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw977step1 raw977step1Labels = mixedMoment B raw977step2 raw977step2Labels := by
      have ha : raw977step2 = raw977step1 := by apply Matrix.ext; unfold raw977step2 raw977step1; decide +kernel
      have hl : raw977step1Labels = labelEmbedding1 ∘ raw977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw977step1 raw977step1Labels raw977step2Labels labelEmbedding1 hl
    _ = mixedMoment B node822 node822Labels := by rfl

def raw978 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw978step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw978step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw978 raw978Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw978 raw978Labels = mixedMoment B raw978step0 raw978step0Labels := by
      have ha : raw978step0 = (fun i j => raw978 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw978step0 raw978; decide +kernel
      have hl : raw978step0Labels = raw978Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw978 raw978Labels permutation32 permutation4
    mixedMoment B raw978step0 raw978step0Labels = mixedMoment B raw978step1 raw978step1Labels := by
      have ha : raw978step1 = raw978step0 := by apply Matrix.ext; unfold raw978step1 raw978step0; decide +kernel
      have hl : raw978step0Labels = labelEmbedding7 ∘ raw978step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw978step0 raw978step0Labels raw978step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4253 node4253Labels := by rfl

def raw979 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw979 raw979Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw979 raw979Labels = mixedMoment B raw979step0 raw979step0Labels := by
      have ha : raw979step0 = (fun i j => raw979 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw979step0 raw979; decide +kernel
      have hl : raw979step0Labels = raw979Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw979 raw979Labels permutation32 permutation4
    _ = mixedMoment B node787 node787Labels := by rfl

def raw980 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw980Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw980step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw980 raw980Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw980 raw980Labels = mixedMoment B raw980step0 raw980step0Labels := by
      have ha : raw980step0 = (fun i j => raw980 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw980step0 raw980; decide +kernel
      have hl : raw980step0Labels = raw980Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw980 raw980Labels permutation32 permutation6
    mixedMoment B raw980step0 raw980step0Labels = mixedMoment B raw980step1 raw980step1Labels := by
      have ha : raw980step1 = -raw980step0 := by apply Matrix.ext; change ∀ i j, raw980step1 i j = -(raw980step0 i j); unfold raw980step1 raw980step0; decide +kernel
      have hl : raw980step1Labels = raw980step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw980step1 raw980step1Labels = mixedMoment B raw980step2 raw980step2Labels := by
      have ha : raw980step2 = raw980step1 := by apply Matrix.ext; unfold raw980step2 raw980step1; decide +kernel
      have hl : raw980step1Labels = labelEmbedding1 ∘ raw980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw980step1 raw980step1Labels raw980step2Labels labelEmbedding1 hl
    _ = mixedMoment B node847 node847Labels := by rfl

def raw981 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw981step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw981step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw981 raw981Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw981 raw981Labels = mixedMoment B raw981step0 raw981step0Labels := by
      have ha : raw981step0 = (fun i j => raw981 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw981step0 raw981; decide +kernel
      have hl : raw981step0Labels = raw981Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw981 raw981Labels permutation32 permutation4
    mixedMoment B raw981step0 raw981step0Labels = mixedMoment B raw981step1 raw981step1Labels := by
      have ha : raw981step1 = raw981step0 := by apply Matrix.ext; unfold raw981step1 raw981step0; decide +kernel
      have hl : raw981step0Labels = labelEmbedding7 ∘ raw981step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw981step0 raw981step0Labels raw981step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

def raw982 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw982 raw982Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw982 raw982Labels = mixedMoment B raw982step0 raw982step0Labels := by
      have ha : raw982step0 = (fun i j => raw982 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw982step0 raw982; decide +kernel
      have hl : raw982step0Labels = raw982Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw982 raw982Labels permutation32 permutation4
    _ = mixedMoment B node789 node789Labels := by rfl

def raw983 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw983Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw983step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw983 raw983Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw983 raw983Labels = mixedMoment B raw983step0 raw983step0Labels := by
      have ha : raw983step0 = (fun i j => raw983 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw983step0 raw983; decide +kernel
      have hl : raw983step0Labels = raw983Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw983 raw983Labels permutation44 permutation6
    mixedMoment B raw983step0 raw983step0Labels = mixedMoment B raw983step1 raw983step1Labels := by
      have ha : raw983step1 = -raw983step0 := by apply Matrix.ext; change ∀ i j, raw983step1 i j = -(raw983step0 i j); unfold raw983step1 raw983step0; decide +kernel
      have hl : raw983step1Labels = raw983step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw983step1 raw983step1Labels = mixedMoment B raw983step2 raw983step2Labels := by
      have ha : raw983step2 = raw983step1 := by apply Matrix.ext; unfold raw983step2 raw983step1; decide +kernel
      have hl : raw983step1Labels = labelEmbedding1 ∘ raw983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw983step1 raw983step1Labels raw983step2Labels labelEmbedding1 hl
    _ = mixedMoment B node823 node823Labels := by rfl

def raw984 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw984step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw984 raw984Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw984 raw984Labels = mixedMoment B raw984step0 raw984step0Labels := by
      have ha : raw984step0 = (fun i j => raw984 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw984step0 raw984; decide +kernel
      have hl : raw984step0Labels = raw984Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw984 raw984Labels permutation32 permutation4
    mixedMoment B raw984step0 raw984step0Labels = mixedMoment B raw984step1 raw984step1Labels := by
      have ha : raw984step1 = raw984step0 := by apply Matrix.ext; unfold raw984step1 raw984step0; decide +kernel
      have hl : raw984step0Labels = labelEmbedding7 ∘ raw984step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw984step0 raw984step0Labels raw984step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4256 node4256Labels := by rfl

def raw985 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw985 raw985Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw985 raw985Labels = mixedMoment B raw985step0 raw985step0Labels := by
      have ha : raw985step0 = (fun i j => raw985 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw985step0 raw985; decide +kernel
      have hl : raw985step0Labels = raw985Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw985 raw985Labels permutation32 permutation4
    _ = mixedMoment B node790 node790Labels := by rfl

def raw986 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw986Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw986 raw986Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw986 raw986Labels = mixedMoment B raw986step0 raw986step0Labels := by
      have ha : raw986step0 = (fun i j => raw986 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw986step0 raw986; decide +kernel
      have hl : raw986step0Labels = raw986Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw986 raw986Labels permutation32 permutation6
    mixedMoment B raw986step0 raw986step0Labels = mixedMoment B raw986step1 raw986step1Labels := by
      have ha : raw986step1 = -raw986step0 := by apply Matrix.ext; change ∀ i j, raw986step1 i j = -(raw986step0 i j); unfold raw986step1 raw986step0; decide +kernel
      have hl : raw986step1Labels = raw986step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw986step1 raw986step1Labels = mixedMoment B raw986step2 raw986step2Labels := by
      have ha : raw986step2 = raw986step1 := by apply Matrix.ext; unfold raw986step2 raw986step1; decide +kernel
      have hl : raw986step1Labels = labelEmbedding1 ∘ raw986step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw986step1 raw986step1Labels raw986step2Labels labelEmbedding1 hl
    _ = mixedMoment B node848 node848Labels := by rfl

def raw987 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]
def raw987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw987step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw987step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw987 raw987Labels = mixedMoment B node4257 node4257Labels := by
  calc
    mixedMoment B raw987 raw987Labels = mixedMoment B raw987step0 raw987step0Labels := by
      have ha : raw987step0 = (fun i j => raw987 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw987step0 raw987; decide +kernel
      have hl : raw987step0Labels = raw987Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw987 raw987Labels permutation8 permutation4
    mixedMoment B raw987step0 raw987step0Labels = mixedMoment B raw987step1 raw987step1Labels := by
      have ha : raw987step1 = raw987step0 := by apply Matrix.ext; unfold raw987step1 raw987step0; decide +kernel
      have hl : raw987step0Labels = labelEmbedding7 ∘ raw987step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw987step0 raw987step0Labels raw987step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4257 node4257Labels := by rfl

def raw988 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]
def raw988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw988step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw988 raw988Labels = mixedMoment B node791 node791Labels := by
  calc
    mixedMoment B raw988 raw988Labels = mixedMoment B raw988step0 raw988step0Labels := by
      have ha : raw988step0 = (fun i j => raw988 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw988step0 raw988; decide +kernel
      have hl : raw988step0Labels = raw988Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw988 raw988Labels permutation8 permutation4
    _ = mixedMoment B node791 node791Labels := by rfl

def raw989 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 0, -1], ![-2, 4, -2]]
def raw989Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw989step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw989 raw989Labels = mixedMoment B node849 node849Labels := by
  calc
    mixedMoment B raw989 raw989Labels = mixedMoment B raw989step0 raw989step0Labels := by
      have ha : raw989step0 = (fun i j => raw989 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw989step0 raw989; decide +kernel
      have hl : raw989step0Labels = raw989Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw989 raw989Labels permutation8 permutation6
    mixedMoment B raw989step0 raw989step0Labels = mixedMoment B raw989step1 raw989step1Labels := by
      have ha : raw989step1 = -raw989step0 := by apply Matrix.ext; change ∀ i j, raw989step1 i j = -(raw989step0 i j); unfold raw989step1 raw989step0; decide +kernel
      have hl : raw989step1Labels = raw989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw989step1 raw989step1Labels = mixedMoment B raw989step2 raw989step2Labels := by
      have ha : raw989step2 = raw989step1 := by apply Matrix.ext; unfold raw989step2 raw989step1; decide +kernel
      have hl : raw989step1Labels = labelEmbedding1 ∘ raw989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw989step1 raw989step1Labels raw989step2Labels labelEmbedding1 hl
    _ = mixedMoment B node849 node849Labels := by rfl

def raw990 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw990step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw990step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw990 raw990Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw990 raw990Labels = mixedMoment B raw990step0 raw990step0Labels := by
      have ha : raw990step0 = (fun i j => raw990 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw990step0 raw990; decide +kernel
      have hl : raw990step0Labels = raw990Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw990 raw990Labels permutation32 permutation4
    mixedMoment B raw990step0 raw990step0Labels = mixedMoment B raw990step1 raw990step1Labels := by
      have ha : raw990step1 = raw990step0 := by apply Matrix.ext; unfold raw990step1 raw990step0; decide +kernel
      have hl : raw990step0Labels = labelEmbedding7 ∘ raw990step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw990step0 raw990step0Labels raw990step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw991 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw991step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw991 raw991Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw991 raw991Labels = mixedMoment B raw991step0 raw991step0Labels := by
      have ha : raw991step0 = (fun i j => raw991 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw991step0 raw991; decide +kernel
      have hl : raw991step0Labels = raw991Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw991 raw991Labels permutation32 permutation4
    _ = mixedMoment B node807 node807Labels := by rfl

def raw992 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw992Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw992 raw992Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw992 raw992Labels = mixedMoment B raw992step0 raw992step0Labels := by
      have ha : raw992step0 = (fun i j => raw992 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw992step0 raw992; decide +kernel
      have hl : raw992step0Labels = raw992Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw992 raw992Labels permutation39 permutation6
    mixedMoment B raw992step0 raw992step0Labels = mixedMoment B raw992step1 raw992step1Labels := by
      have ha : raw992step1 = -raw992step0 := by apply Matrix.ext; change ∀ i j, raw992step1 i j = -(raw992step0 i j); unfold raw992step1 raw992step0; decide +kernel
      have hl : raw992step1Labels = raw992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw992step1 raw992step1Labels = mixedMoment B raw992step2 raw992step2Labels := by
      have ha : raw992step2 = raw992step1 := by apply Matrix.ext; unfold raw992step2 raw992step1; decide +kernel
      have hl : raw992step1Labels = labelEmbedding1 ∘ raw992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw992step1 raw992step1Labels raw992step2Labels labelEmbedding1 hl
    _ = mixedMoment B node807 node807Labels := by rfl

def raw993 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw993step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw993 raw993Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw993 raw993Labels = mixedMoment B raw993step0 raw993step0Labels := by
      have ha : raw993step0 = (fun i j => raw993 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw993step0 raw993; decide +kernel
      have hl : raw993step0Labels = raw993Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw993 raw993Labels permutation32 permutation4
    mixedMoment B raw993step0 raw993step0Labels = mixedMoment B raw993step1 raw993step1Labels := by
      have ha : raw993step1 = raw993step0 := by apply Matrix.ext; unfold raw993step1 raw993step0; decide +kernel
      have hl : raw993step0Labels = labelEmbedding7 ∘ raw993step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw993step0 raw993step0Labels raw993step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw994 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw994 raw994Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw994 raw994Labels = mixedMoment B raw994step0 raw994step0Labels := by
      have ha : raw994step0 = (fun i j => raw994 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw994step0 raw994; decide +kernel
      have hl : raw994step0Labels = raw994Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw994 raw994Labels permutation32 permutation4
    _ = mixedMoment B node811 node811Labels := by rfl

def raw995 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw995Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw995step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw995step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw995 raw995Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw995 raw995Labels = mixedMoment B raw995step0 raw995step0Labels := by
      have ha : raw995step0 = (fun i j => raw995 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw995step0 raw995; decide +kernel
      have hl : raw995step0Labels = raw995Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw995 raw995Labels permutation50 permutation6
    mixedMoment B raw995step0 raw995step0Labels = mixedMoment B raw995step1 raw995step1Labels := by
      have ha : raw995step1 = -raw995step0 := by apply Matrix.ext; change ∀ i j, raw995step1 i j = -(raw995step0 i j); unfold raw995step1 raw995step0; decide +kernel
      have hl : raw995step1Labels = raw995step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw995step1 raw995step1Labels = mixedMoment B raw995step2 raw995step2Labels := by
      have ha : raw995step2 = raw995step1 := by apply Matrix.ext; unfold raw995step2 raw995step1; decide +kernel
      have hl : raw995step1Labels = labelEmbedding1 ∘ raw995step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw995step1 raw995step1Labels raw995step2Labels labelEmbedding1 hl
    _ = mixedMoment B node824 node824Labels := by rfl

def raw996 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw996step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw996step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw996step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw996 raw996Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw996 raw996Labels = mixedMoment B raw996step0 raw996step0Labels := by
      have ha : raw996step0 = (fun i j => raw996 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw996step0 raw996; decide +kernel
      have hl : raw996step0Labels = raw996Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw996 raw996Labels permutation8 permutation4
    mixedMoment B raw996step0 raw996step0Labels = mixedMoment B raw996step1 raw996step1Labels := by
      have ha : raw996step1 = raw996step0 := by apply Matrix.ext; unfold raw996step1 raw996step0; decide +kernel
      have hl : raw996step0Labels = labelEmbedding7 ∘ raw996step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw996step0 raw996step0Labels raw996step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4270 node4270Labels := by rfl

def raw997 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw997step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw997 raw997Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw997 raw997Labels = mixedMoment B raw997step0 raw997step0Labels := by
      have ha : raw997step0 = (fun i j => raw997 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw997step0 raw997; decide +kernel
      have hl : raw997step0Labels = raw997Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw997 raw997Labels permutation8 permutation4
    _ = mixedMoment B node813 node813Labels := by rfl

def raw998 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw998Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw998step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw998 raw998Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw998 raw998Labels = mixedMoment B raw998step0 raw998step0Labels := by
      have ha : raw998step0 = (fun i j => raw998 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw998step0 raw998; decide +kernel
      have hl : raw998step0Labels = raw998Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw998 raw998Labels permutation9 permutation6
    mixedMoment B raw998step0 raw998step0Labels = mixedMoment B raw998step1 raw998step1Labels := by
      have ha : raw998step1 = -raw998step0 := by apply Matrix.ext; change ∀ i j, raw998step1 i j = -(raw998step0 i j); unfold raw998step1 raw998step0; decide +kernel
      have hl : raw998step1Labels = raw998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw998step1 raw998step1Labels = mixedMoment B raw998step2 raw998step2Labels := by
      have ha : raw998step2 = raw998step1 := by apply Matrix.ext; unfold raw998step2 raw998step1; decide +kernel
      have hl : raw998step1Labels = labelEmbedding1 ∘ raw998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw998step1 raw998step1Labels raw998step2Labels labelEmbedding1 hl
    _ = mixedMoment B node853 node853Labels := by rfl

def raw999 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw999step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw999step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw999 raw999Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw999 raw999Labels = mixedMoment B raw999step0 raw999step0Labels := by
      have ha : raw999step0 = (fun i j => raw999 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw999step0 raw999; decide +kernel
      have hl : raw999step0Labels = raw999Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw999 raw999Labels permutation8 permutation4
    mixedMoment B raw999step0 raw999step0Labels = mixedMoment B raw999step1 raw999step1Labels := by
      have ha : raw999step1 = raw999step0 := by apply Matrix.ext; unfold raw999step1 raw999step0; decide +kernel
      have hl : raw999step0Labels = labelEmbedding7 ∘ raw999step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw999step0 raw999step0Labels raw999step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

def raw1000 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1000step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1000 raw1000Labels = mixedMoment B node815 node815Labels := by
  calc
    mixedMoment B raw1000 raw1000Labels = mixedMoment B raw1000step0 raw1000step0Labels := by
      have ha : raw1000step0 = (fun i j => raw1000 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1000step0 raw1000; decide +kernel
      have hl : raw1000step0Labels = raw1000Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1000 raw1000Labels permutation8 permutation4
    _ = mixedMoment B node815 node815Labels := by rfl

def raw1001 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![1, 0, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1001Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1001step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw1001step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw1001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw1001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1001 raw1001Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw1001 raw1001Labels = mixedMoment B raw1001step0 raw1001step0Labels := by
      have ha : raw1001step0 = (fun i j => raw1001 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1001step0 raw1001; decide +kernel
      have hl : raw1001step0Labels = raw1001Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1001 raw1001Labels permutation10 permutation6
    mixedMoment B raw1001step0 raw1001step0Labels = mixedMoment B raw1001step1 raw1001step1Labels := by
      have ha : raw1001step1 = -raw1001step0 := by apply Matrix.ext; change ∀ i j, raw1001step1 i j = -(raw1001step0 i j); unfold raw1001step1 raw1001step0; decide +kernel
      have hl : raw1001step1Labels = raw1001step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1001step1 raw1001step1Labels = mixedMoment B raw1001step2 raw1001step2Labels := by
      have ha : raw1001step2 = raw1001step1 := by apply Matrix.ext; unfold raw1001step2 raw1001step1; decide +kernel
      have hl : raw1001step1Labels = labelEmbedding1 ∘ raw1001step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1001step1 raw1001step1Labels raw1001step2Labels labelEmbedding1 hl
    _ = mixedMoment B node826 node826Labels := by rfl

def raw1002 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1002step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1002 raw1002Labels = mixedMoment B node4275 node4275Labels := by
  calc
    mixedMoment B raw1002 raw1002Labels = mixedMoment B raw1002step0 raw1002step0Labels := by
      have ha : raw1002step0 = (fun i j => raw1002 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1002step0 raw1002; decide +kernel
      have hl : raw1002step0Labels = raw1002Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1002 raw1002Labels permutation32 permutation4
    mixedMoment B raw1002step0 raw1002step0Labels = mixedMoment B raw1002step1 raw1002step1Labels := by
      have ha : raw1002step1 = raw1002step0 := by apply Matrix.ext; unfold raw1002step1 raw1002step0; decide +kernel
      have hl : raw1002step0Labels = labelEmbedding7 ∘ raw1002step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1002step0 raw1002step0Labels raw1002step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4275 node4275Labels := by rfl

def raw1003 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1003 raw1003Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw1003 raw1003Labels = mixedMoment B raw1003step0 raw1003step0Labels := by
      have ha : raw1003step0 = (fun i j => raw1003 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1003step0 raw1003; decide +kernel
      have hl : raw1003step0Labels = raw1003Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1003 raw1003Labels permutation32 permutation4
    _ = mixedMoment B node827 node827Labels := by rfl

def raw1004 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1004Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw1004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1004 raw1004Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw1004 raw1004Labels = mixedMoment B raw1004step0 raw1004step0Labels := by
      have ha : raw1004step0 = (fun i j => raw1004 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1004step0 raw1004; decide +kernel
      have hl : raw1004step0Labels = raw1004Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1004 raw1004Labels permutation53 permutation6
    mixedMoment B raw1004step0 raw1004step0Labels = mixedMoment B raw1004step1 raw1004step1Labels := by
      have ha : raw1004step1 = -raw1004step0 := by apply Matrix.ext; change ∀ i j, raw1004step1 i j = -(raw1004step0 i j); unfold raw1004step1 raw1004step0; decide +kernel
      have hl : raw1004step1Labels = raw1004step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1004step1 raw1004step1Labels = mixedMoment B raw1004step2 raw1004step2Labels := by
      have ha : raw1004step2 = raw1004step1 := by apply Matrix.ext; unfold raw1004step2 raw1004step1; decide +kernel
      have hl : raw1004step1Labels = labelEmbedding1 ∘ raw1004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1004step1 raw1004step1Labels raw1004step2Labels labelEmbedding1 hl
    _ = mixedMoment B node827 node827Labels := by rfl

def raw1005 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1005step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1005step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1005 raw1005Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw1005 raw1005Labels = mixedMoment B raw1005step0 raw1005step0Labels := by
      have ha : raw1005step0 = (fun i j => raw1005 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1005step0 raw1005; decide +kernel
      have hl : raw1005step0Labels = raw1005Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1005 raw1005Labels permutation8 permutation4
    mixedMoment B raw1005step0 raw1005step0Labels = mixedMoment B raw1005step1 raw1005step1Labels := by
      have ha : raw1005step1 = raw1005step0 := by apply Matrix.ext; unfold raw1005step1 raw1005step0; decide +kernel
      have hl : raw1005step0Labels = labelEmbedding7 ∘ raw1005step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1005step0 raw1005step0Labels raw1005step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4276 node4276Labels := by rfl

def raw1006 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1006step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw1006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1006 raw1006Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw1006 raw1006Labels = mixedMoment B raw1006step0 raw1006step0Labels := by
      have ha : raw1006step0 = (fun i j => raw1006 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1006step0 raw1006; decide +kernel
      have hl : raw1006step0Labels = raw1006Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1006 raw1006Labels permutation8 permutation4
    _ = mixedMoment B node828 node828Labels := by rfl

def raw1007 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![0, 1, -1], ![-2, 3, -1]]
def raw1007Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1007step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw1007step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw1007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw1007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1007 raw1007Labels = mixedMoment B node857 node857Labels := by
  calc
    mixedMoment B raw1007 raw1007Labels = mixedMoment B raw1007step0 raw1007step0Labels := by
      have ha : raw1007step0 = (fun i j => raw1007 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1007step0 raw1007; decide +kernel
      have hl : raw1007step0Labels = raw1007Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1007 raw1007Labels permutation11 permutation6
    mixedMoment B raw1007step0 raw1007step0Labels = mixedMoment B raw1007step1 raw1007step1Labels := by
      have ha : raw1007step1 = -raw1007step0 := by apply Matrix.ext; change ∀ i j, raw1007step1 i j = -(raw1007step0 i j); unfold raw1007step1 raw1007step0; decide +kernel
      have hl : raw1007step1Labels = raw1007step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1007step1 raw1007step1Labels = mixedMoment B raw1007step2 raw1007step2Labels := by
      have ha : raw1007step2 = raw1007step1 := by apply Matrix.ext; unfold raw1007step2 raw1007step1; decide +kernel
      have hl : raw1007step1Labels = labelEmbedding1 ∘ raw1007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1007step1 raw1007step1Labels raw1007step2Labels labelEmbedding1 hl
    _ = mixedMoment B node857 node857Labels := by rfl

def raw1008 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1008step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1008step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1008step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1008 raw1008Labels = mixedMoment B node4278 node4278Labels := by
  calc
    mixedMoment B raw1008 raw1008Labels = mixedMoment B raw1008step0 raw1008step0Labels := by
      have ha : raw1008step0 = (fun i j => raw1008 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1008step0 raw1008; decide +kernel
      have hl : raw1008step0Labels = raw1008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1008 raw1008Labels permutation8 permutation4
    mixedMoment B raw1008step0 raw1008step0Labels = mixedMoment B raw1008step1 raw1008step1Labels := by
      have ha : raw1008step1 = raw1008step0 := by apply Matrix.ext; unfold raw1008step1 raw1008step0; decide +kernel
      have hl : raw1008step0Labels = labelEmbedding7 ∘ raw1008step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1008step0 raw1008step0Labels raw1008step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4278 node4278Labels := by rfl

def raw1009 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1009step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1009 raw1009Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw1009 raw1009Labels = mixedMoment B raw1009step0 raw1009step0Labels := by
      have ha : raw1009step0 = (fun i j => raw1009 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1009step0 raw1009; decide +kernel
      have hl : raw1009step0Labels = raw1009Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1009 raw1009Labels permutation8 permutation4
    _ = mixedMoment B node830 node830Labels := by rfl

def raw1010 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1010Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1010step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw1010step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1010step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1010 raw1010Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw1010 raw1010Labels = mixedMoment B raw1010step0 raw1010step0Labels := by
      have ha : raw1010step0 = (fun i j => raw1010 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1010step0 raw1010; decide +kernel
      have hl : raw1010step0Labels = raw1010Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1010 raw1010Labels permutation10 permutation6
    mixedMoment B raw1010step0 raw1010step0Labels = mixedMoment B raw1010step1 raw1010step1Labels := by
      have ha : raw1010step1 = -raw1010step0 := by apply Matrix.ext; change ∀ i j, raw1010step1 i j = -(raw1010step0 i j); unfold raw1010step1 raw1010step0; decide +kernel
      have hl : raw1010step1Labels = raw1010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1010step1 raw1010step1Labels = mixedMoment B raw1010step2 raw1010step2Labels := by
      have ha : raw1010step2 = raw1010step1 := by apply Matrix.ext; unfold raw1010step2 raw1010step1; decide +kernel
      have hl : raw1010step1Labels = labelEmbedding1 ∘ raw1010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1010step1 raw1010step1Labels raw1010step2Labels labelEmbedding1 hl
    _ = mixedMoment B node830 node830Labels := by rfl

def raw1011 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1011step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1011step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1011step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1011 raw1011Labels = mixedMoment B node4279 node4279Labels := by
  calc
    mixedMoment B raw1011 raw1011Labels = mixedMoment B raw1011step0 raw1011step0Labels := by
      have ha : raw1011step0 = (fun i j => raw1011 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1011step0 raw1011; decide +kernel
      have hl : raw1011step0Labels = raw1011Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1011 raw1011Labels permutation8 permutation4
    mixedMoment B raw1011step0 raw1011step0Labels = mixedMoment B raw1011step1 raw1011step1Labels := by
      have ha : raw1011step1 = raw1011step0 := by apply Matrix.ext; unfold raw1011step1 raw1011step0; decide +kernel
      have hl : raw1011step0Labels = labelEmbedding7 ∘ raw1011step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1011step0 raw1011step0Labels raw1011step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4279 node4279Labels := by rfl

def raw1012 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1012step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1012 raw1012Labels = mixedMoment B node831 node831Labels := by
  calc
    mixedMoment B raw1012 raw1012Labels = mixedMoment B raw1012step0 raw1012step0Labels := by
      have ha : raw1012step0 = (fun i j => raw1012 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1012step0 raw1012; decide +kernel
      have hl : raw1012step0Labels = raw1012Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1012 raw1012Labels permutation8 permutation4
    _ = mixedMoment B node831 node831Labels := by rfl

def raw1013 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1013Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1013step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw1013step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw1013step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw1013step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1013 raw1013Labels = mixedMoment B node858 node858Labels := by
  calc
    mixedMoment B raw1013 raw1013Labels = mixedMoment B raw1013step0 raw1013step0Labels := by
      have ha : raw1013step0 = (fun i j => raw1013 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1013step0 raw1013; decide +kernel
      have hl : raw1013step0Labels = raw1013Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1013 raw1013Labels permutation11 permutation6
    mixedMoment B raw1013step0 raw1013step0Labels = mixedMoment B raw1013step1 raw1013step1Labels := by
      have ha : raw1013step1 = -raw1013step0 := by apply Matrix.ext; change ∀ i j, raw1013step1 i j = -(raw1013step0 i j); unfold raw1013step1 raw1013step0; decide +kernel
      have hl : raw1013step1Labels = raw1013step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1013step1 raw1013step1Labels = mixedMoment B raw1013step2 raw1013step2Labels := by
      have ha : raw1013step2 = raw1013step1 := by apply Matrix.ext; unfold raw1013step2 raw1013step1; decide +kernel
      have hl : raw1013step1Labels = labelEmbedding1 ∘ raw1013step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1013step1 raw1013step1Labels raw1013step2Labels labelEmbedding1 hl
    _ = mixedMoment B node858 node858Labels := by rfl

def raw1014 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 4, -2]]
def raw1014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1014step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw1014step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1014step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw1014step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1014 raw1014Labels = mixedMoment B node4280 node4280Labels := by
  calc
    mixedMoment B raw1014 raw1014Labels = mixedMoment B raw1014step0 raw1014step0Labels := by
      have ha : raw1014step0 = (fun i j => raw1014 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1014step0 raw1014; decide +kernel
      have hl : raw1014step0Labels = raw1014Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1014 raw1014Labels permutation2 permutation4
    mixedMoment B raw1014step0 raw1014step0Labels = mixedMoment B raw1014step1 raw1014step1Labels := by
      have ha : raw1014step1 = raw1014step0 := by apply Matrix.ext; unfold raw1014step1 raw1014step0; decide +kernel
      have hl : raw1014step0Labels = labelEmbedding7 ∘ raw1014step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1014step0 raw1014step0Labels raw1014step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4280 node4280Labels := by rfl

def raw1015 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 4, -2]]
def raw1015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1015step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw1015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1015 raw1015Labels = mixedMoment B node832 node832Labels := by
  calc
    mixedMoment B raw1015 raw1015Labels = mixedMoment B raw1015step0 raw1015step0Labels := by
      have ha : raw1015step0 = (fun i j => raw1015 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1015step0 raw1015; decide +kernel
      have hl : raw1015step0Labels = raw1015Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1015 raw1015Labels permutation2 permutation4
    _ = mixedMoment B node832 node832Labels := by rfl

def raw1016 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 0, -2], ![-2, 4, -2]]
def raw1016Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1016step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-2, 2, 0], ![-2, -2, 4]]
def raw1016step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1016step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def raw1016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1016step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def raw1016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1016 raw1016Labels = mixedMoment B node862 node862Labels := by
  calc
    mixedMoment B raw1016 raw1016Labels = mixedMoment B raw1016step0 raw1016step0Labels := by
      have ha : raw1016step0 = (fun i j => raw1016 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1016step0 raw1016; decide +kernel
      have hl : raw1016step0Labels = raw1016Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1016 raw1016Labels permutation2 permutation6
    mixedMoment B raw1016step0 raw1016step0Labels = mixedMoment B raw1016step1 raw1016step1Labels := by
      have ha : raw1016step1 = -raw1016step0 := by apply Matrix.ext; change ∀ i j, raw1016step1 i j = -(raw1016step0 i j); unfold raw1016step1 raw1016step0; decide +kernel
      have hl : raw1016step1Labels = raw1016step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1016step1 raw1016step1Labels = mixedMoment B raw1016step2 raw1016step2Labels := by
      have ha : raw1016step2 = raw1016step1 := by apply Matrix.ext; unfold raw1016step2 raw1016step1; decide +kernel
      have hl : raw1016step1Labels = labelEmbedding1 ∘ raw1016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1016step1 raw1016step1Labels raw1016step2Labels labelEmbedding1 hl
    _ = mixedMoment B node862 node862Labels := by rfl

def raw1017 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 1, -3], ![-2, 3, -1]]
def raw1017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1017step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw1017step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1017step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw1017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1017 raw1017Labels = mixedMoment B node4285 node4285Labels := by
  calc
    mixedMoment B raw1017 raw1017Labels = mixedMoment B raw1017step0 raw1017step0Labels := by
      have ha : raw1017step0 = (fun i j => raw1017 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1017step0 raw1017; decide +kernel
      have hl : raw1017step0Labels = raw1017Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1017 raw1017Labels permutation2 permutation4
    mixedMoment B raw1017step0 raw1017step0Labels = mixedMoment B raw1017step1 raw1017step1Labels := by
      have ha : raw1017step1 = raw1017step0 := by apply Matrix.ext; unfold raw1017step1 raw1017step0; decide +kernel
      have hl : raw1017step0Labels = labelEmbedding7 ∘ raw1017step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1017step0 raw1017step0Labels raw1017step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4285 node4285Labels := by rfl

def raw1018 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 1, -3], ![-2, 3, -1]]
def raw1018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1018step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw1018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1018 raw1018Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw1018 raw1018Labels = mixedMoment B raw1018step0 raw1018step0Labels := by
      have ha : raw1018step0 = (fun i j => raw1018 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1018step0 raw1018; decide +kernel
      have hl : raw1018step0Labels = raw1018Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1018 raw1018Labels permutation2 permutation4
    _ = mixedMoment B node860 node860Labels := by rfl

def raw1019 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, -4, 4], ![2, 1, -3], ![-2, 3, -1]]
def raw1019Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1019step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw1019step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1019step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw1019step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1019step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw1019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1019 raw1019Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw1019 raw1019Labels = mixedMoment B raw1019step0 raw1019step0Labels := by
      have ha : raw1019step0 = (fun i j => raw1019 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1019step0 raw1019; decide +kernel
      have hl : raw1019step0Labels = raw1019Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1019 raw1019Labels permutation3 permutation6
    mixedMoment B raw1019step0 raw1019step0Labels = mixedMoment B raw1019step1 raw1019step1Labels := by
      have ha : raw1019step1 = -raw1019step0 := by apply Matrix.ext; change ∀ i j, raw1019step1 i j = -(raw1019step0 i j); unfold raw1019step1 raw1019step0; decide +kernel
      have hl : raw1019step1Labels = raw1019step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1019step1 raw1019step1Labels = mixedMoment B raw1019step2 raw1019step2Labels := by
      have ha : raw1019step2 = raw1019step1 := by apply Matrix.ext; unfold raw1019step2 raw1019step1; decide +kernel
      have hl : raw1019step1Labels = labelEmbedding1 ∘ raw1019step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1019step1 raw1019step1Labels raw1019step2Labels labelEmbedding1 hl
    _ = mixedMoment B node860 node860Labels := by rfl

def raw1020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1020step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1020 raw1020Labels = mixedMoment B node4286 node4286Labels := by
  calc
    mixedMoment B raw1020 raw1020Labels = mixedMoment B raw1020step0 raw1020step0Labels := by
      have ha : raw1020step0 = (fun i j => raw1020 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1020step0 raw1020; decide +kernel
      have hl : raw1020step0Labels = raw1020Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1020 raw1020Labels permutation152 permutation4
    mixedMoment B raw1020step0 raw1020step0Labels = mixedMoment B raw1020step1 raw1020step1Labels := by
      have ha : raw1020step1 = raw1020step0 := by apply Matrix.ext; unfold raw1020step1 raw1020step0; decide +kernel
      have hl : raw1020step0Labels = labelEmbedding7 ∘ raw1020step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1020step0 raw1020step0Labels raw1020step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4286 node4286Labels := by rfl

def raw1021 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1021 raw1021Labels = mixedMoment B node864 node864Labels := by
  calc
    mixedMoment B raw1021 raw1021Labels = mixedMoment B raw1021step0 raw1021step0Labels := by
      have ha : raw1021step0 = (fun i j => raw1021 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1021step0 raw1021; decide +kernel
      have hl : raw1021step0Labels = raw1021Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1021 raw1021Labels permutation152 permutation4
    _ = mixedMoment B node864 node864Labels := by rfl

def raw1022 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1022Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw1022step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1022step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1022step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1022step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1022 raw1022Labels = mixedMoment B node1550 node1550Labels := by
  calc
    mixedMoment B raw1022 raw1022Labels = mixedMoment B raw1022step0 raw1022step0Labels := by
      have ha : raw1022step0 = (fun i j => raw1022 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1022step0 raw1022; decide +kernel
      have hl : raw1022step0Labels = raw1022Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1022 raw1022Labels permutation160 permutation6
    mixedMoment B raw1022step0 raw1022step0Labels = mixedMoment B raw1022step1 raw1022step1Labels := by
      have ha : raw1022step1 = -raw1022step0 := by apply Matrix.ext; change ∀ i j, raw1022step1 i j = -(raw1022step0 i j); unfold raw1022step1 raw1022step0; decide +kernel
      have hl : raw1022step1Labels = raw1022step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1022step1 raw1022step1Labels = mixedMoment B raw1022step2 raw1022step2Labels := by
      have ha : raw1022step2 = raw1022step1 := by apply Matrix.ext; unfold raw1022step2 raw1022step1; decide +kernel
      have hl : raw1022step1Labels = labelEmbedding1 ∘ raw1022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1022step1 raw1022step1Labels raw1022step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1550 node1550Labels := by rfl

def raw1023 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -4, 3], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1023step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1023step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1023 raw1023Labels = mixedMoment B node4287 node4287Labels := by
  calc
    mixedMoment B raw1023 raw1023Labels = mixedMoment B raw1023step0 raw1023step0Labels := by
      have ha : raw1023step0 = (fun i j => raw1023 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1023step0 raw1023; decide +kernel
      have hl : raw1023step0Labels = raw1023Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1023 raw1023Labels permutation152 permutation4
    mixedMoment B raw1023step0 raw1023step0Labels = mixedMoment B raw1023step1 raw1023step1Labels := by
      have ha : raw1023step1 = raw1023step0 := by apply Matrix.ext; unfold raw1023step1 raw1023step0; decide +kernel
      have hl : raw1023step0Labels = labelEmbedding7 ∘ raw1023step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1023step0 raw1023step0Labels raw1023step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4287 node4287Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
