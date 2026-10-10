import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw10112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10112step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10112step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10112step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10112step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10112 raw10112Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw10112 raw10112Labels = mixedMoment B raw10112step0 raw10112step0Labels := by
      have ha : raw10112step0 = (fun i j => raw10112 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10112step0 raw10112; decide +kernel
      have hl : raw10112step0Labels = raw10112Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10112 raw10112Labels permutation676 permutation3
    mixedMoment B raw10112step0 raw10112step0Labels = mixedMoment B raw10112step1 raw10112step1Labels := by
      have ha : raw10112step1 = -raw10112step0 := by apply Matrix.ext; change ∀ i j, raw10112step1 i j = -(raw10112step0 i j); unfold raw10112step1 raw10112step0; decide +kernel
      have hl : raw10112step1Labels = raw10112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10112step1 raw10112step1Labels = mixedMoment B raw10112step2 raw10112step2Labels := by
      have ha : raw10112step2 = raw10112step1 := by apply Matrix.ext; unfold raw10112step2 raw10112step1; decide +kernel
      have hl : raw10112step1Labels = labelEmbedding6 ∘ raw10112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10112step1 raw10112step1Labels raw10112step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw10113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw10113step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10113step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10113step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10113step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10113 raw10113Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw10113 raw10113Labels = mixedMoment B raw10113step0 raw10113step0Labels := by
      have hz : ∀ j, raw10113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10113step0 = (fun i j => raw10113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10113step0 raw10113; decide +kernel
      have hl : raw10113step0Labels = raw10113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10113 raw10113Labels permutation346 hz
    mixedMoment B raw10113step0 raw10113step0Labels = mixedMoment B raw10113step1 raw10113step1Labels := by
      have ha : raw10113step1 = (fun i j => raw10113step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10113step1 raw10113step0; decide +kernel
      have hl : raw10113step1Labels = raw10113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10113step0 raw10113step0Labels permutation149 permutation3
    mixedMoment B raw10113step1 raw10113step1Labels = mixedMoment B raw10113step2 raw10113step2Labels := by
      have ha : raw10113step2 = -raw10113step1 := by apply Matrix.ext; change ∀ i j, raw10113step2 i j = -(raw10113step1 i j); unfold raw10113step2 raw10113step1; decide +kernel
      have hl : raw10113step2Labels = raw10113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10113step2 raw10113step2Labels = mixedMoment B raw10113step3 raw10113step3Labels := by
      have ha : raw10113step3 = raw10113step2 := by apply Matrix.ext; unfold raw10113step3 raw10113step2; decide +kernel
      have hl : raw10113step2Labels = labelEmbedding6 ∘ raw10113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10113step2 raw10113step2Labels raw10113step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw10114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw10114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw10114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10114step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10114step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10114 raw10114Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw10114 raw10114Labels = mixedMoment B raw10114step0 raw10114step0Labels := by
      have hz : ∀ j, raw10114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10114step0 = (fun i j => raw10114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10114step0 raw10114; decide +kernel
      have hl : raw10114step0Labels = raw10114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10114 raw10114Labels permutation346 hz
    mixedMoment B raw10114step0 raw10114step0Labels = mixedMoment B raw10114step1 raw10114step1Labels := by
      have ha : raw10114step1 = (fun i j => raw10114step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10114step1 raw10114step0; decide +kernel
      have hl : raw10114step1Labels = raw10114step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10114step0 raw10114step0Labels permutation137 permutation5
    mixedMoment B raw10114step1 raw10114step1Labels = mixedMoment B raw10114step2 raw10114step2Labels := by
      have ha : raw10114step2 = raw10114step1 := by apply Matrix.ext; unfold raw10114step2 raw10114step1; decide +kernel
      have hl : raw10114step1Labels = labelEmbedding8 ∘ raw10114step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10114step1 raw10114step1Labels raw10114step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw10115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10115 raw10115Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw10115 raw10115Labels = mixedMoment B raw10115step0 raw10115step0Labels := by
      have hz : ∀ j, raw10115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10115step0 = (fun i j => raw10115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10115step0 raw10115; decide +kernel
      have hl : raw10115step0Labels = raw10115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10115 raw10115Labels permutation346 hz
    mixedMoment B raw10115step0 raw10115step0Labels = mixedMoment B raw10115step1 raw10115step1Labels := by
      have ha : raw10115step1 = (fun i j => raw10115step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10115step1 raw10115step0; decide +kernel
      have hl : raw10115step1Labels = raw10115step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10115step0 raw10115step0Labels permutation151 permutation3
    mixedMoment B raw10115step1 raw10115step1Labels = mixedMoment B raw10115step2 raw10115step2Labels := by
      have ha : raw10115step2 = -raw10115step1 := by apply Matrix.ext; change ∀ i j, raw10115step2 i j = -(raw10115step1 i j); unfold raw10115step2 raw10115step1; decide +kernel
      have hl : raw10115step2Labels = raw10115step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw10116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10116 raw10116Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw10116 raw10116Labels = mixedMoment B raw10116step0 raw10116step0Labels := by
      have ha : raw10116step0 = (fun i j => raw10116 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10116step0 raw10116; decide +kernel
      have hl : raw10116step0Labels = raw10116Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10116 raw10116Labels permutation676 permutation3
    mixedMoment B raw10116step0 raw10116step0Labels = mixedMoment B raw10116step1 raw10116step1Labels := by
      have ha : raw10116step1 = -raw10116step0 := by apply Matrix.ext; change ∀ i j, raw10116step1 i j = -(raw10116step0 i j); unfold raw10116step1 raw10116step0; decide +kernel
      have hl : raw10116step1Labels = raw10116step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw10117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10117step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10117 raw10117Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw10117 raw10117Labels = mixedMoment B raw10117step0 raw10117step0Labels := by
      have hz : ∀ j, raw10117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10117step0 = (fun i j => raw10117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10117step0 raw10117; decide +kernel
      have hl : raw10117step0Labels = raw10117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10117 raw10117Labels permutation346 hz
    mixedMoment B raw10117step0 raw10117step0Labels = mixedMoment B raw10117step1 raw10117step1Labels := by
      have ha : raw10117step1 = (fun i j => raw10117step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10117step1 raw10117step0; decide +kernel
      have hl : raw10117step1Labels = raw10117step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10117step0 raw10117step0Labels permutation149 permutation3
    mixedMoment B raw10117step1 raw10117step1Labels = mixedMoment B raw10117step2 raw10117step2Labels := by
      have ha : raw10117step2 = -raw10117step1 := by apply Matrix.ext; change ∀ i j, raw10117step2 i j = -(raw10117step1 i j); unfold raw10117step2 raw10117step1; decide +kernel
      have hl : raw10117step2Labels = raw10117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw10118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw10118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw10118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10118 raw10118Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw10118 raw10118Labels = mixedMoment B raw10118step0 raw10118step0Labels := by
      have hz : ∀ j, raw10118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10118step0 = (fun i j => raw10118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10118step0 raw10118; decide +kernel
      have hl : raw10118step0Labels = raw10118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10118 raw10118Labels permutation346 hz
    mixedMoment B raw10118step0 raw10118step0Labels = mixedMoment B raw10118step1 raw10118step1Labels := by
      have ha : raw10118step1 = (fun i j => raw10118step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10118step1 raw10118step0; decide +kernel
      have hl : raw10118step1Labels = raw10118step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10118step0 raw10118step0Labels permutation137 permutation3
    mixedMoment B raw10118step1 raw10118step1Labels = mixedMoment B raw10118step2 raw10118step2Labels := by
      have ha : raw10118step2 = -raw10118step1 := by apply Matrix.ext; change ∀ i j, raw10118step2 i j = -(raw10118step1 i j); unfold raw10118step2 raw10118step1; decide +kernel
      have hl : raw10118step2Labels = raw10118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw10119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw10119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10119 raw10119Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw10119 raw10119Labels = mixedMoment B raw10119step0 raw10119step0Labels := by
      have hz : ∀ j, raw10119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10119step0 = (fun i j => raw10119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10119step0 raw10119; decide +kernel
      have hl : raw10119step0Labels = raw10119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10119 raw10119Labels permutation346 hz
    mixedMoment B raw10119step0 raw10119step0Labels = mixedMoment B raw10119step1 raw10119step1Labels := by
      have ha : raw10119step1 = (fun i j => raw10119step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10119step1 raw10119step0; decide +kernel
      have hl : raw10119step1Labels = raw10119step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10119step0 raw10119step0Labels permutation38 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw10120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10120 raw10120Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw10120 raw10120Labels = mixedMoment B raw10120step0 raw10120step0Labels := by
      have hz : ∀ j, raw10120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10120step0 = (fun i j => raw10120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10120step0 raw10120; decide +kernel
      have hl : raw10120step0Labels = raw10120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10120 raw10120Labels permutation346 hz
    mixedMoment B raw10120step0 raw10120step0Labels = mixedMoment B raw10120step1 raw10120step1Labels := by
      have ha : raw10120step1 = (fun i j => raw10120step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10120step1 raw10120step0; decide +kernel
      have hl : raw10120step1Labels = raw10120step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10120step0 raw10120step0Labels permutation40 permutation3
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw10121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10121 raw10121Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw10121 raw10121Labels = mixedMoment B raw10121step0 raw10121step0Labels := by
      have ha : raw10121step0 = (fun i j => raw10121 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10121step0 raw10121; decide +kernel
      have hl : raw10121step0Labels = raw10121Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10121 raw10121Labels permutation184 permutation3
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw10122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10122 raw10122Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw10122 raw10122Labels = mixedMoment B raw10122step0 raw10122step0Labels := by
      have hz : ∀ j, raw10122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10122step0 = (fun i j => raw10122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10122step0 raw10122; decide +kernel
      have hl : raw10122step0Labels = raw10122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10122 raw10122Labels permutation346 hz
    mixedMoment B raw10122step0 raw10122step0Labels = mixedMoment B raw10122step1 raw10122step1Labels := by
      have ha : raw10122step1 = (fun i j => raw10122step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10122step1 raw10122step0; decide +kernel
      have hl : raw10122step1Labels = raw10122step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10122step0 raw10122step0Labels permutation40 permutation3
    _ = mixedMoment B node2400 node2400Labels := by rfl

def raw10123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10123 raw10123Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw10123 raw10123Labels = mixedMoment B raw10123step0 raw10123step0Labels := by
      have hz : ∀ j, raw10123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10123step0 = (fun i j => raw10123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10123step0 raw10123; decide +kernel
      have hl : raw10123step0Labels = raw10123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10123 raw10123Labels permutation346 hz
    mixedMoment B raw10123step0 raw10123step0Labels = mixedMoment B raw10123step1 raw10123step1Labels := by
      have ha : raw10123step1 = (fun i j => raw10123step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10123step1 raw10123step0; decide +kernel
      have hl : raw10123step1Labels = raw10123step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10123step0 raw10123step0Labels permutation40 permutation3
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw10124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10124step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10124 raw10124Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw10124 raw10124Labels = mixedMoment B raw10124step0 raw10124step0Labels := by
      have hz : ∀ j, raw10124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10124step0 = (fun i j => raw10124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10124step0 raw10124; decide +kernel
      have hl : raw10124step0Labels = raw10124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10124 raw10124Labels permutation346 hz
    mixedMoment B raw10124step0 raw10124step0Labels = mixedMoment B raw10124step1 raw10124step1Labels := by
      have ha : raw10124step1 = (fun i j => raw10124step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10124step1 raw10124step0; decide +kernel
      have hl : raw10124step1Labels = raw10124step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10124step0 raw10124step0Labels permutation41 permutation3
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw10125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10125 raw10125Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw10125 raw10125Labels = mixedMoment B raw10125step0 raw10125step0Labels := by
      have ha : raw10125step0 = (fun i j => raw10125 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10125step0 raw10125; decide +kernel
      have hl : raw10125step0Labels = raw10125Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10125 raw10125Labels permutation202 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

def raw10126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10126 raw10126Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw10126 raw10126Labels = mixedMoment B raw10126step0 raw10126step0Labels := by
      have ha : raw10126step0 = (fun i j => raw10126 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10126step0 raw10126; decide +kernel
      have hl : raw10126step0Labels = raw10126Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10126 raw10126Labels permutation160 permutation3
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw10127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10127 raw10127Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw10127 raw10127Labels = mixedMoment B raw10127step0 raw10127step0Labels := by
      have ha : raw10127step0 = (fun i j => raw10127 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10127step0 raw10127; decide +kernel
      have hl : raw10127step0Labels = raw10127Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10127 raw10127Labels permutation202 permutation3
    _ = mixedMoment B node2382 node2382Labels := by rfl

def raw10128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10128 raw10128Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw10128 raw10128Labels = mixedMoment B raw10128step0 raw10128step0Labels := by
      have ha : raw10128step0 = (fun i j => raw10128 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10128step0 raw10128; decide +kernel
      have hl : raw10128step0Labels = raw10128Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10128 raw10128Labels permutation212 permutation3
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw10129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10129 raw10129Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw10129 raw10129Labels = mixedMoment B raw10129step0 raw10129step0Labels := by
      have ha : raw10129step0 = (fun i j => raw10129 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10129step0 raw10129; decide +kernel
      have hl : raw10129step0Labels = raw10129Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10129 raw10129Labels permutation202 permutation3
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw10130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10130Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10130step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10130 raw10130Labels = mixedMoment B node1040 node1040Labels := by
  calc
    mixedMoment B raw10130 raw10130Labels = mixedMoment B raw10130step0 raw10130step0Labels := by
      have hz : ∀ j, raw10130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10130step0 = (fun i j => raw10130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10130step0 raw10130; decide +kernel
      have hl : raw10130step0Labels = raw10130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10130 raw10130Labels permutation346 hz
    mixedMoment B raw10130step0 raw10130step0Labels = mixedMoment B raw10130step1 raw10130step1Labels := by
      have ha : raw10130step1 = (fun i j => raw10130step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10130step1 raw10130step0; decide +kernel
      have hl : raw10130step1Labels = raw10130step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10130step0 raw10130step0Labels permutation32 permutation3
    _ = mixedMoment B node1040 node1040Labels := by rfl

def raw10131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10131Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10131step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10131step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10131 raw10131Labels = mixedMoment B node2594 node2594Labels := by
  calc
    mixedMoment B raw10131 raw10131Labels = mixedMoment B raw10131step0 raw10131step0Labels := by
      have hz : ∀ j, raw10131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10131step0 = (fun i j => raw10131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10131step0 raw10131; decide +kernel
      have hl : raw10131step0Labels = raw10131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10131 raw10131Labels permutation346 hz
    mixedMoment B raw10131step0 raw10131step0Labels = mixedMoment B raw10131step1 raw10131step1Labels := by
      have ha : raw10131step1 = (fun i j => raw10131step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10131step1 raw10131step0; decide +kernel
      have hl : raw10131step1Labels = raw10131step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10131step0 raw10131step0Labels permutation32 permutation3
    _ = mixedMoment B node2594 node2594Labels := by rfl

def raw10132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10132Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10132 raw10132Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw10132 raw10132Labels = mixedMoment B raw10132step0 raw10132step0Labels := by
      have ha : raw10132step0 = (fun i j => raw10132 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10132step0 raw10132; decide +kernel
      have hl : raw10132step0Labels = raw10132Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10132 raw10132Labels permutation176 permutation3
    _ = mixedMoment B node2479 node2479Labels := by rfl

def raw10133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10133Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10133step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10133 raw10133Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10133 raw10133Labels = mixedMoment B raw10133step0 raw10133step0Labels := by
      have hz : ∀ j, raw10133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10133step0 = (fun i j => raw10133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10133step0 raw10133; decide +kernel
      have hl : raw10133step0Labels = raw10133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10133 raw10133Labels permutation346 hz
    mixedMoment B raw10133step0 raw10133step0Labels = mixedMoment B raw10133step1 raw10133step1Labels := by
      have ha : raw10133step1 = (fun i j => raw10133step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10133step1 raw10133step0; decide +kernel
      have hl : raw10133step1Labels = raw10133step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10133step0 raw10133step0Labels permutation44 permutation3
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw10134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10134Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10134step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10134 raw10134Labels = mixedMoment B node2766 node2766Labels := by
  calc
    mixedMoment B raw10134 raw10134Labels = mixedMoment B raw10134step0 raw10134step0Labels := by
      have hz : ∀ j, raw10134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10134step0 = (fun i j => raw10134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10134step0 raw10134; decide +kernel
      have hl : raw10134step0Labels = raw10134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10134 raw10134Labels permutation346 hz
    mixedMoment B raw10134step0 raw10134step0Labels = mixedMoment B raw10134step1 raw10134step1Labels := by
      have ha : raw10134step1 = (fun i j => raw10134step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10134step1 raw10134step0; decide +kernel
      have hl : raw10134step1Labels = raw10134step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10134step0 raw10134step0Labels permutation32 permutation3
    _ = mixedMoment B node2766 node2766Labels := by rfl

def raw10135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10135Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10135step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10135step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10135 raw10135Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw10135 raw10135Labels = mixedMoment B raw10135step0 raw10135step0Labels := by
      have hz : ∀ j, raw10135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10135step0 = (fun i j => raw10135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10135step0 raw10135; decide +kernel
      have hl : raw10135step0Labels = raw10135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10135 raw10135Labels permutation346 hz
    mixedMoment B raw10135step0 raw10135step0Labels = mixedMoment B raw10135step1 raw10135step1Labels := by
      have ha : raw10135step1 = (fun i j => raw10135step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10135step1 raw10135step0; decide +kernel
      have hl : raw10135step1Labels = raw10135step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10135step0 raw10135step0Labels permutation38 permutation3
    _ = mixedMoment B node985 node985Labels := by rfl

def raw10136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10136Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10136step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10136 raw10136Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw10136 raw10136Labels = mixedMoment B raw10136step0 raw10136step0Labels := by
      have hz : ∀ j, raw10136 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10136step0 = (fun i j => raw10136 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10136step0 raw10136; decide +kernel
      have hl : raw10136step0Labels = raw10136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10136 raw10136Labels permutation346 hz
    mixedMoment B raw10136step0 raw10136step0Labels = mixedMoment B raw10136step1 raw10136step1Labels := by
      have ha : raw10136step1 = (fun i j => raw10136step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10136step1 raw10136step0; decide +kernel
      have hl : raw10136step1Labels = raw10136step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10136step0 raw10136step0Labels permutation32 permutation3
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw10137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10137Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10137 raw10137Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw10137 raw10137Labels = mixedMoment B raw10137step0 raw10137step0Labels := by
      have ha : raw10137step0 = (fun i j => raw10137 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10137step0 raw10137; decide +kernel
      have hl : raw10137step0Labels = raw10137Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10137 raw10137Labels permutation182 permutation3
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw10138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10138step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10138 raw10138Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw10138 raw10138Labels = mixedMoment B raw10138step0 raw10138step0Labels := by
      have hz : ∀ j, raw10138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10138step0 = (fun i j => raw10138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10138step0 raw10138; decide +kernel
      have hl : raw10138step0Labels = raw10138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10138 raw10138Labels permutation346 hz
    mixedMoment B raw10138step0 raw10138step0Labels = mixedMoment B raw10138step1 raw10138step1Labels := by
      have ha : raw10138step1 = (fun i j => raw10138step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10138step1 raw10138step0; decide +kernel
      have hl : raw10138step1Labels = raw10138step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10138step0 raw10138step0Labels permutation38 permutation3
    _ = mixedMoment B node2388 node2388Labels := by rfl

def raw10139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw10139Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw10139step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10139step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10139 raw10139Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw10139 raw10139Labels = mixedMoment B raw10139step0 raw10139step0Labels := by
      have hz : ∀ j, raw10139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10139step0 = (fun i j => raw10139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10139step0 raw10139; decide +kernel
      have hl : raw10139step0Labels = raw10139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10139 raw10139Labels permutation346 hz
    mixedMoment B raw10139step0 raw10139step0Labels = mixedMoment B raw10139step1 raw10139step1Labels := by
      have ha : raw10139step1 = (fun i j => raw10139step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10139step1 raw10139step0; decide +kernel
      have hl : raw10139step1Labels = raw10139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10139step0 raw10139step0Labels permutation39 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw10140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10140step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw10140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10140 raw10140Labels = mixedMoment B node979 node979Labels := by
  calc
    mixedMoment B raw10140 raw10140Labels = mixedMoment B raw10140step0 raw10140step0Labels := by
      have hz : ∀ j, raw10140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10140step0 = (fun i j => raw10140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10140step0 raw10140; decide +kernel
      have hl : raw10140step0Labels = raw10140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10140 raw10140Labels permutation346 hz
    mixedMoment B raw10140step0 raw10140step0Labels = mixedMoment B raw10140step1 raw10140step1Labels := by
      have ha : raw10140step1 = (fun i j => raw10140step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10140step1 raw10140step0; decide +kernel
      have hl : raw10140step1Labels = raw10140step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10140step0 raw10140step0Labels permutation38 permutation3
    _ = mixedMoment B node979 node979Labels := by rfl

def raw10141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10141step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10141 raw10141Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw10141 raw10141Labels = mixedMoment B raw10141step0 raw10141step0Labels := by
      have hz : ∀ j, raw10141 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10141step0 = (fun i j => raw10141 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10141step0 raw10141; decide +kernel
      have hl : raw10141step0Labels = raw10141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10141 raw10141Labels permutation346 hz
    mixedMoment B raw10141step0 raw10141step0Labels = mixedMoment B raw10141step1 raw10141step1Labels := by
      have ha : raw10141step1 = (fun i j => raw10141step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10141step1 raw10141step0; decide +kernel
      have hl : raw10141step1Labels = raw10141step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10141step0 raw10141step0Labels permutation151 permutation3
    mixedMoment B raw10141step1 raw10141step1Labels = mixedMoment B raw10141step2 raw10141step2Labels := by
      have ha : raw10141step2 = -raw10141step1 := by apply Matrix.ext; change ∀ i j, raw10141step2 i j = -(raw10141step1 i j); unfold raw10141step2 raw10141step1; decide +kernel
      have hl : raw10141step2Labels = raw10141step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw10142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw10142step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10142step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw10142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10142 raw10142Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw10142 raw10142Labels = mixedMoment B raw10142step0 raw10142step0Labels := by
      have ha : raw10142step0 = (fun i j => raw10142 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10142step0 raw10142; decide +kernel
      have hl : raw10142step0Labels = raw10142Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10142 raw10142Labels permutation676 permutation3
    mixedMoment B raw10142step0 raw10142step0Labels = mixedMoment B raw10142step1 raw10142step1Labels := by
      have ha : raw10142step1 = -raw10142step0 := by apply Matrix.ext; change ∀ i j, raw10142step1 i j = -(raw10142step0 i j); unfold raw10142step1 raw10142step0; decide +kernel
      have hl : raw10142step1Labels = raw10142step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1987 node1987Labels := by rfl

def raw10143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10143step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw10143step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw10143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10143 raw10143Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw10143 raw10143Labels = mixedMoment B raw10143step0 raw10143step0Labels := by
      have hz : ∀ j, raw10143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10143step0 = (fun i j => raw10143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10143step0 raw10143; decide +kernel
      have hl : raw10143step0Labels = raw10143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10143 raw10143Labels permutation346 hz
    mixedMoment B raw10143step0 raw10143step0Labels = mixedMoment B raw10143step1 raw10143step1Labels := by
      have ha : raw10143step1 = (fun i j => raw10143step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10143step1 raw10143step0; decide +kernel
      have hl : raw10143step1Labels = raw10143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10143step0 raw10143step0Labels permutation149 permutation3
    mixedMoment B raw10143step1 raw10143step1Labels = mixedMoment B raw10143step2 raw10143step2Labels := by
      have ha : raw10143step2 = -raw10143step1 := by apply Matrix.ext; change ∀ i j, raw10143step2 i j = -(raw10143step1 i j); unfold raw10143step2 raw10143step1; decide +kernel
      have hl : raw10143step2Labels = raw10143step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2003 node2003Labels := by rfl

def raw10144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw10144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw10144step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw10144step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw10144step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10144 raw10144Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw10144 raw10144Labels = mixedMoment B raw10144step0 raw10144step0Labels := by
      have hz : ∀ j, raw10144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10144step0 = (fun i j => raw10144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10144step0 raw10144; decide +kernel
      have hl : raw10144step0Labels = raw10144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10144 raw10144Labels permutation346 hz
    mixedMoment B raw10144step0 raw10144step0Labels = mixedMoment B raw10144step1 raw10144step1Labels := by
      have ha : raw10144step1 = (fun i j => raw10144step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10144step1 raw10144step0; decide +kernel
      have hl : raw10144step1Labels = raw10144step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10144step0 raw10144step0Labels permutation137 permutation3
    mixedMoment B raw10144step1 raw10144step1Labels = mixedMoment B raw10144step2 raw10144step2Labels := by
      have ha : raw10144step2 = -raw10144step1 := by apply Matrix.ext; change ∀ i j, raw10144step2 i j = -(raw10144step1 i j); unfold raw10144step2 raw10144step1; decide +kernel
      have hl : raw10144step2Labels = raw10144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw10145 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10145step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10145step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10145step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10145 raw10145Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw10145 raw10145Labels = mixedMoment B raw10145step0 raw10145step0Labels := by
      have hz : ∀ j, raw10145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10145step0 = (fun i j => raw10145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10145step0 raw10145; decide +kernel
      have hl : raw10145step0Labels = raw10145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10145 raw10145Labels permutation346 hz
    mixedMoment B raw10145step0 raw10145step0Labels = mixedMoment B raw10145step1 raw10145step1Labels := by
      have hz : ∀ j, raw10145step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10145step1 = (fun i j => raw10145step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10145step1 raw10145step0; decide +kernel
      have hl : raw10145step1Labels = raw10145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10145step0 raw10145step0Labels permutation56 hz
    mixedMoment B raw10145step1 raw10145step1Labels = mixedMoment B raw10145step2 raw10145step2Labels := by
      have ha : raw10145step2 = (fun i j => raw10145step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10145step2 raw10145step1; decide +kernel
      have hl : raw10145step2Labels = raw10145step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10145step1 raw10145step1Labels permutation8 permutation7
    mixedMoment B raw10145step2 raw10145step2Labels = mixedMoment B raw10145step3 raw10145step3Labels := by
      have ha : raw10145step3 = raw10145step2 := by apply Matrix.ext; unfold raw10145step3 raw10145step2; decide +kernel
      have hl : raw10145step2Labels = labelEmbedding10 ∘ raw10145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10145step2 raw10145step2Labels raw10145step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw10146 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10146step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10146 raw10146Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw10146 raw10146Labels = mixedMoment B raw10146step0 raw10146step0Labels := by
      have ha : raw10146step0 = (fun i j => raw10146 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10146step0 raw10146; decide +kernel
      have hl : raw10146step0Labels = raw10146Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10146 raw10146Labels permutation152 permutation7
    mixedMoment B raw10146step0 raw10146step0Labels = mixedMoment B raw10146step1 raw10146step1Labels := by
      have ha : raw10146step1 = raw10146step0 := by apply Matrix.ext; unfold raw10146step1 raw10146step0; decide +kernel
      have hl : raw10146step0Labels = labelEmbedding10 ∘ raw10146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10146step0 raw10146step0Labels raw10146step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw10147 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10147step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10147 raw10147Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw10147 raw10147Labels = mixedMoment B raw10147step0 raw10147step0Labels := by
      have hz : ∀ j, raw10147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10147step0 = (fun i j => raw10147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10147step0 raw10147; decide +kernel
      have hl : raw10147step0Labels = raw10147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10147 raw10147Labels permutation346 hz
    mixedMoment B raw10147step0 raw10147step0Labels = mixedMoment B raw10147step1 raw10147step1Labels := by
      have ha : raw10147step1 = (fun i j => raw10147step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10147step1 raw10147step0; decide +kernel
      have hl : raw10147step1Labels = raw10147step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10147step0 raw10147step0Labels permutation32 permutation7
    mixedMoment B raw10147step1 raw10147step1Labels = mixedMoment B raw10147step2 raw10147step2Labels := by
      have ha : raw10147step2 = raw10147step1 := by apply Matrix.ext; unfold raw10147step2 raw10147step1; decide +kernel
      have hl : raw10147step1Labels = labelEmbedding10 ∘ raw10147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10147step1 raw10147step1Labels raw10147step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw10148 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10148step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10148step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10148step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10148step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10148 raw10148Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw10148 raw10148Labels = mixedMoment B raw10148step0 raw10148step0Labels := by
      have hz : ∀ j, raw10148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10148step0 = (fun i j => raw10148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10148step0 raw10148; decide +kernel
      have hl : raw10148step0Labels = raw10148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10148 raw10148Labels permutation346 hz
    mixedMoment B raw10148step0 raw10148step0Labels = mixedMoment B raw10148step1 raw10148step1Labels := by
      have ha : raw10148step1 = (fun i j => raw10148step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10148step1 raw10148step0; decide +kernel
      have hl : raw10148step1Labels = raw10148step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10148step0 raw10148step0Labels permutation40 permutation4
    mixedMoment B raw10148step1 raw10148step1Labels = mixedMoment B raw10148step2 raw10148step2Labels := by
      have ha : raw10148step2 = -raw10148step1 := by apply Matrix.ext; change ∀ i j, raw10148step2 i j = -(raw10148step1 i j); unfold raw10148step2 raw10148step1; decide +kernel
      have hl : raw10148step2Labels = raw10148step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10148step2 raw10148step2Labels = mixedMoment B raw10148step3 raw10148step3Labels := by
      have ha : raw10148step3 = raw10148step2 := by apply Matrix.ext; unfold raw10148step3 raw10148step2; decide +kernel
      have hl : raw10148step2Labels = labelEmbedding7 ∘ raw10148step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10148step2 raw10148step2Labels raw10148step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw10149 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10149step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10149 raw10149Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw10149 raw10149Labels = mixedMoment B raw10149step0 raw10149step0Labels := by
      have ha : raw10149step0 = (fun i j => raw10149 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10149step0 raw10149; decide +kernel
      have hl : raw10149step0Labels = raw10149Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10149 raw10149Labels permutation182 permutation6
    mixedMoment B raw10149step0 raw10149step0Labels = mixedMoment B raw10149step1 raw10149step1Labels := by
      have ha : raw10149step1 = raw10149step0 := by apply Matrix.ext; unfold raw10149step1 raw10149step0; decide +kernel
      have hl : raw10149step0Labels = labelEmbedding9 ∘ raw10149step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10149step0 raw10149step0Labels raw10149step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw10150 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10150step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10150 raw10150Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw10150 raw10150Labels = mixedMoment B raw10150step0 raw10150step0Labels := by
      have hz : ∀ j, raw10150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10150step0 = (fun i j => raw10150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10150step0 raw10150; decide +kernel
      have hl : raw10150step0Labels = raw10150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10150 raw10150Labels permutation346 hz
    mixedMoment B raw10150step0 raw10150step0Labels = mixedMoment B raw10150step1 raw10150step1Labels := by
      have ha : raw10150step1 = (fun i j => raw10150step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10150step1 raw10150step0; decide +kernel
      have hl : raw10150step1Labels = raw10150step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10150step0 raw10150step0Labels permutation38 permutation6
    mixedMoment B raw10150step1 raw10150step1Labels = mixedMoment B raw10150step2 raw10150step2Labels := by
      have ha : raw10150step2 = raw10150step1 := by apply Matrix.ext; unfold raw10150step2 raw10150step1; decide +kernel
      have hl : raw10150step1Labels = labelEmbedding9 ∘ raw10150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10150step1 raw10150step1Labels raw10150step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw10151 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw10151step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10151step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10151step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10151step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10151 raw10151Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw10151 raw10151Labels = mixedMoment B raw10151step0 raw10151step0Labels := by
      have ha : raw10151step0 = (fun i j => raw10151 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10151step0 raw10151; decide +kernel
      have hl : raw10151step0Labels = raw10151Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10151 raw10151Labels permutation212 permutation4
    mixedMoment B raw10151step0 raw10151step0Labels = mixedMoment B raw10151step1 raw10151step1Labels := by
      have ha : raw10151step1 = -raw10151step0 := by apply Matrix.ext; change ∀ i j, raw10151step1 i j = -(raw10151step0 i j); unfold raw10151step1 raw10151step0; decide +kernel
      have hl : raw10151step1Labels = raw10151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10151step1 raw10151step1Labels = mixedMoment B raw10151step2 raw10151step2Labels := by
      have ha : raw10151step2 = raw10151step1 := by apply Matrix.ext; unfold raw10151step2 raw10151step1; decide +kernel
      have hl : raw10151step1Labels = labelEmbedding7 ∘ raw10151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10151step1 raw10151step1Labels raw10151step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw10152 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10152step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10152 raw10152Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw10152 raw10152Labels = mixedMoment B raw10152step0 raw10152step0Labels := by
      have hz : ∀ j, raw10152 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10152step0 = (fun i j => raw10152 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10152step0 raw10152; decide +kernel
      have hl : raw10152step0Labels = raw10152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10152 raw10152Labels permutation265 hz
    mixedMoment B raw10152step0 raw10152step0Labels = mixedMoment B raw10152step1 raw10152step1Labels := by
      have ha : raw10152step1 = (fun i j => raw10152step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10152step1 raw10152step0; decide +kernel
      have hl : raw10152step1Labels = raw10152step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10152step0 raw10152step0Labels permutation38 permutation6
    mixedMoment B raw10152step1 raw10152step1Labels = mixedMoment B raw10152step2 raw10152step2Labels := by
      have ha : raw10152step2 = raw10152step1 := by apply Matrix.ext; unfold raw10152step2 raw10152step1; decide +kernel
      have hl : raw10152step1Labels = labelEmbedding9 ∘ raw10152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10152step1 raw10152step1Labels raw10152step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw10153 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10153step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10153 raw10153Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw10153 raw10153Labels = mixedMoment B raw10153step0 raw10153step0Labels := by
      have ha : raw10153step0 = (fun i j => raw10153 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10153step0 raw10153; decide +kernel
      have hl : raw10153step0Labels = raw10153Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10153 raw10153Labels permutation200 permutation6
    mixedMoment B raw10153step0 raw10153step0Labels = mixedMoment B raw10153step1 raw10153step1Labels := by
      have ha : raw10153step1 = raw10153step0 := by apply Matrix.ext; unfold raw10153step1 raw10153step0; decide +kernel
      have hl : raw10153step0Labels = labelEmbedding9 ∘ raw10153step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10153step0 raw10153step0Labels raw10153step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw10154 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10154step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10154step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10154step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10154 raw10154Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw10154 raw10154Labels = mixedMoment B raw10154step0 raw10154step0Labels := by
      have hz : ∀ j, raw10154 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10154step0 = (fun i j => raw10154 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10154step0 raw10154; decide +kernel
      have hl : raw10154step0Labels = raw10154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10154 raw10154Labels permutation434 hz
    mixedMoment B raw10154step0 raw10154step0Labels = mixedMoment B raw10154step1 raw10154step1Labels := by
      have hz : ∀ j, raw10154step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10154step1 = (fun i j => raw10154step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10154step1 raw10154step0; decide +kernel
      have hl : raw10154step1Labels = raw10154step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10154step0 raw10154step0Labels permutation80 hz
    mixedMoment B raw10154step1 raw10154step1Labels = mixedMoment B raw10154step2 raw10154step2Labels := by
      have ha : raw10154step2 = (fun i j => raw10154step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10154step2 raw10154step1; decide +kernel
      have hl : raw10154step2Labels = raw10154step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10154step1 raw10154step1Labels permutation8 permutation6
    mixedMoment B raw10154step2 raw10154step2Labels = mixedMoment B raw10154step3 raw10154step3Labels := by
      have ha : raw10154step3 = raw10154step2 := by apply Matrix.ext; unfold raw10154step3 raw10154step2; decide +kernel
      have hl : raw10154step2Labels = labelEmbedding9 ∘ raw10154step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10154step2 raw10154step2Labels raw10154step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw10155 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10155step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw10155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10155 raw10155Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw10155 raw10155Labels = mixedMoment B raw10155step0 raw10155step0Labels := by
      have hz : ∀ j, raw10155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10155step0 = (fun i j => raw10155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10155step0 raw10155; decide +kernel
      have hl : raw10155step0Labels = raw10155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10155 raw10155Labels permutation346 hz
    mixedMoment B raw10155step0 raw10155step0Labels = mixedMoment B raw10155step1 raw10155step1Labels := by
      have ha : raw10155step1 = (fun i j => raw10155step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10155step1 raw10155step0; decide +kernel
      have hl : raw10155step1Labels = raw10155step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10155step0 raw10155step0Labels permutation38 permutation6
    mixedMoment B raw10155step1 raw10155step1Labels = mixedMoment B raw10155step2 raw10155step2Labels := by
      have ha : raw10155step2 = raw10155step1 := by apply Matrix.ext; unfold raw10155step2 raw10155step1; decide +kernel
      have hl : raw10155step1Labels = labelEmbedding9 ∘ raw10155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10155step1 raw10155step1Labels raw10155step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw10156 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10156step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10156step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10156step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10156step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10156 raw10156Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw10156 raw10156Labels = mixedMoment B raw10156step0 raw10156step0Labels := by
      have hz : ∀ j, raw10156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10156step0 = (fun i j => raw10156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10156step0 raw10156; decide +kernel
      have hl : raw10156step0Labels = raw10156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10156 raw10156Labels permutation346 hz
    mixedMoment B raw10156step0 raw10156step0Labels = mixedMoment B raw10156step1 raw10156step1Labels := by
      have ha : raw10156step1 = (fun i j => raw10156step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10156step1 raw10156step0; decide +kernel
      have hl : raw10156step1Labels = raw10156step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10156step0 raw10156step0Labels permutation40 permutation4
    mixedMoment B raw10156step1 raw10156step1Labels = mixedMoment B raw10156step2 raw10156step2Labels := by
      have ha : raw10156step2 = -raw10156step1 := by apply Matrix.ext; change ∀ i j, raw10156step2 i j = -(raw10156step1 i j); unfold raw10156step2 raw10156step1; decide +kernel
      have hl : raw10156step2Labels = raw10156step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10156step2 raw10156step2Labels = mixedMoment B raw10156step3 raw10156step3Labels := by
      have ha : raw10156step3 = raw10156step2 := by apply Matrix.ext; unfold raw10156step3 raw10156step2; decide +kernel
      have hl : raw10156step2Labels = labelEmbedding7 ∘ raw10156step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10156step2 raw10156step2Labels raw10156step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw10157 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10157step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10157step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10157step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10157step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10157step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10157 raw10157Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw10157 raw10157Labels = mixedMoment B raw10157step0 raw10157step0Labels := by
      have hz : ∀ j, raw10157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10157step0 = (fun i j => raw10157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10157step0 raw10157; decide +kernel
      have hl : raw10157step0Labels = raw10157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10157 raw10157Labels permutation346 hz
    mixedMoment B raw10157step0 raw10157step0Labels = mixedMoment B raw10157step1 raw10157step1Labels := by
      have hz : ∀ j, raw10157step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10157step1 = (fun i j => raw10157step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10157step1 raw10157step0; decide +kernel
      have hl : raw10157step1Labels = raw10157step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10157step0 raw10157step0Labels permutation56 hz
    mixedMoment B raw10157step1 raw10157step1Labels = mixedMoment B raw10157step2 raw10157step2Labels := by
      have ha : raw10157step2 = (fun i j => raw10157step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10157step2 raw10157step1; decide +kernel
      have hl : raw10157step2Labels = raw10157step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10157step1 raw10157step1Labels permutation31 permutation4
    mixedMoment B raw10157step2 raw10157step2Labels = mixedMoment B raw10157step3 raw10157step3Labels := by
      have ha : raw10157step3 = raw10157step2 := by apply Matrix.ext; unfold raw10157step3 raw10157step2; decide +kernel
      have hl : raw10157step2Labels = labelEmbedding7 ∘ raw10157step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10157step2 raw10157step2Labels raw10157step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw10158 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10158step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10158 raw10158Labels = mixedMoment B node5133 node5133Labels := by
  calc
    mixedMoment B raw10158 raw10158Labels = mixedMoment B raw10158step0 raw10158step0Labels := by
      have ha : raw10158step0 = (fun i j => raw10158 (permutation620 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10158step0 raw10158; decide +kernel
      have hl : raw10158step0Labels = raw10158Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10158 raw10158Labels permutation620 permutation4
    mixedMoment B raw10158step0 raw10158step0Labels = mixedMoment B raw10158step1 raw10158step1Labels := by
      have ha : raw10158step1 = raw10158step0 := by apply Matrix.ext; unfold raw10158step1 raw10158step0; decide +kernel
      have hl : raw10158step0Labels = labelEmbedding7 ∘ raw10158step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10158step0 raw10158step0Labels raw10158step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5133 node5133Labels := by rfl

def raw10159 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10159step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw10159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw10159step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10159 raw10159Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw10159 raw10159Labels = mixedMoment B raw10159step0 raw10159step0Labels := by
      have hz : ∀ j, raw10159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10159step0 = (fun i j => raw10159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10159step0 raw10159; decide +kernel
      have hl : raw10159step0Labels = raw10159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10159 raw10159Labels permutation346 hz
    mixedMoment B raw10159step0 raw10159step0Labels = mixedMoment B raw10159step1 raw10159step1Labels := by
      have ha : raw10159step1 = (fun i j => raw10159step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10159step1 raw10159step0; decide +kernel
      have hl : raw10159step1Labels = raw10159step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10159step0 raw10159step0Labels permutation139 permutation4
    mixedMoment B raw10159step1 raw10159step1Labels = mixedMoment B raw10159step2 raw10159step2Labels := by
      have ha : raw10159step2 = raw10159step1 := by apply Matrix.ext; unfold raw10159step2 raw10159step1; decide +kernel
      have hl : raw10159step1Labels = labelEmbedding7 ∘ raw10159step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10159step1 raw10159step1Labels raw10159step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw10160 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10160step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10160step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10160 raw10160Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw10160 raw10160Labels = mixedMoment B raw10160step0 raw10160step0Labels := by
      have hz : ∀ j, raw10160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10160step0 = (fun i j => raw10160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10160step0 raw10160; decide +kernel
      have hl : raw10160step0Labels = raw10160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10160 raw10160Labels permutation346 hz
    mixedMoment B raw10160step0 raw10160step0Labels = mixedMoment B raw10160step1 raw10160step1Labels := by
      have hz : ∀ j, raw10160step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10160step1 = (fun i j => raw10160step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10160step1 raw10160step0; decide +kernel
      have hl : raw10160step1Labels = raw10160step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10160step0 raw10160step0Labels permutation56 hz
    mixedMoment B raw10160step1 raw10160step1Labels = mixedMoment B raw10160step2 raw10160step2Labels := by
      have ha : raw10160step2 = (fun i j => raw10160step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10160step2 raw10160step1; decide +kernel
      have hl : raw10160step2Labels = raw10160step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10160step1 raw10160step1Labels permutation8 permutation6
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw10161 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10161 raw10161Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw10161 raw10161Labels = mixedMoment B raw10161step0 raw10161step0Labels := by
      have ha : raw10161step0 = (fun i j => raw10161 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10161step0 raw10161; decide +kernel
      have hl : raw10161step0Labels = raw10161Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10161 raw10161Labels permutation182 permutation6
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw10162 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10162 raw10162Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw10162 raw10162Labels = mixedMoment B raw10162step0 raw10162step0Labels := by
      have hz : ∀ j, raw10162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10162step0 = (fun i j => raw10162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10162step0 raw10162; decide +kernel
      have hl : raw10162step0Labels = raw10162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10162 raw10162Labels permutation346 hz
    mixedMoment B raw10162step0 raw10162step0Labels = mixedMoment B raw10162step1 raw10162step1Labels := by
      have ha : raw10162step1 = (fun i j => raw10162step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10162step1 raw10162step0; decide +kernel
      have hl : raw10162step1Labels = raw10162step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10162step0 raw10162step0Labels permutation38 permutation6
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw10163 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10163 raw10163Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw10163 raw10163Labels = mixedMoment B raw10163step0 raw10163step0Labels := by
      have hz : ∀ j, raw10163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10163step0 = (fun i j => raw10163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10163step0 raw10163; decide +kernel
      have hl : raw10163step0Labels = raw10163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10163 raw10163Labels permutation346 hz
    mixedMoment B raw10163step0 raw10163step0Labels = mixedMoment B raw10163step1 raw10163step1Labels := by
      have ha : raw10163step1 = (fun i j => raw10163step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10163step1 raw10163step0; decide +kernel
      have hl : raw10163step1Labels = raw10163step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10163step0 raw10163step0Labels permutation38 permutation6
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw10164 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10164 raw10164Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw10164 raw10164Labels = mixedMoment B raw10164step0 raw10164step0Labels := by
      have ha : raw10164step0 = (fun i j => raw10164 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10164step0 raw10164; decide +kernel
      have hl : raw10164step0Labels = raw10164Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10164 raw10164Labels permutation182 permutation6
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw10165 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10165 raw10165Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw10165 raw10165Labels = mixedMoment B raw10165step0 raw10165step0Labels := by
      have hz : ∀ j, raw10165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10165step0 = (fun i j => raw10165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10165step0 raw10165; decide +kernel
      have hl : raw10165step0Labels = raw10165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10165 raw10165Labels permutation346 hz
    mixedMoment B raw10165step0 raw10165step0Labels = mixedMoment B raw10165step1 raw10165step1Labels := by
      have ha : raw10165step1 = (fun i j => raw10165step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10165step1 raw10165step0; decide +kernel
      have hl : raw10165step1Labels = raw10165step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10165step0 raw10165step0Labels permutation38 permutation6
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw10166 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10166 raw10166Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw10166 raw10166Labels = mixedMoment B raw10166step0 raw10166step0Labels := by
      have ha : raw10166step0 = (fun i j => raw10166 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10166step0 raw10166; decide +kernel
      have hl : raw10166step0Labels = raw10166Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10166 raw10166Labels permutation200 permutation6
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw10167 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10167 raw10167Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10167 raw10167Labels = mixedMoment B raw10167step0 raw10167step0Labels := by
      have hz : ∀ j, raw10167 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10167step0 = (fun i j => raw10167 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10167step0 raw10167; decide +kernel
      have hl : raw10167step0Labels = raw10167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10167 raw10167Labels permutation265 hz
    mixedMoment B raw10167step0 raw10167step0Labels = mixedMoment B raw10167step1 raw10167step1Labels := by
      have ha : raw10167step1 = (fun i j => raw10167step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10167step1 raw10167step0; decide +kernel
      have hl : raw10167step1Labels = raw10167step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10167step0 raw10167step0Labels permutation38 permutation6
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw10168 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10168 raw10168Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw10168 raw10168Labels = mixedMoment B raw10168step0 raw10168step0Labels := by
      have ha : raw10168step0 = (fun i j => raw10168 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10168step0 raw10168; decide +kernel
      have hl : raw10168step0Labels = raw10168Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10168 raw10168Labels permutation200 permutation6
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw10169 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10169step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10169step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10169 raw10169Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw10169 raw10169Labels = mixedMoment B raw10169step0 raw10169step0Labels := by
      have hz : ∀ j, raw10169 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10169step0 = (fun i j => raw10169 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10169step0 raw10169; decide +kernel
      have hl : raw10169step0Labels = raw10169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10169 raw10169Labels permutation434 hz
    mixedMoment B raw10169step0 raw10169step0Labels = mixedMoment B raw10169step1 raw10169step1Labels := by
      have hz : ∀ j, raw10169step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10169step1 = (fun i j => raw10169step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10169step1 raw10169step0; decide +kernel
      have hl : raw10169step1Labels = raw10169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10169step0 raw10169step0Labels permutation80 hz
    mixedMoment B raw10169step1 raw10169step1Labels = mixedMoment B raw10169step2 raw10169step2Labels := by
      have ha : raw10169step2 = (fun i j => raw10169step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10169step2 raw10169step1; decide +kernel
      have hl : raw10169step2Labels = raw10169step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10169step1 raw10169step1Labels permutation8 permutation6
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw10170 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10170 raw10170Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw10170 raw10170Labels = mixedMoment B raw10170step0 raw10170step0Labels := by
      have hz : ∀ j, raw10170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10170step0 = (fun i j => raw10170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10170step0 raw10170; decide +kernel
      have hl : raw10170step0Labels = raw10170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10170 raw10170Labels permutation346 hz
    mixedMoment B raw10170step0 raw10170step0Labels = mixedMoment B raw10170step1 raw10170step1Labels := by
      have ha : raw10170step1 = (fun i j => raw10170step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10170step1 raw10170step0; decide +kernel
      have hl : raw10170step1Labels = raw10170step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10170step0 raw10170step0Labels permutation38 permutation6
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw10171 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10171 raw10171Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw10171 raw10171Labels = mixedMoment B raw10171step0 raw10171step0Labels := by
      have hz : ∀ j, raw10171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10171step0 = (fun i j => raw10171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10171step0 raw10171; decide +kernel
      have hl : raw10171step0Labels = raw10171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10171 raw10171Labels permutation346 hz
    mixedMoment B raw10171step0 raw10171step0Labels = mixedMoment B raw10171step1 raw10171step1Labels := by
      have ha : raw10171step1 = (fun i j => raw10171step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10171step1 raw10171step0; decide +kernel
      have hl : raw10171step1Labels = raw10171step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10171step0 raw10171step0Labels permutation38 permutation6
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw10172 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10172step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw10172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10172 raw10172Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw10172 raw10172Labels = mixedMoment B raw10172step0 raw10172step0Labels := by
      have hz : ∀ j, raw10172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10172step0 = (fun i j => raw10172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10172step0 raw10172; decide +kernel
      have hl : raw10172step0Labels = raw10172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10172 raw10172Labels permutation346 hz
    mixedMoment B raw10172step0 raw10172step0Labels = mixedMoment B raw10172step1 raw10172step1Labels := by
      have hz : ∀ j, raw10172step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10172step1 = (fun i j => raw10172step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10172step1 raw10172step0; decide +kernel
      have hl : raw10172step1Labels = raw10172step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10172step0 raw10172step0Labels permutation56 hz
    mixedMoment B raw10172step1 raw10172step1Labels = mixedMoment B raw10172step2 raw10172step2Labels := by
      have ha : raw10172step2 = (fun i j => raw10172step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10172step2 raw10172step1; decide +kernel
      have hl : raw10172step2Labels = raw10172step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10172step1 raw10172step1Labels permutation8 permutation6
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw10173 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10173 raw10173Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw10173 raw10173Labels = mixedMoment B raw10173step0 raw10173step0Labels := by
      have ha : raw10173step0 = (fun i j => raw10173 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10173step0 raw10173; decide +kernel
      have hl : raw10173step0Labels = raw10173Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10173 raw10173Labels permutation182 permutation6
    _ = mixedMoment B node2693 node2693Labels := by rfl

def raw10174 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10174 raw10174Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw10174 raw10174Labels = mixedMoment B raw10174step0 raw10174step0Labels := by
      have hz : ∀ j, raw10174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10174step0 = (fun i j => raw10174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10174step0 raw10174; decide +kernel
      have hl : raw10174step0Labels = raw10174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10174 raw10174Labels permutation346 hz
    mixedMoment B raw10174step0 raw10174step0Labels = mixedMoment B raw10174step1 raw10174step1Labels := by
      have ha : raw10174step1 = (fun i j => raw10174step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10174step1 raw10174step0; decide +kernel
      have hl : raw10174step1Labels = raw10174step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10174step0 raw10174step0Labels permutation38 permutation6
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw10175 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10175step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10175step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10175step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10175step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10175 raw10175Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw10175 raw10175Labels = mixedMoment B raw10175step0 raw10175step0Labels := by
      have hz : ∀ j, raw10175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10175step0 = (fun i j => raw10175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10175step0 raw10175; decide +kernel
      have hl : raw10175step0Labels = raw10175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10175 raw10175Labels permutation346 hz
    mixedMoment B raw10175step0 raw10175step0Labels = mixedMoment B raw10175step1 raw10175step1Labels := by
      have hz : ∀ j, raw10175step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10175step1 = (fun i j => raw10175step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10175step1 raw10175step0; decide +kernel
      have hl : raw10175step1Labels = raw10175step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10175step0 raw10175step0Labels permutation56 hz
    mixedMoment B raw10175step1 raw10175step1Labels = mixedMoment B raw10175step2 raw10175step2Labels := by
      have ha : raw10175step2 = (fun i j => raw10175step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10175step2 raw10175step1; decide +kernel
      have hl : raw10175step2Labels = raw10175step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10175step1 raw10175step1Labels permutation8 permutation7
    mixedMoment B raw10175step2 raw10175step2Labels = mixedMoment B raw10175step3 raw10175step3Labels := by
      have ha : raw10175step3 = raw10175step2 := by apply Matrix.ext; unfold raw10175step3 raw10175step2; decide +kernel
      have hl : raw10175step2Labels = labelEmbedding1 ∘ raw10175step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10175step2 raw10175step2Labels raw10175step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw10176 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10176 raw10176Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw10176 raw10176Labels = mixedMoment B raw10176step0 raw10176step0Labels := by
      have ha : raw10176step0 = (fun i j => raw10176 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10176step0 raw10176; decide +kernel
      have hl : raw10176step0Labels = raw10176Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10176 raw10176Labels permutation152 permutation7
    mixedMoment B raw10176step0 raw10176step0Labels = mixedMoment B raw10176step1 raw10176step1Labels := by
      have ha : raw10176step1 = raw10176step0 := by apply Matrix.ext; unfold raw10176step1 raw10176step0; decide +kernel
      have hl : raw10176step0Labels = labelEmbedding1 ∘ raw10176step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10176step0 raw10176step0Labels raw10176step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw10177 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10177 raw10177Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw10177 raw10177Labels = mixedMoment B raw10177step0 raw10177step0Labels := by
      have hz : ∀ j, raw10177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10177step0 = (fun i j => raw10177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10177step0 raw10177; decide +kernel
      have hl : raw10177step0Labels = raw10177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10177 raw10177Labels permutation346 hz
    mixedMoment B raw10177step0 raw10177step0Labels = mixedMoment B raw10177step1 raw10177step1Labels := by
      have ha : raw10177step1 = (fun i j => raw10177step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10177step1 raw10177step0; decide +kernel
      have hl : raw10177step1Labels = raw10177step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10177step0 raw10177step0Labels permutation32 permutation7
    mixedMoment B raw10177step1 raw10177step1Labels = mixedMoment B raw10177step2 raw10177step2Labels := by
      have ha : raw10177step2 = raw10177step1 := by apply Matrix.ext; unfold raw10177step2 raw10177step1; decide +kernel
      have hl : raw10177step1Labels = labelEmbedding1 ∘ raw10177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10177step1 raw10177step1Labels raw10177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw10178 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10178step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10178step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10178step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10178 raw10178Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw10178 raw10178Labels = mixedMoment B raw10178step0 raw10178step0Labels := by
      have hz : ∀ j, raw10178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10178step0 = (fun i j => raw10178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10178step0 raw10178; decide +kernel
      have hl : raw10178step0Labels = raw10178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10178 raw10178Labels permutation346 hz
    mixedMoment B raw10178step0 raw10178step0Labels = mixedMoment B raw10178step1 raw10178step1Labels := by
      have ha : raw10178step1 = (fun i j => raw10178step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10178step1 raw10178step0; decide +kernel
      have hl : raw10178step1Labels = raw10178step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10178step0 raw10178step0Labels permutation41 permutation5
    mixedMoment B raw10178step1 raw10178step1Labels = mixedMoment B raw10178step2 raw10178step2Labels := by
      have ha : raw10178step2 = -raw10178step1 := by apply Matrix.ext; change ∀ i j, raw10178step2 i j = -(raw10178step1 i j); unfold raw10178step2 raw10178step1; decide +kernel
      have hl : raw10178step2Labels = raw10178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10178step2 raw10178step2Labels = mixedMoment B raw10178step3 raw10178step3Labels := by
      have ha : raw10178step3 = raw10178step2 := by apply Matrix.ext; unfold raw10178step3 raw10178step2; decide +kernel
      have hl : raw10178step2Labels = labelEmbedding1 ∘ raw10178step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10178step2 raw10178step2Labels raw10178step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw10179 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10179 raw10179Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw10179 raw10179Labels = mixedMoment B raw10179step0 raw10179step0Labels := by
      have ha : raw10179step0 = (fun i j => raw10179 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10179step0 raw10179; decide +kernel
      have hl : raw10179step0Labels = raw10179Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10179 raw10179Labels permutation152 permutation7
    mixedMoment B raw10179step0 raw10179step0Labels = mixedMoment B raw10179step1 raw10179step1Labels := by
      have ha : raw10179step1 = raw10179step0 := by apply Matrix.ext; unfold raw10179step1 raw10179step0; decide +kernel
      have hl : raw10179step0Labels = labelEmbedding1 ∘ raw10179step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10179step0 raw10179step0Labels raw10179step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3030 node3030Labels := by rfl

def raw10180 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10180 raw10180Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw10180 raw10180Labels = mixedMoment B raw10180step0 raw10180step0Labels := by
      have hz : ∀ j, raw10180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10180step0 = (fun i j => raw10180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10180step0 raw10180; decide +kernel
      have hl : raw10180step0Labels = raw10180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10180 raw10180Labels permutation346 hz
    mixedMoment B raw10180step0 raw10180step0Labels = mixedMoment B raw10180step1 raw10180step1Labels := by
      have ha : raw10180step1 = (fun i j => raw10180step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10180step1 raw10180step0; decide +kernel
      have hl : raw10180step1Labels = raw10180step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10180step0 raw10180step0Labels permutation32 permutation7
    mixedMoment B raw10180step1 raw10180step1Labels = mixedMoment B raw10180step2 raw10180step2Labels := by
      have ha : raw10180step2 = raw10180step1 := by apply Matrix.ext; unfold raw10180step2 raw10180step1; decide +kernel
      have hl : raw10180step1Labels = labelEmbedding1 ∘ raw10180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10180step1 raw10180step1Labels raw10180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3045 node3045Labels := by rfl

def raw10181 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw10181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10181 raw10181Labels = mixedMoment B node3205 node3205Labels := by
  calc
    mixedMoment B raw10181 raw10181Labels = mixedMoment B raw10181step0 raw10181step0Labels := by
      have ha : raw10181step0 = (fun i j => raw10181 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10181step0 raw10181; decide +kernel
      have hl : raw10181step0Labels = raw10181Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10181 raw10181Labels permutation212 permutation5
    mixedMoment B raw10181step0 raw10181step0Labels = mixedMoment B raw10181step1 raw10181step1Labels := by
      have ha : raw10181step1 = -raw10181step0 := by apply Matrix.ext; change ∀ i j, raw10181step1 i j = -(raw10181step0 i j); unfold raw10181step1 raw10181step0; decide +kernel
      have hl : raw10181step1Labels = raw10181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10181step1 raw10181step1Labels = mixedMoment B raw10181step2 raw10181step2Labels := by
      have ha : raw10181step2 = raw10181step1 := by apply Matrix.ext; unfold raw10181step2 raw10181step1; decide +kernel
      have hl : raw10181step1Labels = labelEmbedding1 ∘ raw10181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10181step1 raw10181step1Labels raw10181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3205 node3205Labels := by rfl

def raw10182 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10182step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10182 raw10182Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw10182 raw10182Labels = mixedMoment B raw10182step0 raw10182step0Labels := by
      have hz : ∀ j, raw10182 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10182step0 = (fun i j => raw10182 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10182step0 raw10182; decide +kernel
      have hl : raw10182step0Labels = raw10182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10182 raw10182Labels permutation265 hz
    mixedMoment B raw10182step0 raw10182step0Labels = mixedMoment B raw10182step1 raw10182step1Labels := by
      have ha : raw10182step1 = (fun i j => raw10182step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10182step1 raw10182step0; decide +kernel
      have hl : raw10182step1Labels = raw10182step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10182step0 raw10182step0Labels permutation32 permutation7
    mixedMoment B raw10182step1 raw10182step1Labels = mixedMoment B raw10182step2 raw10182step2Labels := by
      have ha : raw10182step2 = raw10182step1 := by apply Matrix.ext; unfold raw10182step2 raw10182step1; decide +kernel
      have hl : raw10182step1Labels = labelEmbedding1 ∘ raw10182step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10182step1 raw10182step1Labels raw10182step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw10183 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw10183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10183 raw10183Labels = mixedMoment B node3069 node3069Labels := by
  calc
    mixedMoment B raw10183 raw10183Labels = mixedMoment B raw10183step0 raw10183step0Labels := by
      have ha : raw10183step0 = (fun i j => raw10183 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10183step0 raw10183; decide +kernel
      have hl : raw10183step0Labels = raw10183Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10183 raw10183Labels permutation152 permutation7
    mixedMoment B raw10183step0 raw10183step0Labels = mixedMoment B raw10183step1 raw10183step1Labels := by
      have ha : raw10183step1 = raw10183step0 := by apply Matrix.ext; unfold raw10183step1 raw10183step0; decide +kernel
      have hl : raw10183step0Labels = labelEmbedding1 ∘ raw10183step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10183step0 raw10183step0Labels raw10183step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3069 node3069Labels := by rfl

def raw10184 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10184step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw10184step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10184step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10184 raw10184Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw10184 raw10184Labels = mixedMoment B raw10184step0 raw10184step0Labels := by
      have hz : ∀ j, raw10184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10184step0 = (fun i j => raw10184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10184step0 raw10184; decide +kernel
      have hl : raw10184step0Labels = raw10184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10184 raw10184Labels permutation434 hz
    mixedMoment B raw10184step0 raw10184step0Labels = mixedMoment B raw10184step1 raw10184step1Labels := by
      have hz : ∀ j, raw10184step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10184step1 = (fun i j => raw10184step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10184step1 raw10184step0; decide +kernel
      have hl : raw10184step1Labels = raw10184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10184step0 raw10184step0Labels permutation80 hz
    mixedMoment B raw10184step1 raw10184step1Labels = mixedMoment B raw10184step2 raw10184step2Labels := by
      have ha : raw10184step2 = (fun i j => raw10184step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10184step2 raw10184step1; decide +kernel
      have hl : raw10184step2Labels = raw10184step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10184step1 raw10184step1Labels permutation8 permutation7
    mixedMoment B raw10184step2 raw10184step2Labels = mixedMoment B raw10184step3 raw10184step3Labels := by
      have ha : raw10184step3 = raw10184step2 := by apply Matrix.ext; unfold raw10184step3 raw10184step2; decide +kernel
      have hl : raw10184step2Labels = labelEmbedding1 ∘ raw10184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10184step2 raw10184step2Labels raw10184step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw10185 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw10185step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10185 raw10185Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw10185 raw10185Labels = mixedMoment B raw10185step0 raw10185step0Labels := by
      have hz : ∀ j, raw10185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10185step0 = (fun i j => raw10185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10185step0 raw10185; decide +kernel
      have hl : raw10185step0Labels = raw10185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10185 raw10185Labels permutation346 hz
    mixedMoment B raw10185step0 raw10185step0Labels = mixedMoment B raw10185step1 raw10185step1Labels := by
      have ha : raw10185step1 = (fun i j => raw10185step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10185step1 raw10185step0; decide +kernel
      have hl : raw10185step1Labels = raw10185step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10185step0 raw10185step0Labels permutation32 permutation7
    mixedMoment B raw10185step1 raw10185step1Labels = mixedMoment B raw10185step2 raw10185step2Labels := by
      have ha : raw10185step2 = raw10185step1 := by apply Matrix.ext; unfold raw10185step2 raw10185step1; decide +kernel
      have hl : raw10185step1Labels = labelEmbedding1 ∘ raw10185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10185step1 raw10185step1Labels raw10185step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw10186 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10186 raw10186Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw10186 raw10186Labels = mixedMoment B raw10186step0 raw10186step0Labels := by
      have hz : ∀ j, raw10186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10186step0 = (fun i j => raw10186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10186step0 raw10186; decide +kernel
      have hl : raw10186step0Labels = raw10186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10186 raw10186Labels permutation346 hz
    mixedMoment B raw10186step0 raw10186step0Labels = mixedMoment B raw10186step1 raw10186step1Labels := by
      have ha : raw10186step1 = (fun i j => raw10186step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10186step1 raw10186step0; decide +kernel
      have hl : raw10186step1Labels = raw10186step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10186step0 raw10186step0Labels permutation139 permutation5
    mixedMoment B raw10186step1 raw10186step1Labels = mixedMoment B raw10186step2 raw10186step2Labels := by
      have ha : raw10186step2 = raw10186step1 := by apply Matrix.ext; unfold raw10186step2 raw10186step1; decide +kernel
      have hl : raw10186step1Labels = labelEmbedding1 ∘ raw10186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10186step1 raw10186step1Labels raw10186step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw10187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10187step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10187step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10187step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10187step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10187step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10187step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10187step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10187 raw10187Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw10187 raw10187Labels = mixedMoment B raw10187step0 raw10187step0Labels := by
      have hz : ∀ j, raw10187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10187step0 = (fun i j => raw10187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10187step0 raw10187; decide +kernel
      have hl : raw10187step0Labels = raw10187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10187 raw10187Labels permutation346 hz
    mixedMoment B raw10187step0 raw10187step0Labels = mixedMoment B raw10187step1 raw10187step1Labels := by
      have hz : ∀ j, raw10187step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10187step1 = (fun i j => raw10187step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10187step1 raw10187step0; decide +kernel
      have hl : raw10187step1Labels = raw10187step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10187step0 raw10187step0Labels permutation56 hz
    mixedMoment B raw10187step1 raw10187step1Labels = mixedMoment B raw10187step2 raw10187step2Labels := by
      have ha : raw10187step2 = (fun i j => raw10187step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10187step2 raw10187step1; decide +kernel
      have hl : raw10187step2Labels = raw10187step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10187step1 raw10187step1Labels permutation31 permutation5
    mixedMoment B raw10187step2 raw10187step2Labels = mixedMoment B raw10187step3 raw10187step3Labels := by
      have ha : raw10187step3 = raw10187step2 := by apply Matrix.ext; unfold raw10187step3 raw10187step2; decide +kernel
      have hl : raw10187step2Labels = labelEmbedding1 ∘ raw10187step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10187step2 raw10187step2Labels raw10187step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw10188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw10188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10188 raw10188Labels = mixedMoment B node2940 node2940Labels := by
  calc
    mixedMoment B raw10188 raw10188Labels = mixedMoment B raw10188step0 raw10188step0Labels := by
      have ha : raw10188step0 = (fun i j => raw10188 (permutation620 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10188step0 raw10188; decide +kernel
      have hl : raw10188step0Labels = raw10188Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10188 raw10188Labels permutation620 permutation5
    mixedMoment B raw10188step0 raw10188step0Labels = mixedMoment B raw10188step1 raw10188step1Labels := by
      have ha : raw10188step1 = raw10188step0 := by apply Matrix.ext; unfold raw10188step1 raw10188step0; decide +kernel
      have hl : raw10188step0Labels = labelEmbedding1 ∘ raw10188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10188step0 raw10188step0Labels raw10188step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2940 node2940Labels := by rfl

def raw10189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw10189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10189 raw10189Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw10189 raw10189Labels = mixedMoment B raw10189step0 raw10189step0Labels := by
      have hz : ∀ j, raw10189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10189step0 = (fun i j => raw10189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10189step0 raw10189; decide +kernel
      have hl : raw10189step0Labels = raw10189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10189 raw10189Labels permutation346 hz
    mixedMoment B raw10189step0 raw10189step0Labels = mixedMoment B raw10189step1 raw10189step1Labels := by
      have ha : raw10189step1 = (fun i j => raw10189step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10189step1 raw10189step0; decide +kernel
      have hl : raw10189step1Labels = raw10189step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10189step0 raw10189step0Labels permutation138 permutation5
    mixedMoment B raw10189step1 raw10189step1Labels = mixedMoment B raw10189step2 raw10189step2Labels := by
      have ha : raw10189step2 = raw10189step1 := by apply Matrix.ext; unfold raw10189step2 raw10189step1; decide +kernel
      have hl : raw10189step1Labels = labelEmbedding1 ∘ raw10189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10189step1 raw10189step1Labels raw10189step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw10190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10190step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10190 raw10190Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw10190 raw10190Labels = mixedMoment B raw10190step0 raw10190step0Labels := by
      have hz : ∀ j, raw10190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10190step0 = (fun i j => raw10190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10190step0 raw10190; decide +kernel
      have hl : raw10190step0Labels = raw10190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10190 raw10190Labels permutation346 hz
    mixedMoment B raw10190step0 raw10190step0Labels = mixedMoment B raw10190step1 raw10190step1Labels := by
      have ha : raw10190step1 = (fun i j => raw10190step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10190step1 raw10190step0; decide +kernel
      have hl : raw10190step1Labels = raw10190step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10190step0 raw10190step0Labels permutation40 permutation4
    mixedMoment B raw10190step1 raw10190step1Labels = mixedMoment B raw10190step2 raw10190step2Labels := by
      have ha : raw10190step2 = -raw10190step1 := by apply Matrix.ext; change ∀ i j, raw10190step2 i j = -(raw10190step1 i j); unfold raw10190step2 raw10190step1; decide +kernel
      have hl : raw10190step2Labels = raw10190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw10191 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw10191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10191step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10191 raw10191Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw10191 raw10191Labels = mixedMoment B raw10191step0 raw10191step0Labels := by
      have hz : ∀ j, raw10191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10191step0 = (fun i j => raw10191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10191step0 raw10191; decide +kernel
      have hl : raw10191step0Labels = raw10191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10191 raw10191Labels permutation346 hz
    mixedMoment B raw10191step0 raw10191step0Labels = mixedMoment B raw10191step1 raw10191step1Labels := by
      have ha : raw10191step1 = (fun i j => raw10191step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10191step1 raw10191step0; decide +kernel
      have hl : raw10191step1Labels = raw10191step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10191step0 raw10191step0Labels permutation40 permutation4
    mixedMoment B raw10191step1 raw10191step1Labels = mixedMoment B raw10191step2 raw10191step2Labels := by
      have ha : raw10191step2 = -raw10191step1 := by apply Matrix.ext; change ∀ i j, raw10191step2 i j = -(raw10191step1 i j); unfold raw10191step2 raw10191step1; decide +kernel
      have hl : raw10191step2Labels = raw10191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw10192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw10192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw10192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10192step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10192 raw10192Labels = mixedMoment B node2019 node2019Labels := by
  calc
    mixedMoment B raw10192 raw10192Labels = mixedMoment B raw10192step0 raw10192step0Labels := by
      have ha : raw10192step0 = (fun i j => raw10192 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10192step0 raw10192; decide +kernel
      have hl : raw10192step0Labels = raw10192Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10192 raw10192Labels permutation212 permutation4
    mixedMoment B raw10192step0 raw10192step0Labels = mixedMoment B raw10192step1 raw10192step1Labels := by
      have ha : raw10192step1 = -raw10192step0 := by apply Matrix.ext; change ∀ i j, raw10192step1 i j = -(raw10192step0 i j); unfold raw10192step1 raw10192step0; decide +kernel
      have hl : raw10192step1Labels = raw10192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2019 node2019Labels := by rfl

def raw10193 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw10193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10193 raw10193Labels = mixedMoment B node2022 node2022Labels := by
  calc
    mixedMoment B raw10193 raw10193Labels = mixedMoment B raw10193step0 raw10193step0Labels := by
      have hz : ∀ j, raw10193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10193step0 = (fun i j => raw10193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10193step0 raw10193; decide +kernel
      have hl : raw10193step0Labels = raw10193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10193 raw10193Labels permutation346 hz
    mixedMoment B raw10193step0 raw10193step0Labels = mixedMoment B raw10193step1 raw10193step1Labels := by
      have ha : raw10193step1 = (fun i j => raw10193step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw10193step1 raw10193step0; decide +kernel
      have hl : raw10193step1Labels = raw10193step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10193step0 raw10193step0Labels permutation40 permutation4
    mixedMoment B raw10193step1 raw10193step1Labels = mixedMoment B raw10193step2 raw10193step2Labels := by
      have ha : raw10193step2 = -raw10193step1 := by apply Matrix.ext; change ∀ i j, raw10193step2 i j = -(raw10193step1 i j); unfold raw10193step2 raw10193step1; decide +kernel
      have hl : raw10193step2Labels = raw10193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2022 node2022Labels := by rfl

def raw10194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10194 raw10194Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw10194 raw10194Labels = mixedMoment B raw10194step0 raw10194step0Labels := by
      have hz : ∀ j, raw10194 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10194step0 = (fun i j => raw10194 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10194step0 raw10194; decide +kernel
      have hl : raw10194step0Labels = raw10194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10194 raw10194Labels permutation434 hz
    mixedMoment B raw10194step0 raw10194step0Labels = mixedMoment B raw10194step1 raw10194step1Labels := by
      have hz : ∀ j, raw10194step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10194step1 = (fun i j => raw10194step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10194step1 raw10194step0; decide +kernel
      have hl : raw10194step1Labels = raw10194step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10194step0 raw10194step0Labels permutation80 hz
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw10195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10195step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10195 raw10195Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw10195 raw10195Labels = mixedMoment B raw10195step0 raw10195step0Labels := by
      have hz : ∀ j, raw10195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10195step0 = (fun i j => raw10195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10195step0 raw10195; decide +kernel
      have hl : raw10195step0Labels = raw10195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10195 raw10195Labels permutation434 hz
    mixedMoment B raw10195step0 raw10195step0Labels = mixedMoment B raw10195step1 raw10195step1Labels := by
      have hz : ∀ j, raw10195step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10195step1 = (fun i j => raw10195step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10195step1 raw10195step0; decide +kernel
      have hl : raw10195step1Labels = raw10195step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10195step0 raw10195step0Labels permutation56 hz
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw10196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10196step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10196step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10196step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10196 raw10196Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw10196 raw10196Labels = mixedMoment B raw10196step0 raw10196step0Labels := by
      have hz : ∀ j, raw10196 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10196step0 = (fun i j => raw10196 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10196step0 raw10196; decide +kernel
      have hl : raw10196step0Labels = raw10196Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10196 raw10196Labels permutation346 hz
    mixedMoment B raw10196step0 raw10196step0Labels = mixedMoment B raw10196step1 raw10196step1Labels := by
      have hz : ∀ j, raw10196step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10196step1 = (fun i j => raw10196step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10196step1 raw10196step0; decide +kernel
      have hl : raw10196step1Labels = raw10196step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10196step0 raw10196step0Labels permutation56 hz
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw10197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10197step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10197step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10197step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]
def raw10197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10197step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw10197step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw10197step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw10197step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical10197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10197 raw10197Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw10197 raw10197Labels = mixedMoment B raw10197step0 raw10197step0Labels := by
      have hz : ∀ j, raw10197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10197step0 = (fun i j => raw10197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10197step0 raw10197; decide +kernel
      have hl : raw10197step0Labels = raw10197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10197 raw10197Labels permutation434 hz
    mixedMoment B raw10197step0 raw10197step0Labels = mixedMoment B raw10197step1 raw10197step1Labels := by
      have hz : ∀ j, raw10197step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10197step1 = (fun i j => raw10197step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10197step1 raw10197step0; decide +kernel
      have hl : raw10197step1Labels = raw10197step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10197step0 raw10197step0Labels permutation80 hz
    mixedMoment B raw10197step1 raw10197step1Labels = mixedMoment B raw10197step2 raw10197step2Labels := by
      have hz : ∀ j, raw10197step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10197step2 = (fun i j => raw10197step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10197step2 raw10197step1; decide +kernel
      have hl : raw10197step2Labels = raw10197step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10197step1 raw10197step1Labels permutation14 hz
    mixedMoment B raw10197step2 raw10197step2Labels = mixedMoment B raw10197step3 raw10197step3Labels := by
      have hz : ∀ i, raw10197step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw10197step3 = (fun i j => raw10197step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw10197step3 raw10197step2; decide +kernel
      have hl : raw10197step3Labels = (fun j => raw10197step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw10197step2 raw10197step2Labels permutation4 hz
    mixedMoment B raw10197step3 raw10197step3Labels = mixedMoment B raw10197step4 raw10197step4Labels := by
      have ha : raw10197step4 = raw10197step3 := by apply Matrix.ext; unfold raw10197step4 raw10197step3; decide +kernel
      have hl : raw10197step3Labels = labelEmbedding2 ∘ raw10197step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10197step3 raw10197step3Labels raw10197step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw10198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10198step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10198 raw10198Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw10198 raw10198Labels = mixedMoment B raw10198step0 raw10198step0Labels := by
      have hz : ∀ j, raw10198 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10198step0 = (fun i j => raw10198 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10198step0 raw10198; decide +kernel
      have hl : raw10198step0Labels = raw10198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10198 raw10198Labels permutation434 hz
    mixedMoment B raw10198step0 raw10198step0Labels = mixedMoment B raw10198step1 raw10198step1Labels := by
      have hz : ∀ j, raw10198step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10198step1 = (fun i j => raw10198step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10198step1 raw10198step0; decide +kernel
      have hl : raw10198step1Labels = raw10198step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10198step0 raw10198step0Labels permutation80 hz
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw10199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10199 raw10199Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw10199 raw10199Labels = mixedMoment B raw10199step0 raw10199step0Labels := by
      have hz : ∀ j, raw10199 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10199step0 = (fun i j => raw10199 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10199step0 raw10199; decide +kernel
      have hl : raw10199step0Labels = raw10199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10199 raw10199Labels permutation434 hz
    mixedMoment B raw10199step0 raw10199step0Labels = mixedMoment B raw10199step1 raw10199step1Labels := by
      have ha : raw10199step1 = (fun i j => raw10199step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10199step1 raw10199step0; decide +kernel
      have hl : raw10199step1Labels = raw10199step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10199step0 raw10199step0Labels permutation38 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw10200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10200 raw10200Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw10200 raw10200Labels = mixedMoment B raw10200step0 raw10200step0Labels := by
      have hz : ∀ j, raw10200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10200step0 = (fun i j => raw10200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10200step0 raw10200; decide +kernel
      have hl : raw10200step0Labels = raw10200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10200 raw10200Labels permutation346 hz
    mixedMoment B raw10200step0 raw10200step0Labels = mixedMoment B raw10200step1 raw10200step1Labels := by
      have ha : raw10200step1 = (fun i j => raw10200step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10200step1 raw10200step0; decide +kernel
      have hl : raw10200step1Labels = raw10200step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10200step0 raw10200step0Labels permutation38 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw10201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10201 raw10201Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw10201 raw10201Labels = mixedMoment B raw10201step0 raw10201step0Labels := by
      have hz : ∀ j, raw10201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10201step0 = (fun i j => raw10201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10201step0 raw10201; decide +kernel
      have hl : raw10201step0Labels = raw10201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10201 raw10201Labels permutation434 hz
    mixedMoment B raw10201step0 raw10201step0Labels = mixedMoment B raw10201step1 raw10201step1Labels := by
      have hz : ∀ j, raw10201step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10201step1 = (fun i j => raw10201step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10201step1 raw10201step0; decide +kernel
      have hl : raw10201step1Labels = raw10201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10201step0 raw10201step0Labels permutation80 hz
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw10202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10202 raw10202Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw10202 raw10202Labels = mixedMoment B raw10202step0 raw10202step0Labels := by
      have hz : ∀ j, raw10202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10202step0 = (fun i j => raw10202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10202step0 raw10202; decide +kernel
      have hl : raw10202step0Labels = raw10202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10202 raw10202Labels permutation434 hz
    mixedMoment B raw10202step0 raw10202step0Labels = mixedMoment B raw10202step1 raw10202step1Labels := by
      have hz : ∀ j, raw10202step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10202step1 = (fun i j => raw10202step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10202step1 raw10202step0; decide +kernel
      have hl : raw10202step1Labels = raw10202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10202step0 raw10202step0Labels permutation56 hz
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw10203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10203 raw10203Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw10203 raw10203Labels = mixedMoment B raw10203step0 raw10203step0Labels := by
      have hz : ∀ j, raw10203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10203step0 = (fun i j => raw10203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10203step0 raw10203; decide +kernel
      have hl : raw10203step0Labels = raw10203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10203 raw10203Labels permutation434 hz
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw10204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10204step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10204 raw10204Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw10204 raw10204Labels = mixedMoment B raw10204step0 raw10204step0Labels := by
      have hz : ∀ j, raw10204 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10204step0 = (fun i j => raw10204 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10204step0 raw10204; decide +kernel
      have hl : raw10204step0Labels = raw10204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10204 raw10204Labels permutation265 hz
    mixedMoment B raw10204step0 raw10204step0Labels = mixedMoment B raw10204step1 raw10204step1Labels := by
      have ha : raw10204step1 = (fun i j => raw10204step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10204step1 raw10204step0; decide +kernel
      have hl : raw10204step1Labels = raw10204step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10204step0 raw10204step0Labels permutation38 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw10205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10205step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10205step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10205 raw10205Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw10205 raw10205Labels = mixedMoment B raw10205step0 raw10205step0Labels := by
      have hz : ∀ j, raw10205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10205step0 = (fun i j => raw10205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10205step0 raw10205; decide +kernel
      have hl : raw10205step0Labels = raw10205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10205 raw10205Labels permutation434 hz
    mixedMoment B raw10205step0 raw10205step0Labels = mixedMoment B raw10205step1 raw10205step1Labels := by
      have hz : ∀ j, raw10205step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10205step1 = (fun i j => raw10205step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10205step1 raw10205step0; decide +kernel
      have hl : raw10205step1Labels = raw10205step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10205step0 raw10205step0Labels permutation56 hz
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw10206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10206step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10206 raw10206Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw10206 raw10206Labels = mixedMoment B raw10206step0 raw10206step0Labels := by
      have hz : ∀ j, raw10206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10206step0 = (fun i j => raw10206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10206step0 raw10206; decide +kernel
      have hl : raw10206step0Labels = raw10206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10206 raw10206Labels permutation346 hz
    mixedMoment B raw10206step0 raw10206step0Labels = mixedMoment B raw10206step1 raw10206step1Labels := by
      have hz : ∀ j, raw10206step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10206step1 = (fun i j => raw10206step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10206step1 raw10206step0; decide +kernel
      have hl : raw10206step1Labels = raw10206step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10206step0 raw10206step0Labels permutation56 hz
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw10207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10207 raw10207Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw10207 raw10207Labels = mixedMoment B raw10207step0 raw10207step0Labels := by
      have hz : ∀ j, raw10207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10207step0 = (fun i j => raw10207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10207step0 raw10207; decide +kernel
      have hl : raw10207step0Labels = raw10207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10207 raw10207Labels permutation346 hz
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw10208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw10208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10208 raw10208Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw10208 raw10208Labels = mixedMoment B raw10208step0 raw10208step0Labels := by
      have hz : ∀ j, raw10208 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10208step0 = (fun i j => raw10208 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10208step0 raw10208; decide +kernel
      have hl : raw10208step0Labels = raw10208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10208 raw10208Labels permutation265 hz
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw10209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10209 raw10209Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw10209 raw10209Labels = mixedMoment B raw10209step0 raw10209step0Labels := by
      have hz : ∀ j, raw10209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10209step0 = (fun i j => raw10209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10209step0 raw10209; decide +kernel
      have hl : raw10209step0Labels = raw10209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10209 raw10209Labels permutation346 hz
    mixedMoment B raw10209step0 raw10209step0Labels = mixedMoment B raw10209step1 raw10209step1Labels := by
      have hz : ∀ j, raw10209step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10209step1 = (fun i j => raw10209step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10209step1 raw10209step0; decide +kernel
      have hl : raw10209step1Labels = raw10209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10209step0 raw10209step0Labels permutation56 hz
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw10210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10210step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw10210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10210 raw10210Labels = mixedMoment B node4628 node4628Labels := by
  calc
    mixedMoment B raw10210 raw10210Labels = mixedMoment B raw10210step0 raw10210step0Labels := by
      have hz : ∀ j, raw10210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10210step0 = (fun i j => raw10210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10210step0 raw10210; decide +kernel
      have hl : raw10210step0Labels = raw10210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10210 raw10210Labels permutation434 hz
    mixedMoment B raw10210step0 raw10210step0Labels = mixedMoment B raw10210step1 raw10210step1Labels := by
      have hz : ∀ j, raw10210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10210step1 = (fun i j => raw10210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10210step1 raw10210step0; decide +kernel
      have hl : raw10210step1Labels = raw10210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10210step0 raw10210step0Labels permutation80 hz
    mixedMoment B raw10210step1 raw10210step1Labels = mixedMoment B raw10210step2 raw10210step2Labels := by
      have hz : ∀ j, raw10210step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10210step2 = (fun i j => raw10210step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10210step2 raw10210step1; decide +kernel
      have hl : raw10210step2Labels = raw10210step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10210step1 raw10210step1Labels permutation14 hz
    _ = mixedMoment B node4628 node4628Labels := by rfl

def raw10211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10211 raw10211Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw10211 raw10211Labels = mixedMoment B raw10211step0 raw10211step0Labels := by
      have hz : ∀ j, raw10211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10211step0 = (fun i j => raw10211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10211step0 raw10211; decide +kernel
      have hl : raw10211step0Labels = raw10211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10211 raw10211Labels permutation434 hz
    mixedMoment B raw10211step0 raw10211step0Labels = mixedMoment B raw10211step1 raw10211step1Labels := by
      have hz : ∀ j, raw10211step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10211step1 = (fun i j => raw10211step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10211step1 raw10211step0; decide +kernel
      have hl : raw10211step1Labels = raw10211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10211step0 raw10211step0Labels permutation80 hz
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw10212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10212 raw10212Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw10212 raw10212Labels = mixedMoment B raw10212step0 raw10212step0Labels := by
      have hz : ∀ j, raw10212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10212step0 = (fun i j => raw10212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10212step0 raw10212; decide +kernel
      have hl : raw10212step0Labels = raw10212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10212 raw10212Labels permutation434 hz
    mixedMoment B raw10212step0 raw10212step0Labels = mixedMoment B raw10212step1 raw10212step1Labels := by
      have hz : ∀ j, raw10212step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10212step1 = (fun i j => raw10212step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10212step1 raw10212step0; decide +kernel
      have hl : raw10212step1Labels = raw10212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10212step0 raw10212step0Labels permutation56 hz
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw10213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw10213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10213 raw10213Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw10213 raw10213Labels = mixedMoment B raw10213step0 raw10213step0Labels := by
      have hz : ∀ j, raw10213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10213step0 = (fun i j => raw10213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10213step0 raw10213; decide +kernel
      have hl : raw10213step0Labels = raw10213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10213 raw10213Labels permutation346 hz
    mixedMoment B raw10213step0 raw10213step0Labels = mixedMoment B raw10213step1 raw10213step1Labels := by
      have hz : ∀ j, raw10213step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10213step1 = (fun i j => raw10213step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10213step1 raw10213step0; decide +kernel
      have hl : raw10213step1Labels = raw10213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10213step0 raw10213step0Labels permutation56 hz
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw10214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10214step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw10214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10214step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw10214step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10214step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw10214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10214 raw10214Labels = mixedMoment B node5309 node5309Labels := by
  calc
    mixedMoment B raw10214 raw10214Labels = mixedMoment B raw10214step0 raw10214step0Labels := by
      have hz : ∀ j, raw10214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10214step0 = (fun i j => raw10214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10214step0 raw10214; decide +kernel
      have hl : raw10214step0Labels = raw10214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10214 raw10214Labels permutation434 hz
    mixedMoment B raw10214step0 raw10214step0Labels = mixedMoment B raw10214step1 raw10214step1Labels := by
      have hz : ∀ j, raw10214step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10214step1 = (fun i j => raw10214step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10214step1 raw10214step0; decide +kernel
      have hl : raw10214step1Labels = raw10214step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10214step0 raw10214step0Labels permutation80 hz
    mixedMoment B raw10214step1 raw10214step1Labels = mixedMoment B raw10214step2 raw10214step2Labels := by
      have hz : ∀ j, raw10214step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10214step2 = (fun i j => raw10214step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10214step2 raw10214step1; decide +kernel
      have hl : raw10214step2Labels = raw10214step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10214step1 raw10214step1Labels permutation14 hz
    mixedMoment B raw10214step2 raw10214step2Labels = mixedMoment B raw10214step3 raw10214step3Labels := by
      have ha : raw10214step3 = (fun i j => raw10214step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10214step3 raw10214step2; decide +kernel
      have hl : raw10214step3Labels = raw10214step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10214step2 raw10214step2Labels permutation3 permutation2
    _ = mixedMoment B node5309 node5309Labels := by rfl

def raw10215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10215step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw10215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10215step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw10215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10215 raw10215Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw10215 raw10215Labels = mixedMoment B raw10215step0 raw10215step0Labels := by
      have hz : ∀ j, raw10215 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10215step0 = (fun i j => raw10215 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10215step0 raw10215; decide +kernel
      have hl : raw10215step0Labels = raw10215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10215 raw10215Labels permutation434 hz
    mixedMoment B raw10215step0 raw10215step0Labels = mixedMoment B raw10215step1 raw10215step1Labels := by
      have hz : ∀ j, raw10215step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10215step1 = (fun i j => raw10215step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10215step1 raw10215step0; decide +kernel
      have hl : raw10215step1Labels = raw10215step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10215step0 raw10215step0Labels permutation80 hz
    mixedMoment B raw10215step1 raw10215step1Labels = mixedMoment B raw10215step2 raw10215step2Labels := by
      have hz : ∀ j, raw10215step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10215step2 = (fun i j => raw10215step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10215step2 raw10215step1; decide +kernel
      have hl : raw10215step2Labels = raw10215step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10215step1 raw10215step1Labels permutation14 hz
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw10216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10216 raw10216Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw10216 raw10216Labels = mixedMoment B raw10216step0 raw10216step0Labels := by
      have hz : ∀ j, raw10216 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10216step0 = (fun i j => raw10216 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10216step0 raw10216; decide +kernel
      have hl : raw10216step0Labels = raw10216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10216 raw10216Labels permutation434 hz
    mixedMoment B raw10216step0 raw10216step0Labels = mixedMoment B raw10216step1 raw10216step1Labels := by
      have hz : ∀ j, raw10216step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10216step1 = (fun i j => raw10216step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10216step1 raw10216step0; decide +kernel
      have hl : raw10216step1Labels = raw10216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10216step0 raw10216step0Labels permutation80 hz
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw10217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10217 raw10217Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw10217 raw10217Labels = mixedMoment B raw10217step0 raw10217step0Labels := by
      have hz : ∀ j, raw10217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10217step0 = (fun i j => raw10217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10217step0 raw10217; decide +kernel
      have hl : raw10217step0Labels = raw10217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10217 raw10217Labels permutation434 hz
    mixedMoment B raw10217step0 raw10217step0Labels = mixedMoment B raw10217step1 raw10217step1Labels := by
      have hz : ∀ j, raw10217step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10217step1 = (fun i j => raw10217step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10217step1 raw10217step0; decide +kernel
      have hl : raw10217step1Labels = raw10217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10217step0 raw10217step0Labels permutation56 hz
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw10218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10218step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10218 raw10218Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw10218 raw10218Labels = mixedMoment B raw10218step0 raw10218step0Labels := by
      have hz : ∀ j, raw10218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10218step0 = (fun i j => raw10218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10218step0 raw10218; decide +kernel
      have hl : raw10218step0Labels = raw10218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10218 raw10218Labels permutation346 hz
    mixedMoment B raw10218step0 raw10218step0Labels = mixedMoment B raw10218step1 raw10218step1Labels := by
      have hz : ∀ j, raw10218step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10218step1 = (fun i j => raw10218step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10218step1 raw10218step0; decide +kernel
      have hl : raw10218step1Labels = raw10218step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10218step0 raw10218step0Labels permutation56 hz
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw10219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10219step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![1, 1, -2]]
def raw10219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10219step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw10219step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10219step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10219step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10219step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw10219step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10219 raw10219Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw10219 raw10219Labels = mixedMoment B raw10219step0 raw10219step0Labels := by
      have hz : ∀ j, raw10219 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10219step0 = (fun i j => raw10219 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10219step0 raw10219; decide +kernel
      have hl : raw10219step0Labels = raw10219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10219 raw10219Labels permutation434 hz
    mixedMoment B raw10219step0 raw10219step0Labels = mixedMoment B raw10219step1 raw10219step1Labels := by
      have hz : ∀ j, raw10219step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10219step1 = (fun i j => raw10219step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10219step1 raw10219step0; decide +kernel
      have hl : raw10219step1Labels = raw10219step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10219step0 raw10219step0Labels permutation80 hz
    mixedMoment B raw10219step1 raw10219step1Labels = mixedMoment B raw10219step2 raw10219step2Labels := by
      have hz : ∀ j, raw10219step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10219step2 = (fun i j => raw10219step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10219step2 raw10219step1; decide +kernel
      have hl : raw10219step2Labels = raw10219step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10219step1 raw10219step1Labels permutation14 hz
    mixedMoment B raw10219step2 raw10219step2Labels = mixedMoment B raw10219step3 raw10219step3Labels := by
      have ha : raw10219step3 = (fun i j => raw10219step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10219step3 raw10219step2; decide +kernel
      have hl : raw10219step3Labels = raw10219step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10219step2 raw10219step2Labels permutation2 permutation7
    mixedMoment B raw10219step3 raw10219step3Labels = mixedMoment B raw10219step4 raw10219step4Labels := by
      have ha : raw10219step4 = -raw10219step3 := by apply Matrix.ext; change ∀ i j, raw10219step4 i j = -(raw10219step3 i j); unfold raw10219step4 raw10219step3; decide +kernel
      have hl : raw10219step4Labels = raw10219step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10219step4 raw10219step4Labels = mixedMoment B raw10219step5 raw10219step5Labels := by
      have ha : raw10219step5 = raw10219step4 := by apply Matrix.ext; unfold raw10219step5 raw10219step4; decide +kernel
      have hl : raw10219step4Labels = labelEmbedding10 ∘ raw10219step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10219step4 raw10219step4Labels raw10219step5Labels labelEmbedding10 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw10220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10220step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10220 raw10220Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw10220 raw10220Labels = mixedMoment B raw10220step0 raw10220step0Labels := by
      have hz : ∀ j, raw10220 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10220step0 = (fun i j => raw10220 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10220step0 raw10220; decide +kernel
      have hl : raw10220step0Labels = raw10220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10220 raw10220Labels permutation434 hz
    mixedMoment B raw10220step0 raw10220step0Labels = mixedMoment B raw10220step1 raw10220step1Labels := by
      have hz : ∀ j, raw10220step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10220step1 = (fun i j => raw10220step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10220step1 raw10220step0; decide +kernel
      have hl : raw10220step1Labels = raw10220step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10220step0 raw10220step0Labels permutation80 hz
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw10221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10221 raw10221Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw10221 raw10221Labels = mixedMoment B raw10221step0 raw10221step0Labels := by
      have hz : ∀ j, raw10221 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10221step0 = (fun i j => raw10221 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10221step0 raw10221; decide +kernel
      have hl : raw10221step0Labels = raw10221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10221 raw10221Labels permutation434 hz
    mixedMoment B raw10221step0 raw10221step0Labels = mixedMoment B raw10221step1 raw10221step1Labels := by
      have ha : raw10221step1 = (fun i j => raw10221step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10221step1 raw10221step0; decide +kernel
      have hl : raw10221step1Labels = raw10221step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10221step0 raw10221step0Labels permutation38 permutation2
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw10222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10222 raw10222Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw10222 raw10222Labels = mixedMoment B raw10222step0 raw10222step0Labels := by
      have hz : ∀ j, raw10222 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10222step0 = (fun i j => raw10222 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10222step0 raw10222; decide +kernel
      have hl : raw10222step0Labels = raw10222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10222 raw10222Labels permutation346 hz
    mixedMoment B raw10222step0 raw10222step0Labels = mixedMoment B raw10222step1 raw10222step1Labels := by
      have ha : raw10222step1 = (fun i j => raw10222step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10222step1 raw10222step0; decide +kernel
      have hl : raw10222step1Labels = raw10222step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10222step0 raw10222step0Labels permutation38 permutation2
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw10223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10223 raw10223Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw10223 raw10223Labels = mixedMoment B raw10223step0 raw10223step0Labels := by
      have hz : ∀ j, raw10223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10223step0 = (fun i j => raw10223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10223step0 raw10223; decide +kernel
      have hl : raw10223step0Labels = raw10223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10223 raw10223Labels permutation434 hz
    mixedMoment B raw10223step0 raw10223step0Labels = mixedMoment B raw10223step1 raw10223step1Labels := by
      have hz : ∀ j, raw10223step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10223step1 = (fun i j => raw10223step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10223step1 raw10223step0; decide +kernel
      have hl : raw10223step1Labels = raw10223step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10223step0 raw10223step0Labels permutation80 hz
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw10224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10224 raw10224Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw10224 raw10224Labels = mixedMoment B raw10224step0 raw10224step0Labels := by
      have hz : ∀ j, raw10224 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10224step0 = (fun i j => raw10224 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10224step0 raw10224; decide +kernel
      have hl : raw10224step0Labels = raw10224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10224 raw10224Labels permutation434 hz
    mixedMoment B raw10224step0 raw10224step0Labels = mixedMoment B raw10224step1 raw10224step1Labels := by
      have hz : ∀ j, raw10224step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10224step1 = (fun i j => raw10224step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10224step1 raw10224step0; decide +kernel
      have hl : raw10224step1Labels = raw10224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10224step0 raw10224step0Labels permutation56 hz
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw10225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10225 raw10225Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw10225 raw10225Labels = mixedMoment B raw10225step0 raw10225step0Labels := by
      have hz : ∀ j, raw10225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10225step0 = (fun i j => raw10225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10225step0 raw10225; decide +kernel
      have hl : raw10225step0Labels = raw10225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10225 raw10225Labels permutation434 hz
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw10226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10226 raw10226Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw10226 raw10226Labels = mixedMoment B raw10226step0 raw10226step0Labels := by
      have hz : ∀ j, raw10226 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10226step0 = (fun i j => raw10226 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10226step0 raw10226; decide +kernel
      have hl : raw10226step0Labels = raw10226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10226 raw10226Labels permutation265 hz
    mixedMoment B raw10226step0 raw10226step0Labels = mixedMoment B raw10226step1 raw10226step1Labels := by
      have ha : raw10226step1 = (fun i j => raw10226step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10226step1 raw10226step0; decide +kernel
      have hl : raw10226step1Labels = raw10226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10226step0 raw10226step0Labels permutation38 permutation2
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw10227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10227 raw10227Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw10227 raw10227Labels = mixedMoment B raw10227step0 raw10227step0Labels := by
      have hz : ∀ j, raw10227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10227step0 = (fun i j => raw10227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10227step0 raw10227; decide +kernel
      have hl : raw10227step0Labels = raw10227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10227 raw10227Labels permutation434 hz
    mixedMoment B raw10227step0 raw10227step0Labels = mixedMoment B raw10227step1 raw10227step1Labels := by
      have hz : ∀ j, raw10227step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10227step1 = (fun i j => raw10227step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10227step1 raw10227step0; decide +kernel
      have hl : raw10227step1Labels = raw10227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10227step0 raw10227step0Labels permutation56 hz
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw10228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10228 raw10228Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw10228 raw10228Labels = mixedMoment B raw10228step0 raw10228step0Labels := by
      have hz : ∀ j, raw10228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10228step0 = (fun i j => raw10228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10228step0 raw10228; decide +kernel
      have hl : raw10228step0Labels = raw10228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10228 raw10228Labels permutation346 hz
    mixedMoment B raw10228step0 raw10228step0Labels = mixedMoment B raw10228step1 raw10228step1Labels := by
      have hz : ∀ j, raw10228step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10228step1 = (fun i j => raw10228step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10228step1 raw10228step0; decide +kernel
      have hl : raw10228step1Labels = raw10228step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10228step0 raw10228step0Labels permutation56 hz
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw10229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10229 raw10229Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw10229 raw10229Labels = mixedMoment B raw10229step0 raw10229step0Labels := by
      have hz : ∀ j, raw10229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10229step0 = (fun i j => raw10229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10229step0 raw10229; decide +kernel
      have hl : raw10229step0Labels = raw10229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10229 raw10229Labels permutation346 hz
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw10230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10230 raw10230Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw10230 raw10230Labels = mixedMoment B raw10230step0 raw10230step0Labels := by
      have hz : ∀ j, raw10230 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw10230step0 = (fun i j => raw10230 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw10230step0 raw10230; decide +kernel
      have hl : raw10230step0Labels = raw10230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10230 raw10230Labels permutation265 hz
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw10231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10231step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10231 raw10231Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw10231 raw10231Labels = mixedMoment B raw10231step0 raw10231step0Labels := by
      have hz : ∀ j, raw10231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10231step0 = (fun i j => raw10231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10231step0 raw10231; decide +kernel
      have hl : raw10231step0Labels = raw10231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10231 raw10231Labels permutation346 hz
    mixedMoment B raw10231step0 raw10231step0Labels = mixedMoment B raw10231step1 raw10231step1Labels := by
      have hz : ∀ j, raw10231step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10231step1 = (fun i j => raw10231step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10231step1 raw10231step0; decide +kernel
      have hl : raw10231step1Labels = raw10231step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10231step0 raw10231step0Labels permutation56 hz
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw10232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10232step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw10232step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10232 raw10232Labels = mixedMoment B node4627 node4627Labels := by
  calc
    mixedMoment B raw10232 raw10232Labels = mixedMoment B raw10232step0 raw10232step0Labels := by
      have hz : ∀ j, raw10232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10232step0 = (fun i j => raw10232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10232step0 raw10232; decide +kernel
      have hl : raw10232step0Labels = raw10232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10232 raw10232Labels permutation434 hz
    mixedMoment B raw10232step0 raw10232step0Labels = mixedMoment B raw10232step1 raw10232step1Labels := by
      have hz : ∀ j, raw10232step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10232step1 = (fun i j => raw10232step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10232step1 raw10232step0; decide +kernel
      have hl : raw10232step1Labels = raw10232step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10232step0 raw10232step0Labels permutation80 hz
    mixedMoment B raw10232step1 raw10232step1Labels = mixedMoment B raw10232step2 raw10232step2Labels := by
      have hz : ∀ j, raw10232step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10232step2 = (fun i j => raw10232step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10232step2 raw10232step1; decide +kernel
      have hl : raw10232step2Labels = raw10232step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10232step1 raw10232step1Labels permutation14 hz
    _ = mixedMoment B node4627 node4627Labels := by rfl

def raw10233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10233 raw10233Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw10233 raw10233Labels = mixedMoment B raw10233step0 raw10233step0Labels := by
      have hz : ∀ j, raw10233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10233step0 = (fun i j => raw10233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10233step0 raw10233; decide +kernel
      have hl : raw10233step0Labels = raw10233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10233 raw10233Labels permutation434 hz
    mixedMoment B raw10233step0 raw10233step0Labels = mixedMoment B raw10233step1 raw10233step1Labels := by
      have hz : ∀ j, raw10233step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10233step1 = (fun i j => raw10233step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10233step1 raw10233step0; decide +kernel
      have hl : raw10233step1Labels = raw10233step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10233step0 raw10233step0Labels permutation80 hz
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw10234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10234 raw10234Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw10234 raw10234Labels = mixedMoment B raw10234step0 raw10234step0Labels := by
      have hz : ∀ j, raw10234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10234step0 = (fun i j => raw10234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10234step0 raw10234; decide +kernel
      have hl : raw10234step0Labels = raw10234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10234 raw10234Labels permutation434 hz
    mixedMoment B raw10234step0 raw10234step0Labels = mixedMoment B raw10234step1 raw10234step1Labels := by
      have hz : ∀ j, raw10234step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10234step1 = (fun i j => raw10234step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10234step1 raw10234step0; decide +kernel
      have hl : raw10234step1Labels = raw10234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10234step0 raw10234step0Labels permutation56 hz
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw10235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw10235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10235 raw10235Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw10235 raw10235Labels = mixedMoment B raw10235step0 raw10235step0Labels := by
      have hz : ∀ j, raw10235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10235step0 = (fun i j => raw10235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10235step0 raw10235; decide +kernel
      have hl : raw10235step0Labels = raw10235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10235 raw10235Labels permutation346 hz
    mixedMoment B raw10235step0 raw10235step0Labels = mixedMoment B raw10235step1 raw10235step1Labels := by
      have hz : ∀ j, raw10235step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10235step1 = (fun i j => raw10235step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10235step1 raw10235step0; decide +kernel
      have hl : raw10235step1Labels = raw10235step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10235step0 raw10235step0Labels permutation56 hz
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw10236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw10236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw10236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw10236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10236step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw10236step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10236step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw10236step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10236 raw10236Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw10236 raw10236Labels = mixedMoment B raw10236step0 raw10236step0Labels := by
      have hz : ∀ j, raw10236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10236step0 = (fun i j => raw10236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10236step0 raw10236; decide +kernel
      have hl : raw10236step0Labels = raw10236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10236 raw10236Labels permutation434 hz
    mixedMoment B raw10236step0 raw10236step0Labels = mixedMoment B raw10236step1 raw10236step1Labels := by
      have hz : ∀ j, raw10236step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10236step1 = (fun i j => raw10236step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10236step1 raw10236step0; decide +kernel
      have hl : raw10236step1Labels = raw10236step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10236step0 raw10236step0Labels permutation80 hz
    mixedMoment B raw10236step1 raw10236step1Labels = mixedMoment B raw10236step2 raw10236step2Labels := by
      have hz : ∀ j, raw10236step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw10236step2 = (fun i j => raw10236step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw10236step2 raw10236step1; decide +kernel
      have hl : raw10236step2Labels = raw10236step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10236step1 raw10236step1Labels permutation14 hz
    mixedMoment B raw10236step2 raw10236step2Labels = mixedMoment B raw10236step3 raw10236step3Labels := by
      have ha : raw10236step3 = (fun i j => raw10236step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10236step3 raw10236step2; decide +kernel
      have hl : raw10236step3Labels = raw10236step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10236step2 raw10236step2Labels permutation3 permutation2
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw10237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw10237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw10237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw10237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10237step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![3, -1, -2]]
def raw10237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10237step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 1, 2], ![3, -1, -2]]
def raw10237step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10237 raw10237Labels = mixedMoment B node5312 node5312Labels := by
  calc
    mixedMoment B raw10237 raw10237Labels = mixedMoment B raw10237step0 raw10237step0Labels := by
      have hz : ∀ j, raw10237 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10237step0 = (fun i j => raw10237 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10237step0 raw10237; decide +kernel
      have hl : raw10237step0Labels = raw10237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10237 raw10237Labels permutation520 hz
    mixedMoment B raw10237step0 raw10237step0Labels = mixedMoment B raw10237step1 raw10237step1Labels := by
      have hz : ∀ j, raw10237step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw10237step1 = (fun i j => raw10237step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw10237step1 raw10237step0; decide +kernel
      have hl : raw10237step1Labels = raw10237step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10237step0 raw10237step0Labels permutation104 hz
    mixedMoment B raw10237step1 raw10237step1Labels = mixedMoment B raw10237step2 raw10237step2Labels := by
      have hz : ∀ j, raw10237step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw10237step2 = (fun i j => raw10237step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw10237step2 raw10237step1; decide +kernel
      have hl : raw10237step2Labels = raw10237step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10237step1 raw10237step1Labels permutation20 hz
    mixedMoment B raw10237step2 raw10237step2Labels = mixedMoment B raw10237step3 raw10237step3Labels := by
      have hz : ∀ j, raw10237step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw10237step3 = (fun i j => raw10237step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw10237step3 raw10237step2; decide +kernel
      have hl : raw10237step3Labels = raw10237step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10237step2 raw10237step2Labels permutation4 hz
    _ = mixedMoment B node5312 node5312Labels := by rfl

def raw10238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10238step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10238step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10238step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10238step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10238step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10238 raw10238Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw10238 raw10238Labels = mixedMoment B raw10238step0 raw10238step0Labels := by
      have hz : ∀ j, raw10238 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10238step0 = (fun i j => raw10238 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10238step0 raw10238; decide +kernel
      have hl : raw10238step0Labels = raw10238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10238 raw10238Labels permutation434 hz
    mixedMoment B raw10238step0 raw10238step0Labels = mixedMoment B raw10238step1 raw10238step1Labels := by
      have hz : ∀ j, raw10238step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10238step1 = (fun i j => raw10238step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10238step1 raw10238step0; decide +kernel
      have hl : raw10238step1Labels = raw10238step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10238step0 raw10238step0Labels permutation80 hz
    mixedMoment B raw10238step1 raw10238step1Labels = mixedMoment B raw10238step2 raw10238step2Labels := by
      have ha : raw10238step2 = (fun i j => raw10238step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10238step2 raw10238step1; decide +kernel
      have hl : raw10238step2Labels = raw10238step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10238step1 raw10238step1Labels permutation29 permutation7
    mixedMoment B raw10238step2 raw10238step2Labels = mixedMoment B raw10238step3 raw10238step3Labels := by
      have ha : raw10238step3 = raw10238step2 := by apply Matrix.ext; unfold raw10238step3 raw10238step2; decide +kernel
      have hl : raw10238step2Labels = labelEmbedding10 ∘ raw10238step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10238step2 raw10238step2Labels raw10238step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw10239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![2, 1, -3]]
def raw10239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10239step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10239step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw10239step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10239step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10239 raw10239Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw10239 raw10239Labels = mixedMoment B raw10239step0 raw10239step0Labels := by
      have hz : ∀ j, raw10239 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw10239step0 = (fun i j => raw10239 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw10239step0 raw10239; decide +kernel
      have hl : raw10239step0Labels = raw10239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10239 raw10239Labels permutation434 hz
    mixedMoment B raw10239step0 raw10239step0Labels = mixedMoment B raw10239step1 raw10239step1Labels := by
      have hz : ∀ j, raw10239step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw10239step1 = (fun i j => raw10239step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw10239step1 raw10239step0; decide +kernel
      have hl : raw10239step1Labels = raw10239step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10239step0 raw10239step0Labels permutation56 hz
    mixedMoment B raw10239step1 raw10239step1Labels = mixedMoment B raw10239step2 raw10239step2Labels := by
      have ha : raw10239step2 = (fun i j => raw10239step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10239step2 raw10239step1; decide +kernel
      have hl : raw10239step2Labels = raw10239step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10239step1 raw10239step1Labels permutation29 permutation7
    mixedMoment B raw10239step2 raw10239step2Labels = mixedMoment B raw10239step3 raw10239step3Labels := by
      have ha : raw10239step3 = raw10239step2 := by apply Matrix.ext; unfold raw10239step3 raw10239step2; decide +kernel
      have hl : raw10239step2Labels = labelEmbedding10 ∘ raw10239step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10239step2 raw10239step2Labels raw10239step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
