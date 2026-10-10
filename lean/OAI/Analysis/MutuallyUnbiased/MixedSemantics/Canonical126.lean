import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16128 raw16128Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw16128 raw16128Labels = mixedMoment B raw16128step0 raw16128step0Labels := by
      have ha : raw16128step0 = (fun i j => raw16128 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16128step0 raw16128; decide +kernel
      have hl : raw16128step0Labels = raw16128Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16128 raw16128Labels permutation646 permutation2
    mixedMoment B raw16128step0 raw16128step0Labels = mixedMoment B raw16128step1 raw16128step1Labels := by
      have ha : raw16128step1 = -raw16128step0 := by apply Matrix.ext; change ∀ i j, raw16128step1 i j = -(raw16128step0 i j); unfold raw16128step1 raw16128step0; decide +kernel
      have hl : raw16128step1Labels = raw16128step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw16129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw16129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16129 raw16129Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw16129 raw16129Labels = mixedMoment B raw16129step0 raw16129step0Labels := by
      have ha : raw16129step0 = (fun i j => raw16129 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16129step0 raw16129; decide +kernel
      have hl : raw16129step0Labels = raw16129Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16129 raw16129Labels permutation158 permutation2
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw16130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16130Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16130 raw16130Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw16130 raw16130Labels = mixedMoment B raw16130step0 raw16130step0Labels := by
      have ha : raw16130step0 = (fun i j => raw16130 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16130step0 raw16130; decide +kernel
      have hl : raw16130step0Labels = raw16130Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16130 raw16130Labels permutation687 permutation2
    mixedMoment B raw16130step0 raw16130step0Labels = mixedMoment B raw16130step1 raw16130step1Labels := by
      have ha : raw16130step1 = -raw16130step0 := by apply Matrix.ext; change ∀ i j, raw16130step1 i j = -(raw16130step0 i j); unfold raw16130step1 raw16130step0; decide +kernel
      have hl : raw16130step1Labels = raw16130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw16131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16131 raw16131Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw16131 raw16131Labels = mixedMoment B raw16131step0 raw16131step0Labels := by
      have ha : raw16131step0 = (fun i j => raw16131 (permutation320 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16131step0 raw16131; decide +kernel
      have hl : raw16131step0Labels = raw16131Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16131 raw16131Labels permutation320 permutation4
    _ = mixedMoment B node3783 node3783Labels := by rfl

def raw16132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16132 raw16132Labels = mixedMoment B node3935 node3935Labels := by
  calc
    mixedMoment B raw16132 raw16132Labels = mixedMoment B raw16132step0 raw16132step0Labels := by
      have ha : raw16132step0 = (fun i j => raw16132 (permutation359 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16132step0 raw16132; decide +kernel
      have hl : raw16132step0Labels = raw16132Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16132 raw16132Labels permutation359 permutation4
    mixedMoment B raw16132step0 raw16132step0Labels = mixedMoment B raw16132step1 raw16132step1Labels := by
      have ha : raw16132step1 = -raw16132step0 := by apply Matrix.ext; change ∀ i j, raw16132step1 i j = -(raw16132step0 i j); unfold raw16132step1 raw16132step0; decide +kernel
      have hl : raw16132step1Labels = raw16132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3935 node3935Labels := by rfl

def raw16133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16133 raw16133Labels = mixedMoment B node3924 node3924Labels := by
  calc
    mixedMoment B raw16133 raw16133Labels = mixedMoment B raw16133step0 raw16133step0Labels := by
      have ha : raw16133step0 = (fun i j => raw16133 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16133step0 raw16133; decide +kernel
      have hl : raw16133step0Labels = raw16133Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16133 raw16133Labels permutation589 permutation2
    mixedMoment B raw16133step0 raw16133step0Labels = mixedMoment B raw16133step1 raw16133step1Labels := by
      have ha : raw16133step1 = -raw16133step0 := by apply Matrix.ext; change ∀ i j, raw16133step1 i j = -(raw16133step0 i j); unfold raw16133step1 raw16133step0; decide +kernel
      have hl : raw16133step1Labels = raw16133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3924 node3924Labels := by rfl

def raw16134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw16134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16134 raw16134Labels = mixedMoment B node2935 node2935Labels := by
  calc
    mixedMoment B raw16134 raw16134Labels = mixedMoment B raw16134step0 raw16134step0Labels := by
      have ha : raw16134step0 = (fun i j => raw16134 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16134step0 raw16134; decide +kernel
      have hl : raw16134step0Labels = raw16134Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16134 raw16134Labels permutation688 permutation2
    mixedMoment B raw16134step0 raw16134step0Labels = mixedMoment B raw16134step1 raw16134step1Labels := by
      have ha : raw16134step1 = -raw16134step0 := by apply Matrix.ext; change ∀ i j, raw16134step1 i j = -(raw16134step0 i j); unfold raw16134step1 raw16134step0; decide +kernel
      have hl : raw16134step1Labels = raw16134step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2935 node2935Labels := by rfl

def raw16135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![2, -1, -1]]
def raw16135Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16135step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16135 raw16135Labels = mixedMoment B node3922 node3922Labels := by
  calc
    mixedMoment B raw16135 raw16135Labels = mixedMoment B raw16135step0 raw16135step0Labels := by
      have ha : raw16135step0 = (fun i j => raw16135 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16135step0 raw16135; decide +kernel
      have hl : raw16135step0Labels = raw16135Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16135 raw16135Labels permutation584 permutation2
    mixedMoment B raw16135step0 raw16135step0Labels = mixedMoment B raw16135step1 raw16135step1Labels := by
      have ha : raw16135step1 = -raw16135step0 := by apply Matrix.ext; change ∀ i j, raw16135step1 i j = -(raw16135step0 i j); unfold raw16135step1 raw16135step0; decide +kernel
      have hl : raw16135step1Labels = raw16135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3922 node3922Labels := by rfl

def raw16136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw16136Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16136 raw16136Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw16136 raw16136Labels = mixedMoment B raw16136step0 raw16136step0Labels := by
      have ha : raw16136step0 = (fun i j => raw16136 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16136step0 raw16136; decide +kernel
      have hl : raw16136step0Labels = raw16136Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16136 raw16136Labels permutation584 permutation2
    mixedMoment B raw16136step0 raw16136step0Labels = mixedMoment B raw16136step1 raw16136step1Labels := by
      have ha : raw16136step1 = -raw16136step0 := by apply Matrix.ext; change ∀ i j, raw16136step1 i j = -(raw16136step0 i j); unfold raw16136step1 raw16136step0; decide +kernel
      have hl : raw16136step1Labels = raw16136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw16137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16137Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw16137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16137 raw16137Labels = mixedMoment B node4008 node4008Labels := by
  calc
    mixedMoment B raw16137 raw16137Labels = mixedMoment B raw16137step0 raw16137step0Labels := by
      have ha : raw16137step0 = (fun i j => raw16137 (permutation645 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16137step0 raw16137; decide +kernel
      have hl : raw16137step0Labels = raw16137Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16137 raw16137Labels permutation645 permutation2
    mixedMoment B raw16137step0 raw16137step0Labels = mixedMoment B raw16137step1 raw16137step1Labels := by
      have ha : raw16137step1 = -raw16137step0 := by apply Matrix.ext; change ∀ i j, raw16137step1 i j = -(raw16137step0 i j); unfold raw16137step1 raw16137step0; decide +kernel
      have hl : raw16137step1Labels = raw16137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4008 node4008Labels := by rfl

def raw16138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16138Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16138 raw16138Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw16138 raw16138Labels = mixedMoment B raw16138step0 raw16138step0Labels := by
      have ha : raw16138step0 = (fun i j => raw16138 (permutation319 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16138step0 raw16138; decide +kernel
      have hl : raw16138step0Labels = raw16138Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16138 raw16138Labels permutation319 permutation4
    _ = mixedMoment B node3789 node3789Labels := by rfl

def raw16139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw16139Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16139 raw16139Labels = mixedMoment B node3949 node3949Labels := by
  calc
    mixedMoment B raw16139 raw16139Labels = mixedMoment B raw16139step0 raw16139step0Labels := by
      have ha : raw16139step0 = (fun i j => raw16139 (permutation465 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16139step0 raw16139; decide +kernel
      have hl : raw16139step0Labels = raw16139Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16139 raw16139Labels permutation465 permutation4
    _ = mixedMoment B node3949 node3949Labels := by rfl

def raw16140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw16140Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16140step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16140 raw16140Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw16140 raw16140Labels = mixedMoment B raw16140step0 raw16140step0Labels := by
      have ha : raw16140step0 = (fun i j => raw16140 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16140step0 raw16140; decide +kernel
      have hl : raw16140step0Labels = raw16140Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16140 raw16140Labels permutation646 permutation2
    mixedMoment B raw16140step0 raw16140step0Labels = mixedMoment B raw16140step1 raw16140step1Labels := by
      have ha : raw16140step1 = -raw16140step0 := by apply Matrix.ext; change ∀ i j, raw16140step1 i j = -(raw16140step0 i j); unfold raw16140step1 raw16140step0; decide +kernel
      have hl : raw16140step1Labels = raw16140step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3066 node3066Labels := by rfl

def raw16141 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16141 raw16141Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw16141 raw16141Labels = mixedMoment B raw16141step0 raw16141step0Labels := by
      have ha : raw16141step0 = (fun i j => raw16141 (permutation410 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16141step0 raw16141; decide +kernel
      have hl : raw16141step0Labels = raw16141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16141 raw16141Labels permutation410 permutation3
    mixedMoment B raw16141step0 raw16141step0Labels = mixedMoment B raw16141step1 raw16141step1Labels := by
      have ha : raw16141step1 = raw16141step0 := by apply Matrix.ext; unfold raw16141step1 raw16141step0; decide +kernel
      have hl : raw16141step0Labels = labelEmbedding6 ∘ raw16141step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16141step0 raw16141step0Labels raw16141step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw16142 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16142step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16142 raw16142Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16142 raw16142Labels = mixedMoment B raw16142step0 raw16142step0Labels := by
      have hz : ∀ j, raw16142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16142step0 = (fun i j => raw16142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16142step0 raw16142; decide +kernel
      have hl : raw16142step0Labels = raw16142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16142 raw16142Labels permutation434 hz
    mixedMoment B raw16142step0 raw16142step0Labels = mixedMoment B raw16142step1 raw16142step1Labels := by
      have ha : raw16142step1 = (fun i j => raw16142step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16142step1 raw16142step0; decide +kernel
      have hl : raw16142step1Labels = raw16142step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16142step0 raw16142step0Labels permutation32 permutation7
    mixedMoment B raw16142step1 raw16142step1Labels = mixedMoment B raw16142step2 raw16142step2Labels := by
      have ha : raw16142step2 = raw16142step1 := by apply Matrix.ext; unfold raw16142step2 raw16142step1; decide +kernel
      have hl : raw16142step1Labels = labelEmbedding10 ∘ raw16142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16142step1 raw16142step1Labels raw16142step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw16143 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16143 raw16143Labels = mixedMoment B node5468 node5468Labels := by
  calc
    mixedMoment B raw16143 raw16143Labels = mixedMoment B raw16143step0 raw16143step0Labels := by
      have ha : raw16143step0 = (fun i j => raw16143 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16143step0 raw16143; decide +kernel
      have hl : raw16143step0Labels = raw16143Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16143 raw16143Labels permutation583 permutation2
    _ = mixedMoment B node5468 node5468Labels := by rfl

def raw16144 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16144 raw16144Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw16144 raw16144Labels = mixedMoment B raw16144step0 raw16144step0Labels := by
      have ha : raw16144step0 = (fun i j => raw16144 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16144step0 raw16144; decide +kernel
      have hl : raw16144step0Labels = raw16144Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16144 raw16144Labels permutation681 permutation2
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw16145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw16145step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw16145step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16145step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw16145step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16145 raw16145Labels = mixedMoment B node5091 node5091Labels := by
  calc
    mixedMoment B raw16145 raw16145Labels = mixedMoment B raw16145step0 raw16145step0Labels := by
      have ha : raw16145step0 = (fun i j => raw16145 (permutation321 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16145step0 raw16145; decide +kernel
      have hl : raw16145step0Labels = raw16145Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16145 raw16145Labels permutation321 permutation3
    mixedMoment B raw16145step0 raw16145step0Labels = mixedMoment B raw16145step1 raw16145step1Labels := by
      have ha : raw16145step1 = -raw16145step0 := by apply Matrix.ext; change ∀ i j, raw16145step1 i j = -(raw16145step0 i j); unfold raw16145step1 raw16145step0; decide +kernel
      have hl : raw16145step1Labels = raw16145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16145step1 raw16145step1Labels = mixedMoment B raw16145step2 raw16145step2Labels := by
      have ha : raw16145step2 = raw16145step1 := by apply Matrix.ext; unfold raw16145step2 raw16145step1; decide +kernel
      have hl : raw16145step1Labels = labelEmbedding6 ∘ raw16145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16145step1 raw16145step1Labels raw16145step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5091 node5091Labels := by rfl

def raw16146 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16146step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16146step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16146step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16146 raw16146Labels = mixedMoment B node5082 node5082Labels := by
  calc
    mixedMoment B raw16146 raw16146Labels = mixedMoment B raw16146step0 raw16146step0Labels := by
      have ha : raw16146step0 = (fun i j => raw16146 (permutation310 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16146step0 raw16146; decide +kernel
      have hl : raw16146step0Labels = raw16146Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16146 raw16146Labels permutation310 permutation3
    mixedMoment B raw16146step0 raw16146step0Labels = mixedMoment B raw16146step1 raw16146step1Labels := by
      have ha : raw16146step1 = -raw16146step0 := by apply Matrix.ext; change ∀ i j, raw16146step1 i j = -(raw16146step0 i j); unfold raw16146step1 raw16146step0; decide +kernel
      have hl : raw16146step1Labels = raw16146step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16146step1 raw16146step1Labels = mixedMoment B raw16146step2 raw16146step2Labels := by
      have ha : raw16146step2 = raw16146step1 := by apply Matrix.ext; unfold raw16146step2 raw16146step1; decide +kernel
      have hl : raw16146step1Labels = labelEmbedding6 ∘ raw16146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16146step1 raw16146step1Labels raw16146step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5082 node5082Labels := by rfl

def raw16147 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16147step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16147step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16147step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16147step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16147 raw16147Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw16147 raw16147Labels = mixedMoment B raw16147step0 raw16147step0Labels := by
      have hz : ∀ j, raw16147 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16147step0 = (fun i j => raw16147 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16147step0 raw16147; decide +kernel
      have hl : raw16147step0Labels = raw16147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16147 raw16147Labels permutation434 hz
    mixedMoment B raw16147step0 raw16147step0Labels = mixedMoment B raw16147step1 raw16147step1Labels := by
      have ha : raw16147step1 = (fun i j => raw16147step0 (permutation61 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16147step1 raw16147step0; decide +kernel
      have hl : raw16147step1Labels = raw16147step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16147step0 raw16147step0Labels permutation61 permutation3
    mixedMoment B raw16147step1 raw16147step1Labels = mixedMoment B raw16147step2 raw16147step2Labels := by
      have ha : raw16147step2 = -raw16147step1 := by apply Matrix.ext; change ∀ i j, raw16147step2 i j = -(raw16147step1 i j); unfold raw16147step2 raw16147step1; decide +kernel
      have hl : raw16147step2Labels = raw16147step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16147step2 raw16147step2Labels = mixedMoment B raw16147step3 raw16147step3Labels := by
      have ha : raw16147step3 = raw16147step2 := by apply Matrix.ext; unfold raw16147step3 raw16147step2; decide +kernel
      have hl : raw16147step2Labels = labelEmbedding6 ∘ raw16147step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16147step2 raw16147step2Labels raw16147step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw16148 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw16148step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16148step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16148step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16148step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16148 raw16148Labels = mixedMoment B node5083 node5083Labels := by
  calc
    mixedMoment B raw16148 raw16148Labels = mixedMoment B raw16148step0 raw16148step0Labels := by
      have ha : raw16148step0 = (fun i j => raw16148 (permutation309 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16148step0 raw16148; decide +kernel
      have hl : raw16148step0Labels = raw16148Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16148 raw16148Labels permutation309 permutation3
    mixedMoment B raw16148step0 raw16148step0Labels = mixedMoment B raw16148step1 raw16148step1Labels := by
      have ha : raw16148step1 = -raw16148step0 := by apply Matrix.ext; change ∀ i j, raw16148step1 i j = -(raw16148step0 i j); unfold raw16148step1 raw16148step0; decide +kernel
      have hl : raw16148step1Labels = raw16148step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16148step1 raw16148step1Labels = mixedMoment B raw16148step2 raw16148step2Labels := by
      have ha : raw16148step2 = raw16148step1 := by apply Matrix.ext; unfold raw16148step2 raw16148step1; decide +kernel
      have hl : raw16148step1Labels = labelEmbedding6 ∘ raw16148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16148step1 raw16148step1Labels raw16148step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5083 node5083Labels := by rfl

def raw16149 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16149step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16149step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16149step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16149 raw16149Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw16149 raw16149Labels = mixedMoment B raw16149step0 raw16149step0Labels := by
      have ha : raw16149step0 = (fun i j => raw16149 (permutation307 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16149step0 raw16149; decide +kernel
      have hl : raw16149step0Labels = raw16149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16149 raw16149Labels permutation307 permutation3
    mixedMoment B raw16149step0 raw16149step0Labels = mixedMoment B raw16149step1 raw16149step1Labels := by
      have ha : raw16149step1 = -raw16149step0 := by apply Matrix.ext; change ∀ i j, raw16149step1 i j = -(raw16149step0 i j); unfold raw16149step1 raw16149step0; decide +kernel
      have hl : raw16149step1Labels = raw16149step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16149step1 raw16149step1Labels = mixedMoment B raw16149step2 raw16149step2Labels := by
      have ha : raw16149step2 = raw16149step1 := by apply Matrix.ext; unfold raw16149step2 raw16149step1; decide +kernel
      have hl : raw16149step1Labels = labelEmbedding6 ∘ raw16149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16149step1 raw16149step1Labels raw16149step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw16150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16150step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16150step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16150step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16150step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16150 raw16150Labels = mixedMoment B node5146 node5146Labels := by
  calc
    mixedMoment B raw16150 raw16150Labels = mixedMoment B raw16150step0 raw16150step0Labels := by
      have ha : raw16150step0 = (fun i j => raw16150 (permutation189 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16150step0 raw16150; decide +kernel
      have hl : raw16150step0Labels = raw16150Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16150 raw16150Labels permutation189 permutation4
    mixedMoment B raw16150step0 raw16150step0Labels = mixedMoment B raw16150step1 raw16150step1Labels := by
      have ha : raw16150step1 = -raw16150step0 := by apply Matrix.ext; change ∀ i j, raw16150step1 i j = -(raw16150step0 i j); unfold raw16150step1 raw16150step0; decide +kernel
      have hl : raw16150step1Labels = raw16150step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16150step1 raw16150step1Labels = mixedMoment B raw16150step2 raw16150step2Labels := by
      have ha : raw16150step2 = raw16150step1 := by apply Matrix.ext; unfold raw16150step2 raw16150step1; decide +kernel
      have hl : raw16150step1Labels = labelEmbedding7 ∘ raw16150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16150step1 raw16150step1Labels raw16150step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5146 node5146Labels := by rfl

def raw16151 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16151step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16151step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16151step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16151step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16151 raw16151Labels = mixedMoment B node5357 node5357Labels := by
  calc
    mixedMoment B raw16151 raw16151Labels = mixedMoment B raw16151step0 raw16151step0Labels := by
      have ha : raw16151step0 = (fun i j => raw16151 (permutation456 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16151step0 raw16151; decide +kernel
      have hl : raw16151step0Labels = raw16151Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16151 raw16151Labels permutation456 permutation3
    mixedMoment B raw16151step0 raw16151step0Labels = mixedMoment B raw16151step1 raw16151step1Labels := by
      have ha : raw16151step1 = -raw16151step0 := by apply Matrix.ext; change ∀ i j, raw16151step1 i j = -(raw16151step0 i j); unfold raw16151step1 raw16151step0; decide +kernel
      have hl : raw16151step1Labels = raw16151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16151step1 raw16151step1Labels = mixedMoment B raw16151step2 raw16151step2Labels := by
      have ha : raw16151step2 = raw16151step1 := by apply Matrix.ext; unfold raw16151step2 raw16151step1; decide +kernel
      have hl : raw16151step1Labels = labelEmbedding6 ∘ raw16151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16151step1 raw16151step1Labels raw16151step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5357 node5357Labels := by rfl

def raw16152 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw16152step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16152step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16152step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16152step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16152 raw16152Labels = mixedMoment B node5358 node5358Labels := by
  calc
    mixedMoment B raw16152 raw16152Labels = mixedMoment B raw16152step0 raw16152step0Labels := by
      have ha : raw16152step0 = (fun i j => raw16152 (permutation455 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16152step0 raw16152; decide +kernel
      have hl : raw16152step0Labels = raw16152Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16152 raw16152Labels permutation455 permutation3
    mixedMoment B raw16152step0 raw16152step0Labels = mixedMoment B raw16152step1 raw16152step1Labels := by
      have ha : raw16152step1 = -raw16152step0 := by apply Matrix.ext; change ∀ i j, raw16152step1 i j = -(raw16152step0 i j); unfold raw16152step1 raw16152step0; decide +kernel
      have hl : raw16152step1Labels = raw16152step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16152step1 raw16152step1Labels = mixedMoment B raw16152step2 raw16152step2Labels := by
      have ha : raw16152step2 = raw16152step1 := by apply Matrix.ext; unfold raw16152step2 raw16152step1; decide +kernel
      have hl : raw16152step1Labels = labelEmbedding6 ∘ raw16152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16152step1 raw16152step1Labels raw16152step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5358 node5358Labels := by rfl

def raw16153 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16153step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16153step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16153 raw16153Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw16153 raw16153Labels = mixedMoment B raw16153step0 raw16153step0Labels := by
      have ha : raw16153step0 = (fun i j => raw16153 (permutation453 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16153step0 raw16153; decide +kernel
      have hl : raw16153step0Labels = raw16153Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16153 raw16153Labels permutation453 permutation3
    mixedMoment B raw16153step0 raw16153step0Labels = mixedMoment B raw16153step1 raw16153step1Labels := by
      have ha : raw16153step1 = -raw16153step0 := by apply Matrix.ext; change ∀ i j, raw16153step1 i j = -(raw16153step0 i j); unfold raw16153step1 raw16153step0; decide +kernel
      have hl : raw16153step1Labels = raw16153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16153step1 raw16153step1Labels = mixedMoment B raw16153step2 raw16153step2Labels := by
      have ha : raw16153step2 = raw16153step1 := by apply Matrix.ext; unfold raw16153step2 raw16153step1; decide +kernel
      have hl : raw16153step1Labels = labelEmbedding6 ∘ raw16153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16153step1 raw16153step1Labels raw16153step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw16154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16154step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16154step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16154step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16154 raw16154Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw16154 raw16154Labels = mixedMoment B raw16154step0 raw16154step0Labels := by
      have ha : raw16154step0 = (fun i j => raw16154 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16154step0 raw16154; decide +kernel
      have hl : raw16154step0Labels = raw16154Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16154 raw16154Labels permutation176 permutation4
    mixedMoment B raw16154step0 raw16154step0Labels = mixedMoment B raw16154step1 raw16154step1Labels := by
      have ha : raw16154step1 = -raw16154step0 := by apply Matrix.ext; change ∀ i j, raw16154step1 i j = -(raw16154step0 i j); unfold raw16154step1 raw16154step0; decide +kernel
      have hl : raw16154step1Labels = raw16154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16154step1 raw16154step1Labels = mixedMoment B raw16154step2 raw16154step2Labels := by
      have ha : raw16154step2 = raw16154step1 := by apply Matrix.ext; unfold raw16154step2 raw16154step1; decide +kernel
      have hl : raw16154step1Labels = labelEmbedding7 ∘ raw16154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16154step1 raw16154step1Labels raw16154step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw16155 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16155step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16155step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16155step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16155 raw16155Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw16155 raw16155Labels = mixedMoment B raw16155step0 raw16155step0Labels := by
      have ha : raw16155step0 = (fun i j => raw16155 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16155step0 raw16155; decide +kernel
      have hl : raw16155step0Labels = raw16155Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16155 raw16155Labels permutation176 permutation4
    mixedMoment B raw16155step0 raw16155step0Labels = mixedMoment B raw16155step1 raw16155step1Labels := by
      have ha : raw16155step1 = -raw16155step0 := by apply Matrix.ext; change ∀ i j, raw16155step1 i j = -(raw16155step0 i j); unfold raw16155step1 raw16155step0; decide +kernel
      have hl : raw16155step1Labels = raw16155step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16155step1 raw16155step1Labels = mixedMoment B raw16155step2 raw16155step2Labels := by
      have ha : raw16155step2 = raw16155step1 := by apply Matrix.ext; unfold raw16155step2 raw16155step1; decide +kernel
      have hl : raw16155step1Labels = labelEmbedding7 ∘ raw16155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16155step1 raw16155step1Labels raw16155step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5382 node5382Labels := by rfl

def raw16156 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16156step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16156step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16156step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16156step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16156 raw16156Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw16156 raw16156Labels = mixedMoment B raw16156step0 raw16156step0Labels := by
      have hz : ∀ j, raw16156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16156step0 = (fun i j => raw16156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16156step0 raw16156; decide +kernel
      have hl : raw16156step0Labels = raw16156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16156 raw16156Labels permutation434 hz
    mixedMoment B raw16156step0 raw16156step0Labels = mixedMoment B raw16156step1 raw16156step1Labels := by
      have ha : raw16156step1 = (fun i j => raw16156step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16156step1 raw16156step0; decide +kernel
      have hl : raw16156step1Labels = raw16156step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16156step0 raw16156step0Labels permutation38 permutation4
    mixedMoment B raw16156step1 raw16156step1Labels = mixedMoment B raw16156step2 raw16156step2Labels := by
      have ha : raw16156step2 = -raw16156step1 := by apply Matrix.ext; change ∀ i j, raw16156step2 i j = -(raw16156step1 i j); unfold raw16156step2 raw16156step1; decide +kernel
      have hl : raw16156step2Labels = raw16156step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16156step2 raw16156step2Labels = mixedMoment B raw16156step3 raw16156step3Labels := by
      have ha : raw16156step3 = raw16156step2 := by apply Matrix.ext; unfold raw16156step3 raw16156step2; decide +kernel
      have hl : raw16156step2Labels = labelEmbedding7 ∘ raw16156step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16156step2 raw16156step2Labels raw16156step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw16157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16157step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16157step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16157step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16157 raw16157Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw16157 raw16157Labels = mixedMoment B raw16157step0 raw16157step0Labels := by
      have ha : raw16157step0 = (fun i j => raw16157 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16157step0 raw16157; decide +kernel
      have hl : raw16157step0Labels = raw16157Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16157 raw16157Labels permutation188 permutation4
    mixedMoment B raw16157step0 raw16157step0Labels = mixedMoment B raw16157step1 raw16157step1Labels := by
      have ha : raw16157step1 = -raw16157step0 := by apply Matrix.ext; change ∀ i j, raw16157step1 i j = -(raw16157step0 i j); unfold raw16157step1 raw16157step0; decide +kernel
      have hl : raw16157step1Labels = raw16157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16157step1 raw16157step1Labels = mixedMoment B raw16157step2 raw16157step2Labels := by
      have ha : raw16157step2 = raw16157step1 := by apply Matrix.ext; unfold raw16157step2 raw16157step1; decide +kernel
      have hl : raw16157step1Labels = labelEmbedding7 ∘ raw16157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16157step1 raw16157step1Labels raw16157step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw16158 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16158step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16158step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16158step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16158step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16158 raw16158Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw16158 raw16158Labels = mixedMoment B raw16158step0 raw16158step0Labels := by
      have ha : raw16158step0 = (fun i j => raw16158 (permutation358 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16158step0 raw16158; decide +kernel
      have hl : raw16158step0Labels = raw16158Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16158 raw16158Labels permutation358 permutation5
    mixedMoment B raw16158step0 raw16158step0Labels = mixedMoment B raw16158step1 raw16158step1Labels := by
      have ha : raw16158step1 = -raw16158step0 := by apply Matrix.ext; change ∀ i j, raw16158step1 i j = -(raw16158step0 i j); unfold raw16158step1 raw16158step0; decide +kernel
      have hl : raw16158step1Labels = raw16158step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16158step1 raw16158step1Labels = mixedMoment B raw16158step2 raw16158step2Labels := by
      have ha : raw16158step2 = raw16158step1 := by apply Matrix.ext; unfold raw16158step2 raw16158step1; decide +kernel
      have hl : raw16158step1Labels = labelEmbedding8 ∘ raw16158step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16158step1 raw16158step1Labels raw16158step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw16159 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16159step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16159step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16159step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16159step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16159 raw16159Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw16159 raw16159Labels = mixedMoment B raw16159step0 raw16159step0Labels := by
      have hz : ∀ j, raw16159 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16159step0 = (fun i j => raw16159 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16159step0 raw16159; decide +kernel
      have hl : raw16159step0Labels = raw16159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16159 raw16159Labels permutation434 hz
    mixedMoment B raw16159step0 raw16159step0Labels = mixedMoment B raw16159step1 raw16159step1Labels := by
      have ha : raw16159step1 = (fun i j => raw16159step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16159step1 raw16159step0; decide +kernel
      have hl : raw16159step1Labels = raw16159step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16159step0 raw16159step0Labels permutation40 permutation4
    mixedMoment B raw16159step1 raw16159step1Labels = mixedMoment B raw16159step2 raw16159step2Labels := by
      have ha : raw16159step2 = -raw16159step1 := by apply Matrix.ext; change ∀ i j, raw16159step2 i j = -(raw16159step1 i j); unfold raw16159step2 raw16159step1; decide +kernel
      have hl : raw16159step2Labels = raw16159step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16159step2 raw16159step2Labels = mixedMoment B raw16159step3 raw16159step3Labels := by
      have ha : raw16159step3 = raw16159step2 := by apply Matrix.ext; unfold raw16159step3 raw16159step2; decide +kernel
      have hl : raw16159step2Labels = labelEmbedding7 ∘ raw16159step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16159step2 raw16159step2Labels raw16159step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw16160 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16160step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16160 raw16160Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw16160 raw16160Labels = mixedMoment B raw16160step0 raw16160step0Labels := by
      have ha : raw16160step0 = (fun i j => raw16160 (permutation654 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16160step0 raw16160; decide +kernel
      have hl : raw16160step0Labels = raw16160Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16160 raw16160Labels permutation654 permutation4
    mixedMoment B raw16160step0 raw16160step0Labels = mixedMoment B raw16160step1 raw16160step1Labels := by
      have ha : raw16160step1 = raw16160step0 := by apply Matrix.ext; unfold raw16160step1 raw16160step0; decide +kernel
      have hl : raw16160step0Labels = labelEmbedding7 ∘ raw16160step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16160step0 raw16160step0Labels raw16160step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5420 node5420Labels := by rfl

def raw16161 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16161 raw16161Labels = mixedMoment B node3989 node3989Labels := by
  calc
    mixedMoment B raw16161 raw16161Labels = mixedMoment B raw16161step0 raw16161step0Labels := by
      have ha : raw16161step0 = (fun i j => raw16161 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16161step0 raw16161; decide +kernel
      have hl : raw16161step0Labels = raw16161Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16161 raw16161Labels permutation152 permutation6
    _ = mixedMoment B node3989 node3989Labels := by rfl

def raw16162 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16162 raw16162Labels = mixedMoment B node3827 node3827Labels := by
  calc
    mixedMoment B raw16162 raw16162Labels = mixedMoment B raw16162step0 raw16162step0Labels := by
      have ha : raw16162step0 = (fun i j => raw16162 (permutation410 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16162step0 raw16162; decide +kernel
      have hl : raw16162step0Labels = raw16162Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16162 raw16162Labels permutation410 permutation3
    _ = mixedMoment B node3827 node3827Labels := by rfl

def raw16163 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw16163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16163step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16163 raw16163Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw16163 raw16163Labels = mixedMoment B raw16163step0 raw16163step0Labels := by
      have hz : ∀ j, raw16163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16163step0 = (fun i j => raw16163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16163step0 raw16163; decide +kernel
      have hl : raw16163step0Labels = raw16163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16163 raw16163Labels permutation434 hz
    mixedMoment B raw16163step0 raw16163step0Labels = mixedMoment B raw16163step1 raw16163step1Labels := by
      have ha : raw16163step1 = (fun i j => raw16163step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16163step1 raw16163step0; decide +kernel
      have hl : raw16163step1Labels = raw16163step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16163step0 raw16163step0Labels permutation151 permutation6
    mixedMoment B raw16163step1 raw16163step1Labels = mixedMoment B raw16163step2 raw16163step2Labels := by
      have ha : raw16163step2 = -raw16163step1 := by apply Matrix.ext; change ∀ i j, raw16163step2 i j = -(raw16163step1 i j); unfold raw16163step2 raw16163step1; decide +kernel
      have hl : raw16163step2Labels = raw16163step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw16164 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16164 raw16164Labels = mixedMoment B node3968 node3968Labels := by
  calc
    mixedMoment B raw16164 raw16164Labels = mixedMoment B raw16164step0 raw16164step0Labels := by
      have ha : raw16164step0 = (fun i j => raw16164 (permutation548 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16164step0 raw16164; decide +kernel
      have hl : raw16164step0Labels = raw16164Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16164 raw16164Labels permutation548 permutation3
    _ = mixedMoment B node3968 node3968Labels := by rfl

def raw16165 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16165 raw16165Labels = mixedMoment B node3970 node3970Labels := by
  calc
    mixedMoment B raw16165 raw16165Labels = mixedMoment B raw16165step0 raw16165step0Labels := by
      have ha : raw16165step0 = (fun i j => raw16165 (permutation307 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16165step0 raw16165; decide +kernel
      have hl : raw16165step0Labels = raw16165Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16165 raw16165Labels permutation307 permutation3
    mixedMoment B raw16165step0 raw16165step0Labels = mixedMoment B raw16165step1 raw16165step1Labels := by
      have ha : raw16165step1 = -raw16165step0 := by apply Matrix.ext; change ∀ i j, raw16165step1 i j = -(raw16165step0 i j); unfold raw16165step1 raw16165step0; decide +kernel
      have hl : raw16165step1Labels = raw16165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3970 node3970Labels := by rfl

def raw16166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw16166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw16166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16166 raw16166Labels = mixedMoment B node2500 node2500Labels := by
  calc
    mixedMoment B raw16166 raw16166Labels = mixedMoment B raw16166step0 raw16166step0Labels := by
      have ha : raw16166step0 = (fun i j => raw16166 (permutation321 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16166step0 raw16166; decide +kernel
      have hl : raw16166step0Labels = raw16166Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16166 raw16166Labels permutation321 permutation3
    mixedMoment B raw16166step0 raw16166step0Labels = mixedMoment B raw16166step1 raw16166step1Labels := by
      have ha : raw16166step1 = -raw16166step0 := by apply Matrix.ext; change ∀ i j, raw16166step1 i j = -(raw16166step0 i j); unfold raw16166step1 raw16166step0; decide +kernel
      have hl : raw16166step1Labels = raw16166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2500 node2500Labels := by rfl

def raw16167 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16167 raw16167Labels = mixedMoment B node2490 node2490Labels := by
  calc
    mixedMoment B raw16167 raw16167Labels = mixedMoment B raw16167step0 raw16167step0Labels := by
      have ha : raw16167step0 = (fun i j => raw16167 (permutation310 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16167step0 raw16167; decide +kernel
      have hl : raw16167step0Labels = raw16167Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16167 raw16167Labels permutation310 permutation3
    mixedMoment B raw16167step0 raw16167step0Labels = mixedMoment B raw16167step1 raw16167step1Labels := by
      have ha : raw16167step1 = -raw16167step0 := by apply Matrix.ext; change ∀ i j, raw16167step1 i j = -(raw16167step0 i j); unfold raw16167step1 raw16167step0; decide +kernel
      have hl : raw16167step1Labels = raw16167step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2490 node2490Labels := by rfl

def raw16168 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16168 raw16168Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw16168 raw16168Labels = mixedMoment B raw16168step0 raw16168step0Labels := by
      have hz : ∀ j, raw16168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16168step0 = (fun i j => raw16168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16168step0 raw16168; decide +kernel
      have hl : raw16168step0Labels = raw16168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16168 raw16168Labels permutation434 hz
    mixedMoment B raw16168step0 raw16168step0Labels = mixedMoment B raw16168step1 raw16168step1Labels := by
      have ha : raw16168step1 = (fun i j => raw16168step0 (permutation61 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16168step1 raw16168step0; decide +kernel
      have hl : raw16168step1Labels = raw16168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16168step0 raw16168step0Labels permutation61 permutation3
    mixedMoment B raw16168step1 raw16168step1Labels = mixedMoment B raw16168step2 raw16168step2Labels := by
      have ha : raw16168step2 = -raw16168step1 := by apply Matrix.ext; change ∀ i j, raw16168step2 i j = -(raw16168step1 i j); unfold raw16168step2 raw16168step1; decide +kernel
      have hl : raw16168step2Labels = raw16168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw16169 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw16169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16169 raw16169Labels = mixedMoment B node2491 node2491Labels := by
  calc
    mixedMoment B raw16169 raw16169Labels = mixedMoment B raw16169step0 raw16169step0Labels := by
      have ha : raw16169step0 = (fun i j => raw16169 (permutation309 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16169step0 raw16169; decide +kernel
      have hl : raw16169step0Labels = raw16169Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16169 raw16169Labels permutation309 permutation3
    mixedMoment B raw16169step0 raw16169step0Labels = mixedMoment B raw16169step1 raw16169step1Labels := by
      have ha : raw16169step1 = -raw16169step0 := by apply Matrix.ext; change ∀ i j, raw16169step1 i j = -(raw16169step0 i j); unfold raw16169step1 raw16169step0; decide +kernel
      have hl : raw16169step1Labels = raw16169step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2491 node2491Labels := by rfl

def raw16170 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16170 raw16170Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw16170 raw16170Labels = mixedMoment B raw16170step0 raw16170step0Labels := by
      have ha : raw16170step0 = (fun i j => raw16170 (permutation307 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16170step0 raw16170; decide +kernel
      have hl : raw16170step0Labels = raw16170Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16170 raw16170Labels permutation307 permutation3
    mixedMoment B raw16170step0 raw16170step0Labels = mixedMoment B raw16170step1 raw16170step1Labels := by
      have ha : raw16170step1 = -raw16170step0 := by apply Matrix.ext; change ∀ i j, raw16170step1 i j = -(raw16170step0 i j); unfold raw16170step1 raw16170step0; decide +kernel
      have hl : raw16170step1Labels = raw16170step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw16171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16171 raw16171Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw16171 raw16171Labels = mixedMoment B raw16171step0 raw16171step0Labels := by
      have hz : ∀ j, raw16171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16171step0 = (fun i j => raw16171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16171step0 raw16171; decide +kernel
      have hl : raw16171step0Labels = raw16171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16171 raw16171Labels permutation346 hz
    mixedMoment B raw16171step0 raw16171step0Labels = mixedMoment B raw16171step1 raw16171step1Labels := by
      have ha : raw16171step1 = (fun i j => raw16171step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16171step1 raw16171step0; decide +kernel
      have hl : raw16171step1Labels = raw16171step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16171step0 raw16171step0Labels permutation32 permutation6
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw16172 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16172step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16172 raw16172Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw16172 raw16172Labels = mixedMoment B raw16172step0 raw16172step0Labels := by
      have hz : ∀ j, raw16172 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16172step0 = (fun i j => raw16172 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16172step0 raw16172; decide +kernel
      have hl : raw16172step0Labels = raw16172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16172 raw16172Labels permutation434 hz
    mixedMoment B raw16172step0 raw16172step0Labels = mixedMoment B raw16172step1 raw16172step1Labels := by
      have hz : ∀ j, raw16172step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16172step1 = (fun i j => raw16172step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16172step1 raw16172step0; decide +kernel
      have hl : raw16172step1Labels = raw16172step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16172step0 raw16172step0Labels permutation80 hz
    mixedMoment B raw16172step1 raw16172step1Labels = mixedMoment B raw16172step2 raw16172step2Labels := by
      have ha : raw16172step2 = (fun i j => raw16172step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16172step2 raw16172step1; decide +kernel
      have hl : raw16172step2Labels = raw16172step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16172step1 raw16172step1Labels permutation8 permutation6
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw16173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16173 raw16173Labels = mixedMoment B node3560 node3560Labels := by
  calc
    mixedMoment B raw16173 raw16173Labels = mixedMoment B raw16173step0 raw16173step0Labels := by
      have ha : raw16173step0 = (fun i j => raw16173 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16173step0 raw16173; decide +kernel
      have hl : raw16173step0Labels = raw16173Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16173 raw16173Labels permutation152 permutation6
    _ = mixedMoment B node3560 node3560Labels := by rfl

def raw16174 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16174 raw16174Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw16174 raw16174Labels = mixedMoment B raw16174step0 raw16174step0Labels := by
      have ha : raw16174step0 = (fun i j => raw16174 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16174step0 raw16174; decide +kernel
      have hl : raw16174step0Labels = raw16174Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16174 raw16174Labels permutation152 permutation6
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw16175 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16175 raw16175Labels = mixedMoment B node3695 node3695Labels := by
  calc
    mixedMoment B raw16175 raw16175Labels = mixedMoment B raw16175step0 raw16175step0Labels := by
      have ha : raw16175step0 = (fun i j => raw16175 (permutation456 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16175step0 raw16175; decide +kernel
      have hl : raw16175step0Labels = raw16175Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16175 raw16175Labels permutation456 permutation3
    mixedMoment B raw16175step0 raw16175step0Labels = mixedMoment B raw16175step1 raw16175step1Labels := by
      have ha : raw16175step1 = -raw16175step0 := by apply Matrix.ext; change ∀ i j, raw16175step1 i j = -(raw16175step0 i j); unfold raw16175step1 raw16175step0; decide +kernel
      have hl : raw16175step1Labels = raw16175step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3695 node3695Labels := by rfl

def raw16176 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw16176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16176 raw16176Labels = mixedMoment B node3696 node3696Labels := by
  calc
    mixedMoment B raw16176 raw16176Labels = mixedMoment B raw16176step0 raw16176step0Labels := by
      have ha : raw16176step0 = (fun i j => raw16176 (permutation455 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16176step0 raw16176; decide +kernel
      have hl : raw16176step0Labels = raw16176Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16176 raw16176Labels permutation455 permutation3
    mixedMoment B raw16176step0 raw16176step0Labels = mixedMoment B raw16176step1 raw16176step1Labels := by
      have ha : raw16176step1 = -raw16176step0 := by apply Matrix.ext; change ∀ i j, raw16176step1 i j = -(raw16176step0 i j); unfold raw16176step1 raw16176step0; decide +kernel
      have hl : raw16176step1Labels = raw16176step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3696 node3696Labels := by rfl

def raw16177 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16177 raw16177Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw16177 raw16177Labels = mixedMoment B raw16177step0 raw16177step0Labels := by
      have ha : raw16177step0 = (fun i j => raw16177 (permutation453 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16177step0 raw16177; decide +kernel
      have hl : raw16177step0Labels = raw16177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16177 raw16177Labels permutation453 permutation3
    mixedMoment B raw16177step0 raw16177step0Labels = mixedMoment B raw16177step1 raw16177step1Labels := by
      have ha : raw16177step1 = -raw16177step0 := by apply Matrix.ext; change ∀ i j, raw16177step1 i j = -(raw16177step0 i j); unfold raw16177step1 raw16177step0; decide +kernel
      have hl : raw16177step1Labels = raw16177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3698 node3698Labels := by rfl

def raw16178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16178 raw16178Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw16178 raw16178Labels = mixedMoment B raw16178step0 raw16178step0Labels := by
      have ha : raw16178step0 = (fun i j => raw16178 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16178step0 raw16178; decide +kernel
      have hl : raw16178step0Labels = raw16178Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16178 raw16178Labels permutation152 permutation6
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw16179 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16179 raw16179Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw16179 raw16179Labels = mixedMoment B raw16179step0 raw16179step0Labels := by
      have ha : raw16179step0 = (fun i j => raw16179 (permutation418 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16179step0 raw16179; decide +kernel
      have hl : raw16179step0Labels = raw16179Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16179 raw16179Labels permutation418 permutation3
    _ = mixedMoment B node3866 node3866Labels := by rfl

def raw16180 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16180 raw16180Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16180 raw16180Labels = mixedMoment B raw16180step0 raw16180step0Labels := by
      have hz : ∀ j, raw16180 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16180step0 = (fun i j => raw16180 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16180step0 raw16180; decide +kernel
      have hl : raw16180step0Labels = raw16180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16180 raw16180Labels permutation434 hz
    mixedMoment B raw16180step0 raw16180step0Labels = mixedMoment B raw16180step1 raw16180step1Labels := by
      have ha : raw16180step1 = (fun i j => raw16180step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16180step1 raw16180step0; decide +kernel
      have hl : raw16180step1Labels = raw16180step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16180step0 raw16180step0Labels permutation32 permutation6
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw16181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16181step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16181 raw16181Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw16181 raw16181Labels = mixedMoment B raw16181step0 raw16181step0Labels := by
      have ha : raw16181step0 = (fun i j => raw16181 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16181step0 raw16181; decide +kernel
      have hl : raw16181step0Labels = raw16181Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16181 raw16181Labels permutation152 permutation6
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw16182 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw16182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16182 raw16182Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw16182 raw16182Labels = mixedMoment B raw16182step0 raw16182step0Labels := by
      have ha : raw16182step0 = (fun i j => raw16182 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16182step0 raw16182; decide +kernel
      have hl : raw16182step0Labels = raw16182Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16182 raw16182Labels permutation152 permutation6
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw16183 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw16183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16183 raw16183Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw16183 raw16183Labels = mixedMoment B raw16183step0 raw16183step0Labels := by
      have ha : raw16183step0 = (fun i j => raw16183 (permutation402 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16183step0 raw16183; decide +kernel
      have hl : raw16183step0Labels = raw16183Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16183 raw16183Labels permutation402 permutation3
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw16184 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16184 raw16184Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw16184 raw16184Labels = mixedMoment B raw16184step0 raw16184step0Labels := by
      have hz : ∀ j, raw16184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16184step0 = (fun i j => raw16184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16184step0 raw16184; decide +kernel
      have hl : raw16184step0Labels = raw16184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16184 raw16184Labels permutation434 hz
    mixedMoment B raw16184step0 raw16184step0Labels = mixedMoment B raw16184step1 raw16184step1Labels := by
      have ha : raw16184step1 = (fun i j => raw16184step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16184step1 raw16184step0; decide +kernel
      have hl : raw16184step1Labels = raw16184step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16184step0 raw16184step0Labels permutation151 permutation6
    mixedMoment B raw16184step1 raw16184step1Labels = mixedMoment B raw16184step2 raw16184step2Labels := by
      have ha : raw16184step2 = -raw16184step1 := by apply Matrix.ext; change ∀ i j, raw16184step2 i j = -(raw16184step1 i j); unfold raw16184step2 raw16184step1; decide +kernel
      have hl : raw16184step2Labels = raw16184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw16185 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16185 raw16185Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw16185 raw16185Labels = mixedMoment B raw16185step0 raw16185step0Labels := by
      have ha : raw16185step0 = (fun i j => raw16185 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16185step0 raw16185; decide +kernel
      have hl : raw16185step0Labels = raw16185Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16185 raw16185Labels permutation152 permutation6
    _ = mixedMoment B node3870 node3870Labels := by rfl

def raw16186 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16186step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16186 raw16186Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw16186 raw16186Labels = mixedMoment B raw16186step0 raw16186step0Labels := by
      have ha : raw16186step0 = (fun i j => raw16186 (permutation360 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16186step0 raw16186; decide +kernel
      have hl : raw16186step0Labels = raw16186Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16186 raw16186Labels permutation360 permutation5
    mixedMoment B raw16186step0 raw16186step0Labels = mixedMoment B raw16186step1 raw16186step1Labels := by
      have ha : raw16186step1 = -raw16186step0 := by apply Matrix.ext; change ∀ i j, raw16186step1 i j = -(raw16186step0 i j); unfold raw16186step1 raw16186step0; decide +kernel
      have hl : raw16186step1Labels = raw16186step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16186step1 raw16186step1Labels = mixedMoment B raw16186step2 raw16186step2Labels := by
      have ha : raw16186step2 = raw16186step1 := by apply Matrix.ext; unfold raw16186step2 raw16186step1; decide +kernel
      have hl : raw16186step1Labels = labelEmbedding1 ∘ raw16186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16186step1 raw16186step1Labels raw16186step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw16187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16187step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16187 raw16187Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw16187 raw16187Labels = mixedMoment B raw16187step0 raw16187step0Labels := by
      have hz : ∀ j, raw16187 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16187step0 = (fun i j => raw16187 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16187step0 raw16187; decide +kernel
      have hl : raw16187step0Labels = raw16187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16187 raw16187Labels permutation434 hz
    mixedMoment B raw16187step0 raw16187step0Labels = mixedMoment B raw16187step1 raw16187step1Labels := by
      have ha : raw16187step1 = (fun i j => raw16187step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16187step1 raw16187step0; decide +kernel
      have hl : raw16187step1Labels = raw16187step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16187step0 raw16187step0Labels permutation32 permutation7
    mixedMoment B raw16187step1 raw16187step1Labels = mixedMoment B raw16187step2 raw16187step2Labels := by
      have ha : raw16187step2 = raw16187step1 := by apply Matrix.ext; unfold raw16187step2 raw16187step1; decide +kernel
      have hl : raw16187step1Labels = labelEmbedding1 ∘ raw16187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16187step1 raw16187step1Labels raw16187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw16188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16188 raw16188Labels = mixedMoment B node3950 node3950Labels := by
  calc
    mixedMoment B raw16188 raw16188Labels = mixedMoment B raw16188step0 raw16188step0Labels := by
      have ha : raw16188step0 = (fun i j => raw16188 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16188step0 raw16188; decide +kernel
      have hl : raw16188step0Labels = raw16188Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16188 raw16188Labels permutation158 permutation7
    mixedMoment B raw16188step0 raw16188step0Labels = mixedMoment B raw16188step1 raw16188step1Labels := by
      have ha : raw16188step1 = raw16188step0 := by apply Matrix.ext; unfold raw16188step1 raw16188step0; decide +kernel
      have hl : raw16188step0Labels = labelEmbedding1 ∘ raw16188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16188step0 raw16188step0Labels raw16188step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3950 node3950Labels := by rfl

def raw16189 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16189step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16189step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16189 raw16189Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw16189 raw16189Labels = mixedMoment B raw16189step0 raw16189step0Labels := by
      have ha : raw16189step0 = (fun i j => raw16189 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16189step0 raw16189; decide +kernel
      have hl : raw16189step0Labels = raw16189Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16189 raw16189Labels permutation682 permutation7
    mixedMoment B raw16189step0 raw16189step0Labels = mixedMoment B raw16189step1 raw16189step1Labels := by
      have ha : raw16189step1 = -raw16189step0 := by apply Matrix.ext; change ∀ i j, raw16189step1 i j = -(raw16189step0 i j); unfold raw16189step1 raw16189step0; decide +kernel
      have hl : raw16189step1Labels = raw16189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16189step1 raw16189step1Labels = mixedMoment B raw16189step2 raw16189step2Labels := by
      have ha : raw16189step2 = raw16189step1 := by apply Matrix.ext; unfold raw16189step2 raw16189step1; decide +kernel
      have hl : raw16189step1Labels = labelEmbedding1 ∘ raw16189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16189step1 raw16189step1Labels raw16189step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw16190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw16190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16190step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw16190step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16190 raw16190Labels = mixedMoment B node2921 node2921Labels := by
  calc
    mixedMoment B raw16190 raw16190Labels = mixedMoment B raw16190step0 raw16190step0Labels := by
      have ha : raw16190step0 = (fun i j => raw16190 (permutation193 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16190step0 raw16190; decide +kernel
      have hl : raw16190step0Labels = raw16190Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16190 raw16190Labels permutation193 permutation5
    mixedMoment B raw16190step0 raw16190step0Labels = mixedMoment B raw16190step1 raw16190step1Labels := by
      have ha : raw16190step1 = -raw16190step0 := by apply Matrix.ext; change ∀ i j, raw16190step1 i j = -(raw16190step0 i j); unfold raw16190step1 raw16190step0; decide +kernel
      have hl : raw16190step1Labels = raw16190step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16190step1 raw16190step1Labels = mixedMoment B raw16190step2 raw16190step2Labels := by
      have ha : raw16190step2 = raw16190step1 := by apply Matrix.ext; unfold raw16190step2 raw16190step1; decide +kernel
      have hl : raw16190step1Labels = labelEmbedding1 ∘ raw16190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16190step1 raw16190step1Labels raw16190step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2921 node2921Labels := by rfl

def raw16191 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16191step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw16191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16191 raw16191Labels = mixedMoment B node3441 node3441Labels := by
  calc
    mixedMoment B raw16191 raw16191Labels = mixedMoment B raw16191step0 raw16191step0Labels := by
      have ha : raw16191step0 = (fun i j => raw16191 (permutation320 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16191step0 raw16191; decide +kernel
      have hl : raw16191step0Labels = raw16191Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16191 raw16191Labels permutation320 permutation5
    mixedMoment B raw16191step0 raw16191step0Labels = mixedMoment B raw16191step1 raw16191step1Labels := by
      have ha : raw16191step1 = raw16191step0 := by apply Matrix.ext; unfold raw16191step1 raw16191step0; decide +kernel
      have hl : raw16191step0Labels = labelEmbedding1 ∘ raw16191step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16191step0 raw16191step0Labels raw16191step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3441 node3441Labels := by rfl

def raw16192 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16192step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16192 raw16192Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw16192 raw16192Labels = mixedMoment B raw16192step0 raw16192step0Labels := by
      have hz : ∀ j, raw16192 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16192step0 = (fun i j => raw16192 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16192step0 raw16192; decide +kernel
      have hl : raw16192step0Labels = raw16192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16192 raw16192Labels permutation434 hz
    mixedMoment B raw16192step0 raw16192step0Labels = mixedMoment B raw16192step1 raw16192step1Labels := by
      have ha : raw16192step1 = (fun i j => raw16192step0 (permutation79 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16192step1 raw16192step0; decide +kernel
      have hl : raw16192step1Labels = raw16192step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16192step0 raw16192step0Labels permutation79 permutation5
    mixedMoment B raw16192step1 raw16192step1Labels = mixedMoment B raw16192step2 raw16192step2Labels := by
      have ha : raw16192step2 = raw16192step1 := by apply Matrix.ext; unfold raw16192step2 raw16192step1; decide +kernel
      have hl : raw16192step1Labels = labelEmbedding1 ∘ raw16192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16192step1 raw16192step1Labels raw16192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw16193 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16193step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16193 raw16193Labels = mixedMoment B node3447 node3447Labels := by
  calc
    mixedMoment B raw16193 raw16193Labels = mixedMoment B raw16193step0 raw16193step0Labels := by
      have ha : raw16193step0 = (fun i j => raw16193 (permutation319 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16193step0 raw16193; decide +kernel
      have hl : raw16193step0Labels = raw16193Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16193 raw16193Labels permutation319 permutation5
    mixedMoment B raw16193step0 raw16193step0Labels = mixedMoment B raw16193step1 raw16193step1Labels := by
      have ha : raw16193step1 = raw16193step0 := by apply Matrix.ext; unfold raw16193step1 raw16193step0; decide +kernel
      have hl : raw16193step0Labels = labelEmbedding1 ∘ raw16193step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16193step0 raw16193step0Labels raw16193step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3447 node3447Labels := by rfl

def raw16194 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16194 raw16194Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw16194 raw16194Labels = mixedMoment B raw16194step0 raw16194step0Labels := by
      have ha : raw16194step0 = (fun i j => raw16194 (permutation317 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16194step0 raw16194; decide +kernel
      have hl : raw16194step0Labels = raw16194Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16194 raw16194Labels permutation317 permutation5
    mixedMoment B raw16194step0 raw16194step0Labels = mixedMoment B raw16194step1 raw16194step1Labels := by
      have ha : raw16194step1 = raw16194step0 := by apply Matrix.ext; unfold raw16194step1 raw16194step0; decide +kernel
      have hl : raw16194step0Labels = labelEmbedding1 ∘ raw16194step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16194step0 raw16194step0Labels raw16194step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw16195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16195step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16195step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16195 raw16195Labels = mixedMoment B node2922 node2922Labels := by
  calc
    mixedMoment B raw16195 raw16195Labels = mixedMoment B raw16195step0 raw16195step0Labels := by
      have ha : raw16195step0 = (fun i j => raw16195 (permutation192 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16195step0 raw16195; decide +kernel
      have hl : raw16195step0Labels = raw16195Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16195 raw16195Labels permutation192 permutation5
    mixedMoment B raw16195step0 raw16195step0Labels = mixedMoment B raw16195step1 raw16195step1Labels := by
      have ha : raw16195step1 = -raw16195step0 := by apply Matrix.ext; change ∀ i j, raw16195step1 i j = -(raw16195step0 i j); unfold raw16195step1 raw16195step0; decide +kernel
      have hl : raw16195step1Labels = raw16195step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16195step1 raw16195step1Labels = mixedMoment B raw16195step2 raw16195step2Labels := by
      have ha : raw16195step2 = raw16195step1 := by apply Matrix.ext; unfold raw16195step2 raw16195step1; decide +kernel
      have hl : raw16195step1Labels = labelEmbedding1 ∘ raw16195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16195step1 raw16195step1Labels raw16195step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2922 node2922Labels := by rfl

def raw16196 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw16196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw16196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16196 raw16196Labels = mixedMoment B node3718 node3718Labels := by
  calc
    mixedMoment B raw16196 raw16196Labels = mixedMoment B raw16196step0 raw16196step0Labels := by
      have ha : raw16196step0 = (fun i j => raw16196 (permutation359 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16196step0 raw16196; decide +kernel
      have hl : raw16196step0Labels = raw16196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16196 raw16196Labels permutation359 permutation5
    mixedMoment B raw16196step0 raw16196step0Labels = mixedMoment B raw16196step1 raw16196step1Labels := by
      have ha : raw16196step1 = -raw16196step0 := by apply Matrix.ext; change ∀ i j, raw16196step1 i j = -(raw16196step0 i j); unfold raw16196step1 raw16196step0; decide +kernel
      have hl : raw16196step1Labels = raw16196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16196step1 raw16196step1Labels = mixedMoment B raw16196step2 raw16196step2Labels := by
      have ha : raw16196step2 = raw16196step1 := by apply Matrix.ext; unfold raw16196step2 raw16196step1; decide +kernel
      have hl : raw16196step1Labels = labelEmbedding1 ∘ raw16196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16196step1 raw16196step1Labels raw16196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3718 node3718Labels := by rfl

def raw16197 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16197step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16197 raw16197Labels = mixedMoment B node3752 node3752Labels := by
  calc
    mixedMoment B raw16197 raw16197Labels = mixedMoment B raw16197step0 raw16197step0Labels := by
      have ha : raw16197step0 = (fun i j => raw16197 (permutation465 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16197step0 raw16197; decide +kernel
      have hl : raw16197step0Labels = raw16197Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16197 raw16197Labels permutation465 permutation5
    mixedMoment B raw16197step0 raw16197step0Labels = mixedMoment B raw16197step1 raw16197step1Labels := by
      have ha : raw16197step1 = raw16197step0 := by apply Matrix.ext; unfold raw16197step1 raw16197step0; decide +kernel
      have hl : raw16197step0Labels = labelEmbedding1 ∘ raw16197step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16197step0 raw16197step0Labels raw16197step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3752 node3752Labels := by rfl

def raw16198 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw16198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16198 raw16198Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw16198 raw16198Labels = mixedMoment B raw16198step0 raw16198step0Labels := by
      have ha : raw16198step0 = (fun i j => raw16198 (permutation463 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16198step0 raw16198; decide +kernel
      have hl : raw16198step0Labels = raw16198Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16198 raw16198Labels permutation463 permutation5
    mixedMoment B raw16198step0 raw16198step0Labels = mixedMoment B raw16198step1 raw16198step1Labels := by
      have ha : raw16198step1 = raw16198step0 := by apply Matrix.ext; unfold raw16198step1 raw16198step0; decide +kernel
      have hl : raw16198step0Labels = labelEmbedding1 ∘ raw16198step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16198step0 raw16198step0Labels raw16198step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw16199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16199step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16199step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16199 raw16199Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw16199 raw16199Labels = mixedMoment B raw16199step0 raw16199step0Labels := by
      have ha : raw16199step0 = (fun i j => raw16199 (permutation199 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16199step0 raw16199; decide +kernel
      have hl : raw16199step0Labels = raw16199Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16199 raw16199Labels permutation199 permutation5
    mixedMoment B raw16199step0 raw16199step0Labels = mixedMoment B raw16199step1 raw16199step1Labels := by
      have ha : raw16199step1 = -raw16199step0 := by apply Matrix.ext; change ∀ i j, raw16199step1 i j = -(raw16199step0 i j); unfold raw16199step1 raw16199step0; decide +kernel
      have hl : raw16199step1Labels = raw16199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16199step1 raw16199step1Labels = mixedMoment B raw16199step2 raw16199step2Labels := by
      have ha : raw16199step2 = raw16199step1 := by apply Matrix.ext; unfold raw16199step2 raw16199step1; decide +kernel
      have hl : raw16199step1Labels = labelEmbedding1 ∘ raw16199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16199step1 raw16199step1Labels raw16199step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2951 node2951Labels := by rfl

def raw16200 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16200step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16200step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16200step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16200step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16200 raw16200Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw16200 raw16200Labels = mixedMoment B raw16200step0 raw16200step0Labels := by
      have ha : raw16200step0 = (fun i j => raw16200 (permutation366 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16200step0 raw16200; decide +kernel
      have hl : raw16200step0Labels = raw16200Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16200 raw16200Labels permutation366 permutation5
    mixedMoment B raw16200step0 raw16200step0Labels = mixedMoment B raw16200step1 raw16200step1Labels := by
      have ha : raw16200step1 = -raw16200step0 := by apply Matrix.ext; change ∀ i j, raw16200step1 i j = -(raw16200step0 i j); unfold raw16200step1 raw16200step0; decide +kernel
      have hl : raw16200step1Labels = raw16200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16200step1 raw16200step1Labels = mixedMoment B raw16200step2 raw16200step2Labels := by
      have ha : raw16200step2 = raw16200step1 := by apply Matrix.ext; unfold raw16200step2 raw16200step1; decide +kernel
      have hl : raw16200step1Labels = labelEmbedding1 ∘ raw16200step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16200step1 raw16200step1Labels raw16200step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3730 node3730Labels := by rfl

def raw16201 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16201step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16201step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16201 raw16201Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw16201 raw16201Labels = mixedMoment B raw16201step0 raw16201step0Labels := by
      have hz : ∀ j, raw16201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16201step0 = (fun i j => raw16201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16201step0 raw16201; decide +kernel
      have hl : raw16201step0Labels = raw16201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16201 raw16201Labels permutation434 hz
    mixedMoment B raw16201step0 raw16201step0Labels = mixedMoment B raw16201step1 raw16201step1Labels := by
      have ha : raw16201step1 = (fun i j => raw16201step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16201step1 raw16201step0; decide +kernel
      have hl : raw16201step1Labels = raw16201step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16201step0 raw16201step0Labels permutation151 permutation7
    mixedMoment B raw16201step1 raw16201step1Labels = mixedMoment B raw16201step2 raw16201step2Labels := by
      have ha : raw16201step2 = -raw16201step1 := by apply Matrix.ext; change ∀ i j, raw16201step2 i j = -(raw16201step1 i j); unfold raw16201step2 raw16201step1; decide +kernel
      have hl : raw16201step2Labels = raw16201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16201step2 raw16201step2Labels = mixedMoment B raw16201step3 raw16201step3Labels := by
      have ha : raw16201step3 = raw16201step2 := by apply Matrix.ext; unfold raw16201step3 raw16201step2; decide +kernel
      have hl : raw16201step2Labels = labelEmbedding1 ∘ raw16201step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16201step2 raw16201step2Labels raw16201step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw16202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16202step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16202step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16202step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16202 raw16202Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw16202 raw16202Labels = mixedMoment B raw16202step0 raw16202step0Labels := by
      have ha : raw16202step0 = (fun i j => raw16202 (permutation190 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16202step0 raw16202; decide +kernel
      have hl : raw16202step0Labels = raw16202Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16202 raw16202Labels permutation190 permutation5
    mixedMoment B raw16202step0 raw16202step0Labels = mixedMoment B raw16202step1 raw16202step1Labels := by
      have ha : raw16202step1 = -raw16202step0 := by apply Matrix.ext; change ∀ i j, raw16202step1 i j = -(raw16202step0 i j); unfold raw16202step1 raw16202step0; decide +kernel
      have hl : raw16202step1Labels = raw16202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16202step1 raw16202step1Labels = mixedMoment B raw16202step2 raw16202step2Labels := by
      have ha : raw16202step2 = raw16202step1 := by apply Matrix.ext; unfold raw16202step2 raw16202step1; decide +kernel
      have hl : raw16202step1Labels = labelEmbedding1 ∘ raw16202step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16202step1 raw16202step1Labels raw16202step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2928 node2928Labels := by rfl

def raw16203 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16203step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16203step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16203step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16203 raw16203Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw16203 raw16203Labels = mixedMoment B raw16203step0 raw16203step0Labels := by
      have ha : raw16203step0 = (fun i j => raw16203 (permutation358 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16203step0 raw16203; decide +kernel
      have hl : raw16203step0Labels = raw16203Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16203 raw16203Labels permutation358 permutation5
    mixedMoment B raw16203step0 raw16203step0Labels = mixedMoment B raw16203step1 raw16203step1Labels := by
      have ha : raw16203step1 = -raw16203step0 := by apply Matrix.ext; change ∀ i j, raw16203step1 i j = -(raw16203step0 i j); unfold raw16203step1 raw16203step0; decide +kernel
      have hl : raw16203step1Labels = raw16203step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16203step1 raw16203step1Labels = mixedMoment B raw16203step2 raw16203step2Labels := by
      have ha : raw16203step2 = raw16203step1 := by apply Matrix.ext; unfold raw16203step2 raw16203step1; decide +kernel
      have hl : raw16203step1Labels = labelEmbedding1 ∘ raw16203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16203step1 raw16203step1Labels raw16203step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3722 node3722Labels := by rfl

def raw16204 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16204 raw16204Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw16204 raw16204Labels = mixedMoment B raw16204step0 raw16204step0Labels := by
      have hz : ∀ j, raw16204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16204step0 = (fun i j => raw16204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16204step0 raw16204; decide +kernel
      have hl : raw16204step0Labels = raw16204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16204 raw16204Labels permutation434 hz
    mixedMoment B raw16204step0 raw16204step0Labels = mixedMoment B raw16204step1 raw16204step1Labels := by
      have ha : raw16204step1 = (fun i j => raw16204step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16204step1 raw16204step0; decide +kernel
      have hl : raw16204step1Labels = raw16204step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16204step0 raw16204step0Labels permutation139 permutation5
    mixedMoment B raw16204step1 raw16204step1Labels = mixedMoment B raw16204step2 raw16204step2Labels := by
      have ha : raw16204step2 = raw16204step1 := by apply Matrix.ext; unfold raw16204step2 raw16204step1; decide +kernel
      have hl : raw16204step1Labels = labelEmbedding1 ∘ raw16204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16204step1 raw16204step1Labels raw16204step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw16205 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw16205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16205step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw16205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16205 raw16205Labels = mixedMoment B node4022 node4022Labels := by
  calc
    mixedMoment B raw16205 raw16205Labels = mixedMoment B raw16205step0 raw16205step0Labels := by
      have ha : raw16205step0 = (fun i j => raw16205 (permutation614 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16205step0 raw16205; decide +kernel
      have hl : raw16205step0Labels = raw16205Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16205 raw16205Labels permutation614 permutation5
    mixedMoment B raw16205step0 raw16205step0Labels = mixedMoment B raw16205step1 raw16205step1Labels := by
      have ha : raw16205step1 = raw16205step0 := by apply Matrix.ext; unfold raw16205step1 raw16205step0; decide +kernel
      have hl : raw16205step0Labels = labelEmbedding1 ∘ raw16205step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16205step0 raw16205step0Labels raw16205step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4022 node4022Labels := by rfl

def raw16206 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16206step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16206 raw16206Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw16206 raw16206Labels = mixedMoment B raw16206step0 raw16206step0Labels := by
      have ha : raw16206step0 = (fun i j => raw16206 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16206step0 raw16206; decide +kernel
      have hl : raw16206step0Labels = raw16206Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16206 raw16206Labels permutation188 permutation4
    mixedMoment B raw16206step0 raw16206step0Labels = mixedMoment B raw16206step1 raw16206step1Labels := by
      have ha : raw16206step1 = -raw16206step0 := by apply Matrix.ext; change ∀ i j, raw16206step1 i j = -(raw16206step0 i j); unfold raw16206step1 raw16206step0; decide +kernel
      have hl : raw16206step1Labels = raw16206step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw16207 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16207 raw16207Labels = mixedMoment B node4044 node4044Labels := by
  calc
    mixedMoment B raw16207 raw16207Labels = mixedMoment B raw16207step0 raw16207step0Labels := by
      have ha : raw16207step0 = (fun i j => raw16207 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16207step0 raw16207; decide +kernel
      have hl : raw16207step0Labels = raw16207Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16207 raw16207Labels permutation682 permutation2
    _ = mixedMoment B node4044 node4044Labels := by rfl

def raw16208 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16208step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16208 raw16208Labels = mixedMoment B node3946 node3946Labels := by
  calc
    mixedMoment B raw16208 raw16208Labels = mixedMoment B raw16208step0 raw16208step0Labels := by
      have ha : raw16208step0 = (fun i j => raw16208 (permutation274 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16208step0 raw16208; decide +kernel
      have hl : raw16208step0Labels = raw16208Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16208 raw16208Labels permutation274 permutation2
    mixedMoment B raw16208step0 raw16208step0Labels = mixedMoment B raw16208step1 raw16208step1Labels := by
      have ha : raw16208step1 = -raw16208step0 := by apply Matrix.ext; change ∀ i j, raw16208step1 i j = -(raw16208step0 i j); unfold raw16208step1 raw16208step0; decide +kernel
      have hl : raw16208step1Labels = raw16208step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3946 node3946Labels := by rfl

def raw16209 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16209step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16209 raw16209Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw16209 raw16209Labels = mixedMoment B raw16209step0 raw16209step0Labels := by
      have hz : ∀ j, raw16209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16209step0 = (fun i j => raw16209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16209step0 raw16209; decide +kernel
      have hl : raw16209step0Labels = raw16209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16209 raw16209Labels permutation434 hz
    mixedMoment B raw16209step0 raw16209step0Labels = mixedMoment B raw16209step1 raw16209step1Labels := by
      have ha : raw16209step1 = (fun i j => raw16209step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16209step1 raw16209step0; decide +kernel
      have hl : raw16209step1Labels = raw16209step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16209step0 raw16209step0Labels permutation56 permutation2
    mixedMoment B raw16209step1 raw16209step1Labels = mixedMoment B raw16209step2 raw16209step2Labels := by
      have ha : raw16209step2 = -raw16209step1 := by apply Matrix.ext; change ∀ i j, raw16209step2 i j = -(raw16209step1 i j); unfold raw16209step2 raw16209step1; decide +kernel
      have hl : raw16209step2Labels = raw16209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw16210 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16210 raw16210Labels = mixedMoment B node3944 node3944Labels := by
  calc
    mixedMoment B raw16210 raw16210Labels = mixedMoment B raw16210step0 raw16210step0Labels := by
      have ha : raw16210step0 = (fun i j => raw16210 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16210step0 raw16210; decide +kernel
      have hl : raw16210step0Labels = raw16210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16210 raw16210Labels permutation583 permutation2
    _ = mixedMoment B node3944 node3944Labels := by rfl

def raw16211 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16211 raw16211Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw16211 raw16211Labels = mixedMoment B raw16211step0 raw16211step0Labels := by
      have ha : raw16211step0 = (fun i j => raw16211 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16211step0 raw16211; decide +kernel
      have hl : raw16211step0Labels = raw16211Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16211 raw16211Labels permutation681 permutation2
    _ = mixedMoment B node3781 node3781Labels := by rfl

def raw16212 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16212 raw16212Labels = mixedMoment B node2977 node2977Labels := by
  calc
    mixedMoment B raw16212 raw16212Labels = mixedMoment B raw16212step0 raw16212step0Labels := by
      have ha : raw16212step0 = (fun i j => raw16212 (permutation308 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16212step0 raw16212; decide +kernel
      have hl : raw16212step0Labels = raw16212Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16212 raw16212Labels permutation308 permutation2
    mixedMoment B raw16212step0 raw16212step0Labels = mixedMoment B raw16212step1 raw16212step1Labels := by
      have ha : raw16212step1 = -raw16212step0 := by apply Matrix.ext; change ∀ i j, raw16212step1 i j = -(raw16212step0 i j); unfold raw16212step1 raw16212step0; decide +kernel
      have hl : raw16212step1Labels = raw16212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2977 node2977Labels := by rfl

def raw16213 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16213 raw16213Labels = mixedMoment B node3725 node3725Labels := by
  calc
    mixedMoment B raw16213 raw16213Labels = mixedMoment B raw16213step0 raw16213step0Labels := by
      have ha : raw16213step0 = (fun i j => raw16213 (permutation189 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16213step0 raw16213; decide +kernel
      have hl : raw16213step0Labels = raw16213Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16213 raw16213Labels permutation189 permutation4
    mixedMoment B raw16213step0 raw16213step0Labels = mixedMoment B raw16213step1 raw16213step1Labels := by
      have ha : raw16213step1 = -raw16213step0 := by apply Matrix.ext; change ∀ i j, raw16213step1 i j = -(raw16213step0 i j); unfold raw16213step1 raw16213step0; decide +kernel
      have hl : raw16213step1Labels = raw16213step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3725 node3725Labels := by rfl

def raw16214 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16214Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16214step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16214 raw16214Labels = mixedMoment B node3730 node3730Labels := by
  calc
    mixedMoment B raw16214 raw16214Labels = mixedMoment B raw16214step0 raw16214step0Labels := by
      have ha : raw16214step0 = (fun i j => raw16214 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16214step0 raw16214; decide +kernel
      have hl : raw16214step0Labels = raw16214Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16214 raw16214Labels permutation176 permutation4
    mixedMoment B raw16214step0 raw16214step0Labels = mixedMoment B raw16214step1 raw16214step1Labels := by
      have ha : raw16214step1 = -raw16214step0 := by apply Matrix.ext; change ∀ i j, raw16214step1 i j = -(raw16214step0 i j); unfold raw16214step1 raw16214step0; decide +kernel
      have hl : raw16214step1Labels = raw16214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3730 node3730Labels := by rfl

def raw16215 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16215Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw16215step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16215step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16215 raw16215Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw16215 raw16215Labels = mixedMoment B raw16215step0 raw16215step0Labels := by
      have ha : raw16215step0 = (fun i j => raw16215 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16215step0 raw16215; decide +kernel
      have hl : raw16215step0Labels = raw16215Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16215 raw16215Labels permutation188 permutation4
    mixedMoment B raw16215step0 raw16215step0Labels = mixedMoment B raw16215step1 raw16215step1Labels := by
      have ha : raw16215step1 = -raw16215step0 := by apply Matrix.ext; change ∀ i j, raw16215step1 i j = -(raw16215step0 i j); unfold raw16215step1 raw16215step0; decide +kernel
      have hl : raw16215step1Labels = raw16215step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3723 node3723Labels := by rfl

def raw16216 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw16216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16216step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16216 raw16216Labels = mixedMoment B node2975 node2975Labels := by
  calc
    mixedMoment B raw16216 raw16216Labels = mixedMoment B raw16216step0 raw16216step0Labels := by
      have ha : raw16216step0 = (fun i j => raw16216 (permutation306 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16216step0 raw16216; decide +kernel
      have hl : raw16216step0Labels = raw16216Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16216 raw16216Labels permutation306 permutation2
    mixedMoment B raw16216step0 raw16216step0Labels = mixedMoment B raw16216step1 raw16216step1Labels := by
      have ha : raw16216step1 = -raw16216step0 := by apply Matrix.ext; change ∀ i j, raw16216step1 i j = -(raw16216step0 i j); unfold raw16216step1 raw16216step0; decide +kernel
      have hl : raw16216step1Labels = raw16216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2975 node2975Labels := by rfl

def raw16217 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16217step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16217 raw16217Labels = mixedMoment B node3828 node3828Labels := by
  calc
    mixedMoment B raw16217 raw16217Labels = mixedMoment B raw16217step0 raw16217step0Labels := by
      have ha : raw16217step0 = (fun i j => raw16217 (permutation189 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16217step0 raw16217; decide +kernel
      have hl : raw16217step0Labels = raw16217Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16217 raw16217Labels permutation189 permutation4
    mixedMoment B raw16217step0 raw16217step0Labels = mixedMoment B raw16217step1 raw16217step1Labels := by
      have ha : raw16217step1 = -raw16217step0 := by apply Matrix.ext; change ∀ i j, raw16217step1 i j = -(raw16217step0 i j); unfold raw16217step1 raw16217step0; decide +kernel
      have hl : raw16217step1Labels = raw16217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3828 node3828Labels := by rfl

def raw16218 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw16218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16218 raw16218Labels = mixedMoment B node3826 node3826Labels := by
  calc
    mixedMoment B raw16218 raw16218Labels = mixedMoment B raw16218step0 raw16218step0Labels := by
      have ha : raw16218step0 = (fun i j => raw16218 (permutation654 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16218step0 raw16218; decide +kernel
      have hl : raw16218step0Labels = raw16218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16218 raw16218Labels permutation654 permutation4
    _ = mixedMoment B node3826 node3826Labels := by rfl

def raw16219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16219step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16219step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16219step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16219step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16219step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16219 raw16219Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw16219 raw16219Labels = mixedMoment B raw16219step0 raw16219step0Labels := by
      have hz : ∀ j, raw16219 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16219step0 = (fun i j => raw16219 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16219step0 raw16219; decide +kernel
      have hl : raw16219step0Labels = raw16219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16219 raw16219Labels permutation434 hz
    mixedMoment B raw16219step0 raw16219step0Labels = mixedMoment B raw16219step1 raw16219step1Labels := by
      have hz : ∀ j, raw16219step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16219step1 = (fun i j => raw16219step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16219step1 raw16219step0; decide +kernel
      have hl : raw16219step1Labels = raw16219step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16219step0 raw16219step0Labels permutation80 hz
    mixedMoment B raw16219step1 raw16219step1Labels = mixedMoment B raw16219step2 raw16219step2Labels := by
      have ha : raw16219step2 = (fun i j => raw16219step1 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16219step2 raw16219step1; decide +kernel
      have hl : raw16219step2Labels = raw16219step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16219step1 raw16219step1Labels permutation14 permutation5
    mixedMoment B raw16219step2 raw16219step2Labels = mixedMoment B raw16219step3 raw16219step3Labels := by
      have ha : raw16219step3 = -raw16219step2 := by apply Matrix.ext; change ∀ i j, raw16219step3 i j = -(raw16219step2 i j); unfold raw16219step3 raw16219step2; decide +kernel
      have hl : raw16219step3Labels = raw16219step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16219step3 raw16219step3Labels = mixedMoment B raw16219step4 raw16219step4Labels := by
      have ha : raw16219step4 = raw16219step3 := by apply Matrix.ext; unfold raw16219step4 raw16219step3; decide +kernel
      have hl : raw16219step3Labels = labelEmbedding8 ∘ raw16219step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16219step3 raw16219step3Labels raw16219step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw16220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16220step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16220step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16220step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16220step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16220 raw16220Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw16220 raw16220Labels = mixedMoment B raw16220step0 raw16220step0Labels := by
      have hz : ∀ j, raw16220 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16220step0 = (fun i j => raw16220 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16220step0 raw16220; decide +kernel
      have hl : raw16220step0Labels = raw16220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16220 raw16220Labels permutation434 hz
    mixedMoment B raw16220step0 raw16220step0Labels = mixedMoment B raw16220step1 raw16220step1Labels := by
      have ha : raw16220step1 = (fun i j => raw16220step0 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16220step1 raw16220step0; decide +kernel
      have hl : raw16220step1Labels = raw16220step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16220step0 raw16220step0Labels permutation147 permutation3
    mixedMoment B raw16220step1 raw16220step1Labels = mixedMoment B raw16220step2 raw16220step2Labels := by
      have ha : raw16220step2 = -raw16220step1 := by apply Matrix.ext; change ∀ i j, raw16220step2 i j = -(raw16220step1 i j); unfold raw16220step2 raw16220step1; decide +kernel
      have hl : raw16220step2Labels = raw16220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16220step2 raw16220step2Labels = mixedMoment B raw16220step3 raw16220step3Labels := by
      have ha : raw16220step3 = raw16220step2 := by apply Matrix.ext; unfold raw16220step3 raw16220step2; decide +kernel
      have hl : raw16220step2Labels = labelEmbedding6 ∘ raw16220step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16220step2 raw16220step2Labels raw16220step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw16221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16221step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16221step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16221step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16221step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16221 raw16221Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw16221 raw16221Labels = mixedMoment B raw16221step0 raw16221step0Labels := by
      have hz : ∀ j, raw16221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16221step0 = (fun i j => raw16221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16221step0 raw16221; decide +kernel
      have hl : raw16221step0Labels = raw16221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16221 raw16221Labels permutation346 hz
    mixedMoment B raw16221step0 raw16221step0Labels = mixedMoment B raw16221step1 raw16221step1Labels := by
      have ha : raw16221step1 = (fun i j => raw16221step0 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16221step1 raw16221step0; decide +kernel
      have hl : raw16221step1Labels = raw16221step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16221step0 raw16221step0Labels permutation147 permutation3
    mixedMoment B raw16221step1 raw16221step1Labels = mixedMoment B raw16221step2 raw16221step2Labels := by
      have ha : raw16221step2 = -raw16221step1 := by apply Matrix.ext; change ∀ i j, raw16221step2 i j = -(raw16221step1 i j); unfold raw16221step2 raw16221step1; decide +kernel
      have hl : raw16221step2Labels = raw16221step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16221step2 raw16221step2Labels = mixedMoment B raw16221step3 raw16221step3Labels := by
      have ha : raw16221step3 = raw16221step2 := by apply Matrix.ext; unfold raw16221step3 raw16221step2; decide +kernel
      have hl : raw16221step2Labels = labelEmbedding6 ∘ raw16221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16221step2 raw16221step2Labels raw16221step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw16222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16222step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, -1, -1]]
def raw16222step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16222step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw16222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16222step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw16222step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16222 raw16222Labels = mixedMoment B node5494 node5494Labels := by
  calc
    mixedMoment B raw16222 raw16222Labels = mixedMoment B raw16222step0 raw16222step0Labels := by
      have hz : ∀ j, raw16222 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16222step0 = (fun i j => raw16222 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16222step0 raw16222; decide +kernel
      have hl : raw16222step0Labels = raw16222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16222 raw16222Labels permutation520 hz
    mixedMoment B raw16222step0 raw16222step0Labels = mixedMoment B raw16222step1 raw16222step1Labels := by
      have hz : ∀ j, raw16222step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw16222step1 = (fun i j => raw16222step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw16222step1 raw16222step0; decide +kernel
      have hl : raw16222step1Labels = raw16222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16222step0 raw16222step0Labels permutation104 hz
    mixedMoment B raw16222step1 raw16222step1Labels = mixedMoment B raw16222step2 raw16222step2Labels := by
      have hz : ∀ j, raw16222step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw16222step2 = (fun i j => raw16222step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw16222step2 raw16222step1; decide +kernel
      have hl : raw16222step2Labels = raw16222step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16222step1 raw16222step1Labels permutation20 hz
    mixedMoment B raw16222step2 raw16222step2Labels = mixedMoment B raw16222step3 raw16222step3Labels := by
      have ha : raw16222step3 = (fun i j => raw16222step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16222step3 raw16222step2; decide +kernel
      have hl : raw16222step3Labels = raw16222step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16222step2 raw16222step2Labels permutation7 permutation2
    mixedMoment B raw16222step3 raw16222step3Labels = mixedMoment B raw16222step4 raw16222step4Labels := by
      have ha : raw16222step4 = -raw16222step3 := by apply Matrix.ext; change ∀ i j, raw16222step4 i j = -(raw16222step3 i j); unfold raw16222step4 raw16222step3; decide +kernel
      have hl : raw16222step4Labels = raw16222step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5494 node5494Labels := by rfl

def raw16223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16223step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16223step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16223step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16223step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16223step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16223step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16223step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16223 raw16223Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw16223 raw16223Labels = mixedMoment B raw16223step0 raw16223step0Labels := by
      have hz : ∀ j, raw16223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16223step0 = (fun i j => raw16223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16223step0 raw16223; decide +kernel
      have hl : raw16223step0Labels = raw16223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16223 raw16223Labels permutation434 hz
    mixedMoment B raw16223step0 raw16223step0Labels = mixedMoment B raw16223step1 raw16223step1Labels := by
      have hz : ∀ j, raw16223step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16223step1 = (fun i j => raw16223step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16223step1 raw16223step0; decide +kernel
      have hl : raw16223step1Labels = raw16223step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16223step0 raw16223step0Labels permutation80 hz
    mixedMoment B raw16223step1 raw16223step1Labels = mixedMoment B raw16223step2 raw16223step2Labels := by
      have ha : raw16223step2 = (fun i j => raw16223step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16223step2 raw16223step1; decide +kernel
      have hl : raw16223step2Labels = raw16223step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16223step1 raw16223step1Labels permutation19 permutation4
    mixedMoment B raw16223step2 raw16223step2Labels = mixedMoment B raw16223step3 raw16223step3Labels := by
      have ha : raw16223step3 = -raw16223step2 := by apply Matrix.ext; change ∀ i j, raw16223step3 i j = -(raw16223step2 i j); unfold raw16223step3 raw16223step2; decide +kernel
      have hl : raw16223step3Labels = raw16223step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16223step3 raw16223step3Labels = mixedMoment B raw16223step4 raw16223step4Labels := by
      have ha : raw16223step4 = raw16223step3 := by apply Matrix.ext; unfold raw16223step4 raw16223step3; decide +kernel
      have hl : raw16223step3Labels = labelEmbedding7 ∘ raw16223step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16223step3 raw16223step3Labels raw16223step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw16224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16224 raw16224Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw16224 raw16224Labels = mixedMoment B raw16224step0 raw16224step0Labels := by
      have hz : ∀ j, raw16224 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16224step0 = (fun i j => raw16224 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16224step0 raw16224; decide +kernel
      have hl : raw16224step0Labels = raw16224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16224 raw16224Labels permutation434 hz
    mixedMoment B raw16224step0 raw16224step0Labels = mixedMoment B raw16224step1 raw16224step1Labels := by
      have hz : ∀ j, raw16224step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16224step1 = (fun i j => raw16224step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16224step1 raw16224step0; decide +kernel
      have hl : raw16224step1Labels = raw16224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16224step0 raw16224step0Labels permutation80 hz
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw16225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16225 raw16225Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw16225 raw16225Labels = mixedMoment B raw16225step0 raw16225step0Labels := by
      have hz : ∀ j, raw16225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16225step0 = (fun i j => raw16225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16225step0 raw16225; decide +kernel
      have hl : raw16225step0Labels = raw16225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16225 raw16225Labels permutation434 hz
    mixedMoment B raw16225step0 raw16225step0Labels = mixedMoment B raw16225step1 raw16225step1Labels := by
      have ha : raw16225step1 = (fun i j => raw16225step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16225step1 raw16225step0; decide +kernel
      have hl : raw16225step1Labels = raw16225step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16225step0 raw16225step0Labels permutation38 permutation2
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw16226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16226 raw16226Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw16226 raw16226Labels = mixedMoment B raw16226step0 raw16226step0Labels := by
      have hz : ∀ j, raw16226 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16226step0 = (fun i j => raw16226 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16226step0 raw16226; decide +kernel
      have hl : raw16226step0Labels = raw16226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16226 raw16226Labels permutation346 hz
    mixedMoment B raw16226step0 raw16226step0Labels = mixedMoment B raw16226step1 raw16226step1Labels := by
      have ha : raw16226step1 = (fun i j => raw16226step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16226step1 raw16226step0; decide +kernel
      have hl : raw16226step1Labels = raw16226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16226step0 raw16226step0Labels permutation38 permutation2
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw16227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16227step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw16227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16227 raw16227Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw16227 raw16227Labels = mixedMoment B raw16227step0 raw16227step0Labels := by
      have hz : ∀ j, raw16227 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16227step0 = (fun i j => raw16227 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16227step0 raw16227; decide +kernel
      have hl : raw16227step0Labels = raw16227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16227 raw16227Labels permutation520 hz
    mixedMoment B raw16227step0 raw16227step0Labels = mixedMoment B raw16227step1 raw16227step1Labels := by
      have hz : ∀ j, raw16227step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw16227step1 = (fun i j => raw16227step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw16227step1 raw16227step0; decide +kernel
      have hl : raw16227step1Labels = raw16227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16227step0 raw16227step0Labels permutation104 hz
    mixedMoment B raw16227step1 raw16227step1Labels = mixedMoment B raw16227step2 raw16227step2Labels := by
      have hz : ∀ j, raw16227step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw16227step2 = (fun i j => raw16227step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw16227step2 raw16227step1; decide +kernel
      have hl : raw16227step2Labels = raw16227step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16227step1 raw16227step1Labels permutation20 hz
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw16228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16228 raw16228Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw16228 raw16228Labels = mixedMoment B raw16228step0 raw16228step0Labels := by
      have hz : ∀ j, raw16228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16228step0 = (fun i j => raw16228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16228step0 raw16228; decide +kernel
      have hl : raw16228step0Labels = raw16228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16228 raw16228Labels permutation434 hz
    mixedMoment B raw16228step0 raw16228step0Labels = mixedMoment B raw16228step1 raw16228step1Labels := by
      have hz : ∀ j, raw16228step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16228step1 = (fun i j => raw16228step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16228step1 raw16228step0; decide +kernel
      have hl : raw16228step1Labels = raw16228step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16228step0 raw16228step0Labels permutation80 hz
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw16229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16229 raw16229Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw16229 raw16229Labels = mixedMoment B raw16229step0 raw16229step0Labels := by
      have hz : ∀ j, raw16229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16229step0 = (fun i j => raw16229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16229step0 raw16229; decide +kernel
      have hl : raw16229step0Labels = raw16229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16229 raw16229Labels permutation434 hz
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw16230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16230step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16230step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16230step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16230step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16230 raw16230Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw16230 raw16230Labels = mixedMoment B raw16230step0 raw16230step0Labels := by
      have hz : ∀ j, raw16230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16230step0 = (fun i j => raw16230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16230step0 raw16230; decide +kernel
      have hl : raw16230step0Labels = raw16230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16230 raw16230Labels permutation434 hz
    mixedMoment B raw16230step0 raw16230step0Labels = mixedMoment B raw16230step1 raw16230step1Labels := by
      have ha : raw16230step1 = (fun i j => raw16230step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16230step1 raw16230step0; decide +kernel
      have hl : raw16230step1Labels = raw16230step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16230step0 raw16230step0Labels permutation56 permutation5
    mixedMoment B raw16230step1 raw16230step1Labels = mixedMoment B raw16230step2 raw16230step2Labels := by
      have ha : raw16230step2 = -raw16230step1 := by apply Matrix.ext; change ∀ i j, raw16230step2 i j = -(raw16230step1 i j); unfold raw16230step2 raw16230step1; decide +kernel
      have hl : raw16230step2Labels = raw16230step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16230step2 raw16230step2Labels = mixedMoment B raw16230step3 raw16230step3Labels := by
      have ha : raw16230step3 = raw16230step2 := by apply Matrix.ext; unfold raw16230step3 raw16230step2; decide +kernel
      have hl : raw16230step2Labels = labelEmbedding8 ∘ raw16230step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16230step2 raw16230step2Labels raw16230step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw16231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16231 raw16231Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw16231 raw16231Labels = mixedMoment B raw16231step0 raw16231step0Labels := by
      have ha : raw16231step0 = (fun i j => raw16231 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16231step0 raw16231; decide +kernel
      have hl : raw16231step0Labels = raw16231Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16231 raw16231Labels permutation200 permutation2
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw16232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16232 raw16232Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw16232 raw16232Labels = mixedMoment B raw16232step0 raw16232step0Labels := by
      have hz : ∀ j, raw16232 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16232step0 = (fun i j => raw16232 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16232step0 raw16232; decide +kernel
      have hl : raw16232step0Labels = raw16232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16232 raw16232Labels permutation520 hz
    mixedMoment B raw16232step0 raw16232step0Labels = mixedMoment B raw16232step1 raw16232step1Labels := by
      have hz : ∀ j, raw16232step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw16232step1 = (fun i j => raw16232step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw16232step1 raw16232step0; decide +kernel
      have hl : raw16232step1Labels = raw16232step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16232step0 raw16232step0Labels permutation104 hz
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw16233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16233 raw16233Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw16233 raw16233Labels = mixedMoment B raw16233step0 raw16233step0Labels := by
      have hz : ∀ j, raw16233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16233step0 = (fun i j => raw16233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16233step0 raw16233; decide +kernel
      have hl : raw16233step0Labels = raw16233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16233 raw16233Labels permutation434 hz
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw16234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16234 raw16234Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw16234 raw16234Labels = mixedMoment B raw16234step0 raw16234step0Labels := by
      have hz : ∀ j, raw16234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16234step0 = (fun i j => raw16234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16234step0 raw16234; decide +kernel
      have hl : raw16234step0Labels = raw16234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16234 raw16234Labels permutation346 hz
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw16235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16235step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16235step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw16235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16235 raw16235Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw16235 raw16235Labels = mixedMoment B raw16235step0 raw16235step0Labels := by
      have hz : ∀ j, raw16235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16235step0 = (fun i j => raw16235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16235step0 raw16235; decide +kernel
      have hl : raw16235step0Labels = raw16235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16235 raw16235Labels permutation346 hz
    mixedMoment B raw16235step0 raw16235step0Labels = mixedMoment B raw16235step1 raw16235step1Labels := by
      have ha : raw16235step1 = (fun i j => raw16235step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16235step1 raw16235step0; decide +kernel
      have hl : raw16235step1Labels = raw16235step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16235step0 raw16235step0Labels permutation56 permutation5
    mixedMoment B raw16235step1 raw16235step1Labels = mixedMoment B raw16235step2 raw16235step2Labels := by
      have ha : raw16235step2 = -raw16235step1 := by apply Matrix.ext; change ∀ i j, raw16235step2 i j = -(raw16235step1 i j); unfold raw16235step2 raw16235step1; decide +kernel
      have hl : raw16235step2Labels = raw16235step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16235step2 raw16235step2Labels = mixedMoment B raw16235step3 raw16235step3Labels := by
      have ha : raw16235step3 = raw16235step2 := by apply Matrix.ext; unfold raw16235step3 raw16235step2; decide +kernel
      have hl : raw16235step2Labels = labelEmbedding8 ∘ raw16235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16235step2 raw16235step2Labels raw16235step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw16236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16236 raw16236Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw16236 raw16236Labels = mixedMoment B raw16236step0 raw16236step0Labels := by
      have ha : raw16236step0 = (fun i j => raw16236 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16236step0 raw16236; decide +kernel
      have hl : raw16236step0Labels = raw16236Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16236 raw16236Labels permutation176 permutation2
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw16237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16237step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16237 raw16237Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw16237 raw16237Labels = mixedMoment B raw16237step0 raw16237step0Labels := by
      have hz : ∀ j, raw16237 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16237step0 = (fun i j => raw16237 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16237step0 raw16237; decide +kernel
      have hl : raw16237step0Labels = raw16237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16237 raw16237Labels permutation520 hz
    mixedMoment B raw16237step0 raw16237step0Labels = mixedMoment B raw16237step1 raw16237step1Labels := by
      have hz : ∀ j, raw16237step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16237step1 = (fun i j => raw16237step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16237step1 raw16237step0; decide +kernel
      have hl : raw16237step1Labels = raw16237step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16237step0 raw16237step0Labels permutation80 hz
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw16238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16238 raw16238Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw16238 raw16238Labels = mixedMoment B raw16238step0 raw16238step0Labels := by
      have hz : ∀ j, raw16238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16238step0 = (fun i j => raw16238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16238step0 raw16238; decide +kernel
      have hl : raw16238step0Labels = raw16238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16238 raw16238Labels permutation346 hz
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw16239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16239step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16239 raw16239Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw16239 raw16239Labels = mixedMoment B raw16239step0 raw16239step0Labels := by
      have hz : ∀ j, raw16239 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16239step0 = (fun i j => raw16239 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16239step0 raw16239; decide +kernel
      have hl : raw16239step0Labels = raw16239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16239 raw16239Labels permutation434 hz
    mixedMoment B raw16239step0 raw16239step0Labels = mixedMoment B raw16239step1 raw16239step1Labels := by
      have hz : ∀ j, raw16239step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16239step1 = (fun i j => raw16239step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16239step1 raw16239step0; decide +kernel
      have hl : raw16239step1Labels = raw16239step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16239step0 raw16239step0Labels permutation80 hz
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw16240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16240step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw16240step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16240step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw16240step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16240step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw16240step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16240 raw16240Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw16240 raw16240Labels = mixedMoment B raw16240step0 raw16240step0Labels := by
      have hz : ∀ j, raw16240 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16240step0 = (fun i j => raw16240 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16240step0 raw16240; decide +kernel
      have hl : raw16240step0Labels = raw16240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16240 raw16240Labels permutation434 hz
    mixedMoment B raw16240step0 raw16240step0Labels = mixedMoment B raw16240step1 raw16240step1Labels := by
      have hz : ∀ j, raw16240step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16240step1 = (fun i j => raw16240step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16240step1 raw16240step0; decide +kernel
      have hl : raw16240step1Labels = raw16240step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16240step0 raw16240step0Labels permutation80 hz
    mixedMoment B raw16240step1 raw16240step1Labels = mixedMoment B raw16240step2 raw16240step2Labels := by
      have ha : raw16240step2 = (fun i j => raw16240step1 (permutation15 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16240step2 raw16240step1; decide +kernel
      have hl : raw16240step2Labels = raw16240step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16240step1 raw16240step1Labels permutation15 permutation5
    mixedMoment B raw16240step2 raw16240step2Labels = mixedMoment B raw16240step3 raw16240step3Labels := by
      have ha : raw16240step3 = -raw16240step2 := by apply Matrix.ext; change ∀ i j, raw16240step3 i j = -(raw16240step2 i j); unfold raw16240step3 raw16240step2; decide +kernel
      have hl : raw16240step3Labels = raw16240step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16240step3 raw16240step3Labels = mixedMoment B raw16240step4 raw16240step4Labels := by
      have ha : raw16240step4 = raw16240step3 := by apply Matrix.ext; unfold raw16240step4 raw16240step3; decide +kernel
      have hl : raw16240step3Labels = labelEmbedding8 ∘ raw16240step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16240step3 raw16240step3Labels raw16240step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw16241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16241step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16241step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16241step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16241step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16241 raw16241Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw16241 raw16241Labels = mixedMoment B raw16241step0 raw16241step0Labels := by
      have hz : ∀ j, raw16241 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16241step0 = (fun i j => raw16241 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16241step0 raw16241; decide +kernel
      have hl : raw16241step0Labels = raw16241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16241 raw16241Labels permutation434 hz
    mixedMoment B raw16241step0 raw16241step0Labels = mixedMoment B raw16241step1 raw16241step1Labels := by
      have ha : raw16241step1 = (fun i j => raw16241step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16241step1 raw16241step0; decide +kernel
      have hl : raw16241step1Labels = raw16241step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16241step0 raw16241step0Labels permutation127 permutation3
    mixedMoment B raw16241step1 raw16241step1Labels = mixedMoment B raw16241step2 raw16241step2Labels := by
      have ha : raw16241step2 = -raw16241step1 := by apply Matrix.ext; change ∀ i j, raw16241step2 i j = -(raw16241step1 i j); unfold raw16241step2 raw16241step1; decide +kernel
      have hl : raw16241step2Labels = raw16241step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16241step2 raw16241step2Labels = mixedMoment B raw16241step3 raw16241step3Labels := by
      have ha : raw16241step3 = raw16241step2 := by apply Matrix.ext; unfold raw16241step3 raw16241step2; decide +kernel
      have hl : raw16241step2Labels = labelEmbedding6 ∘ raw16241step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16241step2 raw16241step2Labels raw16241step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw16242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16242step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16242step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16242step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16242step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16242 raw16242Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw16242 raw16242Labels = mixedMoment B raw16242step0 raw16242step0Labels := by
      have hz : ∀ j, raw16242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16242step0 = (fun i j => raw16242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16242step0 raw16242; decide +kernel
      have hl : raw16242step0Labels = raw16242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16242 raw16242Labels permutation346 hz
    mixedMoment B raw16242step0 raw16242step0Labels = mixedMoment B raw16242step1 raw16242step1Labels := by
      have ha : raw16242step1 = (fun i j => raw16242step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16242step1 raw16242step0; decide +kernel
      have hl : raw16242step1Labels = raw16242step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16242step0 raw16242step0Labels permutation127 permutation3
    mixedMoment B raw16242step1 raw16242step1Labels = mixedMoment B raw16242step2 raw16242step2Labels := by
      have ha : raw16242step2 = -raw16242step1 := by apply Matrix.ext; change ∀ i j, raw16242step2 i j = -(raw16242step1 i j); unfold raw16242step2 raw16242step1; decide +kernel
      have hl : raw16242step2Labels = raw16242step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16242step2 raw16242step2Labels = mixedMoment B raw16242step3 raw16242step3Labels := by
      have ha : raw16242step3 = raw16242step2 := by apply Matrix.ext; unfold raw16242step3 raw16242step2; decide +kernel
      have hl : raw16242step2Labels = labelEmbedding6 ∘ raw16242step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16242step2 raw16242step2Labels raw16242step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw16243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw16243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw16243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16243step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16243step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16243step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16243step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16243step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16243step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16243step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16243 raw16243Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw16243 raw16243Labels = mixedMoment B raw16243step0 raw16243step0Labels := by
      have hz : ∀ j, raw16243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16243step0 = (fun i j => raw16243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16243step0 raw16243; decide +kernel
      have hl : raw16243step0Labels = raw16243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16243 raw16243Labels permutation434 hz
    mixedMoment B raw16243step0 raw16243step0Labels = mixedMoment B raw16243step1 raw16243step1Labels := by
      have hz : ∀ j, raw16243step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16243step1 = (fun i j => raw16243step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16243step1 raw16243step0; decide +kernel
      have hl : raw16243step1Labels = raw16243step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16243step0 raw16243step0Labels permutation80 hz
    mixedMoment B raw16243step1 raw16243step1Labels = mixedMoment B raw16243step2 raw16243step2Labels := by
      have ha : raw16243step2 = (fun i j => raw16243step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16243step2 raw16243step1; decide +kernel
      have hl : raw16243step2Labels = raw16243step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16243step1 raw16243step1Labels permutation25 permutation3
    mixedMoment B raw16243step2 raw16243step2Labels = mixedMoment B raw16243step3 raw16243step3Labels := by
      have ha : raw16243step3 = -raw16243step2 := by apply Matrix.ext; change ∀ i j, raw16243step3 i j = -(raw16243step2 i j); unfold raw16243step3 raw16243step2; decide +kernel
      have hl : raw16243step3Labels = raw16243step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16243step3 raw16243step3Labels = mixedMoment B raw16243step4 raw16243step4Labels := by
      have ha : raw16243step4 = raw16243step3 := by apply Matrix.ext; unfold raw16243step4 raw16243step3; decide +kernel
      have hl : raw16243step3Labels = labelEmbedding6 ∘ raw16243step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16243step3 raw16243step3Labels raw16243step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw16244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16244step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw16244step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16244step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16244step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16244step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16244step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16244 raw16244Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw16244 raw16244Labels = mixedMoment B raw16244step0 raw16244step0Labels := by
      have hz : ∀ j, raw16244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16244step0 = (fun i j => raw16244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16244step0 raw16244; decide +kernel
      have hl : raw16244step0Labels = raw16244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16244 raw16244Labels permutation434 hz
    mixedMoment B raw16244step0 raw16244step0Labels = mixedMoment B raw16244step1 raw16244step1Labels := by
      have hz : ∀ j, raw16244step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16244step1 = (fun i j => raw16244step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16244step1 raw16244step0; decide +kernel
      have hl : raw16244step1Labels = raw16244step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16244step0 raw16244step0Labels permutation80 hz
    mixedMoment B raw16244step1 raw16244step1Labels = mixedMoment B raw16244step2 raw16244step2Labels := by
      have ha : raw16244step2 = (fun i j => raw16244step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16244step2 raw16244step1; decide +kernel
      have hl : raw16244step2Labels = raw16244step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16244step1 raw16244step1Labels permutation31 permutation3
    mixedMoment B raw16244step2 raw16244step2Labels = mixedMoment B raw16244step3 raw16244step3Labels := by
      have ha : raw16244step3 = -raw16244step2 := by apply Matrix.ext; change ∀ i j, raw16244step3 i j = -(raw16244step2 i j); unfold raw16244step3 raw16244step2; decide +kernel
      have hl : raw16244step3Labels = raw16244step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16244step3 raw16244step3Labels = mixedMoment B raw16244step4 raw16244step4Labels := by
      have ha : raw16244step4 = raw16244step3 := by apply Matrix.ext; unfold raw16244step4 raw16244step3; decide +kernel
      have hl : raw16244step3Labels = labelEmbedding6 ∘ raw16244step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16244step3 raw16244step3Labels raw16244step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw16245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw16245step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw16245step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16245step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw16245step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16245 raw16245Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw16245 raw16245Labels = mixedMoment B raw16245step0 raw16245step0Labels := by
      have hz : ∀ j, raw16245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16245step0 = (fun i j => raw16245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16245step0 raw16245; decide +kernel
      have hl : raw16245step0Labels = raw16245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16245 raw16245Labels permutation434 hz
    mixedMoment B raw16245step0 raw16245step0Labels = mixedMoment B raw16245step1 raw16245step1Labels := by
      have hz : ∀ j, raw16245step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16245step1 = (fun i j => raw16245step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16245step1 raw16245step0; decide +kernel
      have hl : raw16245step1Labels = raw16245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16245step0 raw16245step0Labels permutation80 hz
    mixedMoment B raw16245step1 raw16245step1Labels = mixedMoment B raw16245step2 raw16245step2Labels := by
      have ha : raw16245step2 = (fun i j => raw16245step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16245step2 raw16245step1; decide +kernel
      have hl : raw16245step2Labels = raw16245step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16245step1 raw16245step1Labels permutation30 permutation3
    mixedMoment B raw16245step2 raw16245step2Labels = mixedMoment B raw16245step3 raw16245step3Labels := by
      have ha : raw16245step3 = -raw16245step2 := by apply Matrix.ext; change ∀ i j, raw16245step3 i j = -(raw16245step2 i j); unfold raw16245step3 raw16245step2; decide +kernel
      have hl : raw16245step3Labels = raw16245step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16245step3 raw16245step3Labels = mixedMoment B raw16245step4 raw16245step4Labels := by
      have ha : raw16245step4 = raw16245step3 := by apply Matrix.ext; unfold raw16245step4 raw16245step3; decide +kernel
      have hl : raw16245step3Labels = labelEmbedding6 ∘ raw16245step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16245step3 raw16245step3Labels raw16245step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw16246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16246step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16246step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16246step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16246step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16246 raw16246Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw16246 raw16246Labels = mixedMoment B raw16246step0 raw16246step0Labels := by
      have hz : ∀ j, raw16246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16246step0 = (fun i j => raw16246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16246step0 raw16246; decide +kernel
      have hl : raw16246step0Labels = raw16246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16246 raw16246Labels permutation434 hz
    mixedMoment B raw16246step0 raw16246step0Labels = mixedMoment B raw16246step1 raw16246step1Labels := by
      have ha : raw16246step1 = (fun i j => raw16246step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16246step1 raw16246step0; decide +kernel
      have hl : raw16246step1Labels = raw16246step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16246step0 raw16246step0Labels permutation151 permutation3
    mixedMoment B raw16246step1 raw16246step1Labels = mixedMoment B raw16246step2 raw16246step2Labels := by
      have ha : raw16246step2 = -raw16246step1 := by apply Matrix.ext; change ∀ i j, raw16246step2 i j = -(raw16246step1 i j); unfold raw16246step2 raw16246step1; decide +kernel
      have hl : raw16246step2Labels = raw16246step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16246step2 raw16246step2Labels = mixedMoment B raw16246step3 raw16246step3Labels := by
      have ha : raw16246step3 = raw16246step2 := by apply Matrix.ext; unfold raw16246step3 raw16246step2; decide +kernel
      have hl : raw16246step2Labels = labelEmbedding6 ∘ raw16246step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16246step2 raw16246step2Labels raw16246step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw16247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16247step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16247step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16247step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16247step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16247 raw16247Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw16247 raw16247Labels = mixedMoment B raw16247step0 raw16247step0Labels := by
      have hz : ∀ j, raw16247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16247step0 = (fun i j => raw16247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16247step0 raw16247; decide +kernel
      have hl : raw16247step0Labels = raw16247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16247 raw16247Labels permutation346 hz
    mixedMoment B raw16247step0 raw16247step0Labels = mixedMoment B raw16247step1 raw16247step1Labels := by
      have ha : raw16247step1 = (fun i j => raw16247step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16247step1 raw16247step0; decide +kernel
      have hl : raw16247step1Labels = raw16247step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16247step0 raw16247step0Labels permutation151 permutation3
    mixedMoment B raw16247step1 raw16247step1Labels = mixedMoment B raw16247step2 raw16247step2Labels := by
      have ha : raw16247step2 = -raw16247step1 := by apply Matrix.ext; change ∀ i j, raw16247step2 i j = -(raw16247step1 i j); unfold raw16247step2 raw16247step1; decide +kernel
      have hl : raw16247step2Labels = raw16247step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16247step2 raw16247step2Labels = mixedMoment B raw16247step3 raw16247step3Labels := by
      have ha : raw16247step3 = raw16247step2 := by apply Matrix.ext; unfold raw16247step3 raw16247step2; decide +kernel
      have hl : raw16247step2Labels = labelEmbedding6 ∘ raw16247step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16247step2 raw16247step2Labels raw16247step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw16248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw16248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw16248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16248step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![3, -2, -1]]
def raw16248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16248step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16248step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16248step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16248step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16248step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16248step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16248 raw16248Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw16248 raw16248Labels = mixedMoment B raw16248step0 raw16248step0Labels := by
      have hz : ∀ j, raw16248 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16248step0 = (fun i j => raw16248 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16248step0 raw16248; decide +kernel
      have hl : raw16248step0Labels = raw16248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16248 raw16248Labels permutation520 hz
    mixedMoment B raw16248step0 raw16248step0Labels = mixedMoment B raw16248step1 raw16248step1Labels := by
      have hz : ∀ j, raw16248step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw16248step1 = (fun i j => raw16248step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw16248step1 raw16248step0; decide +kernel
      have hl : raw16248step1Labels = raw16248step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16248step0 raw16248step0Labels permutation104 hz
    mixedMoment B raw16248step1 raw16248step1Labels = mixedMoment B raw16248step2 raw16248step2Labels := by
      have hz : ∀ j, raw16248step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw16248step2 = (fun i j => raw16248step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw16248step2 raw16248step1; decide +kernel
      have hl : raw16248step2Labels = raw16248step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16248step1 raw16248step1Labels permutation20 hz
    mixedMoment B raw16248step2 raw16248step2Labels = mixedMoment B raw16248step3 raw16248step3Labels := by
      have ha : raw16248step3 = (fun i j => raw16248step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16248step3 raw16248step2; decide +kernel
      have hl : raw16248step3Labels = raw16248step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16248step2 raw16248step2Labels permutation7 permutation3
    mixedMoment B raw16248step3 raw16248step3Labels = mixedMoment B raw16248step4 raw16248step4Labels := by
      have ha : raw16248step4 = -raw16248step3 := by apply Matrix.ext; change ∀ i j, raw16248step4 i j = -(raw16248step3 i j); unfold raw16248step4 raw16248step3; decide +kernel
      have hl : raw16248step4Labels = raw16248step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16248step4 raw16248step4Labels = mixedMoment B raw16248step5 raw16248step5Labels := by
      have ha : raw16248step5 = raw16248step4 := by apply Matrix.ext; unfold raw16248step5 raw16248step4; decide +kernel
      have hl : raw16248step4Labels = labelEmbedding6 ∘ raw16248step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16248step4 raw16248step4Labels raw16248step5Labels labelEmbedding6 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw16249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16249step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16249step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16249step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16249step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16249 raw16249Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw16249 raw16249Labels = mixedMoment B raw16249step0 raw16249step0Labels := by
      have hz : ∀ j, raw16249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16249step0 = (fun i j => raw16249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16249step0 raw16249; decide +kernel
      have hl : raw16249step0Labels = raw16249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16249 raw16249Labels permutation434 hz
    mixedMoment B raw16249step0 raw16249step0Labels = mixedMoment B raw16249step1 raw16249step1Labels := by
      have hz : ∀ j, raw16249step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16249step1 = (fun i j => raw16249step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16249step1 raw16249step0; decide +kernel
      have hl : raw16249step1Labels = raw16249step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16249step0 raw16249step0Labels permutation80 hz
    mixedMoment B raw16249step1 raw16249step1Labels = mixedMoment B raw16249step2 raw16249step2Labels := by
      have ha : raw16249step2 = (fun i j => raw16249step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16249step2 raw16249step1; decide +kernel
      have hl : raw16249step2Labels = raw16249step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16249step1 raw16249step1Labels permutation14 permutation3
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw16250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16250 raw16250Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw16250 raw16250Labels = mixedMoment B raw16250step0 raw16250step0Labels := by
      have hz : ∀ j, raw16250 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16250step0 = (fun i j => raw16250 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16250step0 raw16250; decide +kernel
      have hl : raw16250step0Labels = raw16250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16250 raw16250Labels permutation434 hz
    mixedMoment B raw16250step0 raw16250step0Labels = mixedMoment B raw16250step1 raw16250step1Labels := by
      have ha : raw16250step1 = (fun i j => raw16250step0 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16250step1 raw16250step0; decide +kernel
      have hl : raw16250step1Labels = raw16250step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16250step0 raw16250step0Labels permutation147 permutation3
    mixedMoment B raw16250step1 raw16250step1Labels = mixedMoment B raw16250step2 raw16250step2Labels := by
      have ha : raw16250step2 = -raw16250step1 := by apply Matrix.ext; change ∀ i j, raw16250step2 i j = -(raw16250step1 i j); unfold raw16250step2 raw16250step1; decide +kernel
      have hl : raw16250step2Labels = raw16250step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw16251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16251 raw16251Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw16251 raw16251Labels = mixedMoment B raw16251step0 raw16251step0Labels := by
      have hz : ∀ j, raw16251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16251step0 = (fun i j => raw16251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16251step0 raw16251; decide +kernel
      have hl : raw16251step0Labels = raw16251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16251 raw16251Labels permutation346 hz
    mixedMoment B raw16251step0 raw16251step0Labels = mixedMoment B raw16251step1 raw16251step1Labels := by
      have ha : raw16251step1 = (fun i j => raw16251step0 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16251step1 raw16251step0; decide +kernel
      have hl : raw16251step1Labels = raw16251step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16251step0 raw16251step0Labels permutation147 permutation3
    mixedMoment B raw16251step1 raw16251step1Labels = mixedMoment B raw16251step2 raw16251step2Labels := by
      have ha : raw16251step2 = -raw16251step1 := by apply Matrix.ext; change ∀ i j, raw16251step2 i j = -(raw16251step1 i j); unfold raw16251step2 raw16251step1; decide +kernel
      have hl : raw16251step2Labels = raw16251step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw16252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16252step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16252step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![2, -1, -1]]
def raw16252step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16252step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw16252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16252step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw16252step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16252 raw16252Labels = mixedMoment B node4020 node4020Labels := by
  calc
    mixedMoment B raw16252 raw16252Labels = mixedMoment B raw16252step0 raw16252step0Labels := by
      have hz : ∀ j, raw16252 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16252step0 = (fun i j => raw16252 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16252step0 raw16252; decide +kernel
      have hl : raw16252step0Labels = raw16252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16252 raw16252Labels permutation520 hz
    mixedMoment B raw16252step0 raw16252step0Labels = mixedMoment B raw16252step1 raw16252step1Labels := by
      have hz : ∀ j, raw16252step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw16252step1 = (fun i j => raw16252step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw16252step1 raw16252step0; decide +kernel
      have hl : raw16252step1Labels = raw16252step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16252step0 raw16252step0Labels permutation104 hz
    mixedMoment B raw16252step1 raw16252step1Labels = mixedMoment B raw16252step2 raw16252step2Labels := by
      have hz : ∀ j, raw16252step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw16252step2 = (fun i j => raw16252step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw16252step2 raw16252step1; decide +kernel
      have hl : raw16252step2Labels = raw16252step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16252step1 raw16252step1Labels permutation20 hz
    mixedMoment B raw16252step2 raw16252step2Labels = mixedMoment B raw16252step3 raw16252step3Labels := by
      have ha : raw16252step3 = (fun i j => raw16252step2 (permutation6 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16252step3 raw16252step2; decide +kernel
      have hl : raw16252step3Labels = raw16252step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16252step2 raw16252step2Labels permutation6 permutation3
    mixedMoment B raw16252step3 raw16252step3Labels = mixedMoment B raw16252step4 raw16252step4Labels := by
      have ha : raw16252step4 = -raw16252step3 := by apply Matrix.ext; change ∀ i j, raw16252step4 i j = -(raw16252step3 i j); unfold raw16252step4 raw16252step3; decide +kernel
      have hl : raw16252step4Labels = raw16252step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4020 node4020Labels := by rfl

def raw16253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16253step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16253step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16253step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16253step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16253step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16253step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16253 raw16253Labels = mixedMoment B node4015 node4015Labels := by
  calc
    mixedMoment B raw16253 raw16253Labels = mixedMoment B raw16253step0 raw16253step0Labels := by
      have hz : ∀ j, raw16253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16253step0 = (fun i j => raw16253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16253step0 raw16253; decide +kernel
      have hl : raw16253step0Labels = raw16253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16253 raw16253Labels permutation434 hz
    mixedMoment B raw16253step0 raw16253step0Labels = mixedMoment B raw16253step1 raw16253step1Labels := by
      have hz : ∀ j, raw16253step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16253step1 = (fun i j => raw16253step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16253step1 raw16253step0; decide +kernel
      have hl : raw16253step1Labels = raw16253step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16253step0 raw16253step0Labels permutation80 hz
    mixedMoment B raw16253step1 raw16253step1Labels = mixedMoment B raw16253step2 raw16253step2Labels := by
      have ha : raw16253step2 = (fun i j => raw16253step1 (permutation11 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16253step2 raw16253step1; decide +kernel
      have hl : raw16253step2Labels = raw16253step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16253step1 raw16253step1Labels permutation11 permutation6
    mixedMoment B raw16253step2 raw16253step2Labels = mixedMoment B raw16253step3 raw16253step3Labels := by
      have ha : raw16253step3 = -raw16253step2 := by apply Matrix.ext; change ∀ i j, raw16253step3 i j = -(raw16253step2 i j); unfold raw16253step3 raw16253step2; decide +kernel
      have hl : raw16253step3Labels = raw16253step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw16254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16254step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16254step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16254 raw16254Labels = mixedMoment B node3102 node3102Labels := by
  calc
    mixedMoment B raw16254 raw16254Labels = mixedMoment B raw16254step0 raw16254step0Labels := by
      have hz : ∀ j, raw16254 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16254step0 = (fun i j => raw16254 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16254step0 raw16254; decide +kernel
      have hl : raw16254step0Labels = raw16254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16254 raw16254Labels permutation434 hz
    mixedMoment B raw16254step0 raw16254step0Labels = mixedMoment B raw16254step1 raw16254step1Labels := by
      have hz : ∀ j, raw16254step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16254step1 = (fun i j => raw16254step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16254step1 raw16254step0; decide +kernel
      have hl : raw16254step1Labels = raw16254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16254step0 raw16254step0Labels permutation80 hz
    mixedMoment B raw16254step1 raw16254step1Labels = mixedMoment B raw16254step2 raw16254step2Labels := by
      have ha : raw16254step2 = (fun i j => raw16254step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16254step2 raw16254step1; decide +kernel
      have hl : raw16254step2Labels = raw16254step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16254step1 raw16254step1Labels permutation8 permutation3
    _ = mixedMoment B node3102 node3102Labels := by rfl

def raw16255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16255step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16255 raw16255Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw16255 raw16255Labels = mixedMoment B raw16255step0 raw16255step0Labels := by
      have hz : ∀ j, raw16255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16255step0 = (fun i j => raw16255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16255step0 raw16255; decide +kernel
      have hl : raw16255step0Labels = raw16255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16255 raw16255Labels permutation434 hz
    mixedMoment B raw16255step0 raw16255step0Labels = mixedMoment B raw16255step1 raw16255step1Labels := by
      have ha : raw16255step1 = (fun i j => raw16255step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16255step1 raw16255step0; decide +kernel
      have hl : raw16255step1Labels = raw16255step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16255step0 raw16255step0Labels permutation149 permutation3
    mixedMoment B raw16255step1 raw16255step1Labels = mixedMoment B raw16255step2 raw16255step2Labels := by
      have ha : raw16255step2 = -raw16255step1 := by apply Matrix.ext; change ∀ i j, raw16255step2 i j = -(raw16255step1 i j); unfold raw16255step2 raw16255step1; decide +kernel
      have hl : raw16255step2Labels = raw16255step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3982 node3982Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
