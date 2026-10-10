import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw8064 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8064step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8064 raw8064Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw8064 raw8064Labels = mixedMoment B raw8064step0 raw8064step0Labels := by
      have ha : raw8064step0 = (fun i j => raw8064 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8064step0 raw8064; decide +kernel
      have hl : raw8064step0Labels = raw8064Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8064 raw8064Labels permutation176 permutation6
    mixedMoment B raw8064step0 raw8064step0Labels = mixedMoment B raw8064step1 raw8064step1Labels := by
      have ha : raw8064step1 = raw8064step0 := by apply Matrix.ext; unfold raw8064step1 raw8064step0; decide +kernel
      have hl : raw8064step0Labels = labelEmbedding9 ∘ raw8064step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8064step0 raw8064step0Labels raw8064step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw8065 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw8065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8065 raw8065Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw8065 raw8065Labels = mixedMoment B raw8065step0 raw8065step0Labels := by
      have hz : ∀ j, raw8065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8065step0 = (fun i j => raw8065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8065step0 raw8065; decide +kernel
      have hl : raw8065step0Labels = raw8065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8065 raw8065Labels permutation346 hz
    mixedMoment B raw8065step0 raw8065step0Labels = mixedMoment B raw8065step1 raw8065step1Labels := by
      have ha : raw8065step1 = (fun i j => raw8065step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8065step1 raw8065step0; decide +kernel
      have hl : raw8065step1Labels = raw8065step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8065step0 raw8065step0Labels permutation149 permutation2
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw8066 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8066 raw8066Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw8066 raw8066Labels = mixedMoment B raw8066step0 raw8066step0Labels := by
      have hz : ∀ j, raw8066 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8066step0 = (fun i j => raw8066 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8066step0 raw8066; decide +kernel
      have hl : raw8066step0Labels = raw8066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8066 raw8066Labels permutation265 hz
    mixedMoment B raw8066step0 raw8066step0Labels = mixedMoment B raw8066step1 raw8066step1Labels := by
      have ha : raw8066step1 = (fun i j => raw8066step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8066step1 raw8066step0; decide +kernel
      have hl : raw8066step1Labels = raw8066step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8066step0 raw8066step0Labels permutation32 permutation6
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw8067 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8067step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw8067step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8067 raw8067Labels = mixedMoment B node3113 node3113Labels := by
  calc
    mixedMoment B raw8067 raw8067Labels = mixedMoment B raw8067step0 raw8067step0Labels := by
      have hz : ∀ j, raw8067 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8067step0 = (fun i j => raw8067 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8067step0 raw8067; decide +kernel
      have hl : raw8067step0Labels = raw8067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8067 raw8067Labels permutation346 hz
    mixedMoment B raw8067step0 raw8067step0Labels = mixedMoment B raw8067step1 raw8067step1Labels := by
      have hz : ∀ j, raw8067step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8067step1 = (fun i j => raw8067step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8067step1 raw8067step0; decide +kernel
      have hl : raw8067step1Labels = raw8067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8067step0 raw8067step0Labels permutation56 hz
    mixedMoment B raw8067step1 raw8067step1Labels = mixedMoment B raw8067step2 raw8067step2Labels := by
      have ha : raw8067step2 = (fun i j => raw8067step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8067step2 raw8067step1; decide +kernel
      have hl : raw8067step2Labels = raw8067step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8067step1 raw8067step1Labels permutation31 permutation3
    _ = mixedMoment B node3113 node3113Labels := by rfl

def raw8068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw8068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8068 raw8068Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw8068 raw8068Labels = mixedMoment B raw8068step0 raw8068step0Labels := by
      have ha : raw8068step0 = (fun i j => raw8068 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8068step0 raw8068; decide +kernel
      have hl : raw8068step0Labels = raw8068Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8068 raw8068Labels permutation176 permutation6
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw8069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw8069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw8069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8069 raw8069Labels = mixedMoment B node2754 node2754Labels := by
  calc
    mixedMoment B raw8069 raw8069Labels = mixedMoment B raw8069step0 raw8069step0Labels := by
      have hz : ∀ j, raw8069 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8069step0 = (fun i j => raw8069 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8069step0 raw8069; decide +kernel
      have hl : raw8069step0Labels = raw8069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8069 raw8069Labels permutation346 hz
    mixedMoment B raw8069step0 raw8069step0Labels = mixedMoment B raw8069step1 raw8069step1Labels := by
      have ha : raw8069step1 = (fun i j => raw8069step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8069step1 raw8069step0; decide +kernel
      have hl : raw8069step1Labels = raw8069step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8069step0 raw8069step0Labels permutation32 permutation6
    _ = mixedMoment B node2754 node2754Labels := by rfl

def raw8070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8070step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8070 raw8070Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw8070 raw8070Labels = mixedMoment B raw8070step0 raw8070step0Labels := by
      have hz : ∀ j, raw8070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8070step0 = (fun i j => raw8070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8070step0 raw8070; decide +kernel
      have hl : raw8070step0Labels = raw8070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8070 raw8070Labels permutation346 hz
    mixedMoment B raw8070step0 raw8070step0Labels = mixedMoment B raw8070step1 raw8070step1Labels := by
      have ha : raw8070step1 = (fun i j => raw8070step0 (permutation133 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8070step1 raw8070step0; decide +kernel
      have hl : raw8070step1Labels = raw8070step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8070step0 raw8070step0Labels permutation133 permutation5
    mixedMoment B raw8070step1 raw8070step1Labels = mixedMoment B raw8070step2 raw8070step2Labels := by
      have ha : raw8070step2 = raw8070step1 := by apply Matrix.ext; unfold raw8070step2 raw8070step1; decide +kernel
      have hl : raw8070step1Labels = labelEmbedding8 ∘ raw8070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8070step1 raw8070step1Labels raw8070step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw8071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8071step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8071 raw8071Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw8071 raw8071Labels = mixedMoment B raw8071step0 raw8071step0Labels := by
      have hz : ∀ j, raw8071 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8071step0 = (fun i j => raw8071 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8071step0 raw8071; decide +kernel
      have hl : raw8071step0Labels = raw8071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8071 raw8071Labels permutation265 hz
    mixedMoment B raw8071step0 raw8071step0Labels = mixedMoment B raw8071step1 raw8071step1Labels := by
      have ha : raw8071step1 = (fun i j => raw8071step0 (permutation133 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8071step1 raw8071step0; decide +kernel
      have hl : raw8071step1Labels = raw8071step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8071step0 raw8071step0Labels permutation133 permutation5
    mixedMoment B raw8071step1 raw8071step1Labels = mixedMoment B raw8071step2 raw8071step2Labels := by
      have ha : raw8071step2 = raw8071step1 := by apply Matrix.ext; unfold raw8071step2 raw8071step1; decide +kernel
      have hl : raw8071step1Labels = labelEmbedding8 ∘ raw8071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8071step1 raw8071step1Labels raw8071step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw8072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8072step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8072step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8072step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8072 raw8072Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw8072 raw8072Labels = mixedMoment B raw8072step0 raw8072step0Labels := by
      have hz : ∀ j, raw8072 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8072step0 = (fun i j => raw8072 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8072step0 raw8072; decide +kernel
      have hl : raw8072step0Labels = raw8072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8072 raw8072Labels permutation346 hz
    mixedMoment B raw8072step0 raw8072step0Labels = mixedMoment B raw8072step1 raw8072step1Labels := by
      have hz : ∀ j, raw8072step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8072step1 = (fun i j => raw8072step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8072step1 raw8072step0; decide +kernel
      have hl : raw8072step1Labels = raw8072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8072step0 raw8072step0Labels permutation56 hz
    mixedMoment B raw8072step1 raw8072step1Labels = mixedMoment B raw8072step2 raw8072step2Labels := by
      have ha : raw8072step2 = (fun i j => raw8072step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8072step2 raw8072step1; decide +kernel
      have hl : raw8072step2Labels = raw8072step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8072step1 raw8072step1Labels permutation27 permutation5
    mixedMoment B raw8072step2 raw8072step2Labels = mixedMoment B raw8072step3 raw8072step3Labels := by
      have ha : raw8072step3 = raw8072step2 := by apply Matrix.ext; unfold raw8072step3 raw8072step2; decide +kernel
      have hl : raw8072step2Labels = labelEmbedding8 ∘ raw8072step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8072step2 raw8072step2Labels raw8072step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw8073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8073step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8073step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8073step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8073 raw8073Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw8073 raw8073Labels = mixedMoment B raw8073step0 raw8073step0Labels := by
      have hz : ∀ j, raw8073 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8073step0 = (fun i j => raw8073 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8073step0 raw8073; decide +kernel
      have hl : raw8073step0Labels = raw8073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8073 raw8073Labels permutation346 hz
    mixedMoment B raw8073step0 raw8073step0Labels = mixedMoment B raw8073step1 raw8073step1Labels := by
      have hz : ∀ j, raw8073step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8073step1 = (fun i j => raw8073step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8073step1 raw8073step0; decide +kernel
      have hl : raw8073step1Labels = raw8073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8073step0 raw8073step0Labels permutation56 hz
    mixedMoment B raw8073step1 raw8073step1Labels = mixedMoment B raw8073step2 raw8073step2Labels := by
      have ha : raw8073step2 = (fun i j => raw8073step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8073step2 raw8073step1; decide +kernel
      have hl : raw8073step2Labels = raw8073step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8073step1 raw8073step1Labels permutation26 permutation5
    mixedMoment B raw8073step2 raw8073step2Labels = mixedMoment B raw8073step3 raw8073step3Labels := by
      have ha : raw8073step3 = raw8073step2 := by apply Matrix.ext; unfold raw8073step3 raw8073step2; decide +kernel
      have hl : raw8073step2Labels = labelEmbedding8 ∘ raw8073step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8073step2 raw8073step2Labels raw8073step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw8074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8074step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8074step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8074step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8074step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8074step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8074 raw8074Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw8074 raw8074Labels = mixedMoment B raw8074step0 raw8074step0Labels := by
      have hz : ∀ j, raw8074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8074step0 = (fun i j => raw8074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8074step0 raw8074; decide +kernel
      have hl : raw8074step0Labels = raw8074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8074 raw8074Labels permutation346 hz
    mixedMoment B raw8074step0 raw8074step0Labels = mixedMoment B raw8074step1 raw8074step1Labels := by
      have hz : ∀ j, raw8074step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8074step1 = (fun i j => raw8074step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8074step1 raw8074step0; decide +kernel
      have hl : raw8074step1Labels = raw8074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8074step0 raw8074step0Labels permutation56 hz
    mixedMoment B raw8074step1 raw8074step1Labels = mixedMoment B raw8074step2 raw8074step2Labels := by
      have ha : raw8074step2 = (fun i j => raw8074step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8074step2 raw8074step1; decide +kernel
      have hl : raw8074step2Labels = raw8074step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8074step1 raw8074step1Labels permutation12 permutation7
    mixedMoment B raw8074step2 raw8074step2Labels = mixedMoment B raw8074step3 raw8074step3Labels := by
      have ha : raw8074step3 = -raw8074step2 := by apply Matrix.ext; change ∀ i j, raw8074step3 i j = -(raw8074step2 i j); unfold raw8074step3 raw8074step2; decide +kernel
      have hl : raw8074step3Labels = raw8074step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8074step3 raw8074step3Labels = mixedMoment B raw8074step4 raw8074step4Labels := by
      have ha : raw8074step4 = raw8074step3 := by apply Matrix.ext; unfold raw8074step4 raw8074step3; decide +kernel
      have hl : raw8074step3Labels = labelEmbedding10 ∘ raw8074step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8074step3 raw8074step3Labels raw8074step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw8075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8075step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8075 raw8075Labels = mixedMoment B node4596 node4596Labels := by
  calc
    mixedMoment B raw8075 raw8075Labels = mixedMoment B raw8075step0 raw8075step0Labels := by
      have hz : ∀ j, raw8075 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8075step0 = (fun i j => raw8075 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8075step0 raw8075; decide +kernel
      have hl : raw8075step0Labels = raw8075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8075 raw8075Labels permutation346 hz
    mixedMoment B raw8075step0 raw8075step0Labels = mixedMoment B raw8075step1 raw8075step1Labels := by
      have ha : raw8075step1 = (fun i j => raw8075step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8075step1 raw8075step0; decide +kernel
      have hl : raw8075step1Labels = raw8075step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8075step0 raw8075step0Labels permutation40 permutation3
    mixedMoment B raw8075step1 raw8075step1Labels = mixedMoment B raw8075step2 raw8075step2Labels := by
      have ha : raw8075step2 = raw8075step1 := by apply Matrix.ext; unfold raw8075step2 raw8075step1; decide +kernel
      have hl : raw8075step1Labels = labelEmbedding6 ∘ raw8075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8075step1 raw8075step1Labels raw8075step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4596 node4596Labels := by rfl

def raw8076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8076step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8076 raw8076Labels = mixedMoment B node5091 node5091Labels := by
  calc
    mixedMoment B raw8076 raw8076Labels = mixedMoment B raw8076step0 raw8076step0Labels := by
      have ha : raw8076step0 = (fun i j => raw8076 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8076step0 raw8076; decide +kernel
      have hl : raw8076step0Labels = raw8076Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8076 raw8076Labels permutation622 permutation5
    mixedMoment B raw8076step0 raw8076step0Labels = mixedMoment B raw8076step1 raw8076step1Labels := by
      have ha : raw8076step1 = raw8076step0 := by apply Matrix.ext; unfold raw8076step1 raw8076step0; decide +kernel
      have hl : raw8076step0Labels = labelEmbedding8 ∘ raw8076step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8076step0 raw8076step0Labels raw8076step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5091 node5091Labels := by rfl

def raw8077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8077step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8077step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8077 raw8077Labels = mixedMoment B node5096 node5096Labels := by
  calc
    mixedMoment B raw8077 raw8077Labels = mixedMoment B raw8077step0 raw8077step0Labels := by
      have hz : ∀ j, raw8077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8077step0 = (fun i j => raw8077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8077step0 raw8077; decide +kernel
      have hl : raw8077step0Labels = raw8077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8077 raw8077Labels permutation346 hz
    mixedMoment B raw8077step0 raw8077step0Labels = mixedMoment B raw8077step1 raw8077step1Labels := by
      have ha : raw8077step1 = (fun i j => raw8077step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8077step1 raw8077step0; decide +kernel
      have hl : raw8077step1Labels = raw8077step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8077step0 raw8077step0Labels permutation138 permutation5
    mixedMoment B raw8077step1 raw8077step1Labels = mixedMoment B raw8077step2 raw8077step2Labels := by
      have ha : raw8077step2 = raw8077step1 := by apply Matrix.ext; unfold raw8077step2 raw8077step1; decide +kernel
      have hl : raw8077step1Labels = labelEmbedding8 ∘ raw8077step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8077step1 raw8077step1Labels raw8077step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5096 node5096Labels := by rfl

def raw8078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8078step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8078step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8078 raw8078Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw8078 raw8078Labels = mixedMoment B raw8078step0 raw8078step0Labels := by
      have hz : ∀ j, raw8078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8078step0 = (fun i j => raw8078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8078step0 raw8078; decide +kernel
      have hl : raw8078step0Labels = raw8078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8078 raw8078Labels permutation346 hz
    mixedMoment B raw8078step0 raw8078step0Labels = mixedMoment B raw8078step1 raw8078step1Labels := by
      have ha : raw8078step1 = (fun i j => raw8078step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8078step1 raw8078step0; decide +kernel
      have hl : raw8078step1Labels = raw8078step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8078step0 raw8078step0Labels permutation136 permutation5
    mixedMoment B raw8078step1 raw8078step1Labels = mixedMoment B raw8078step2 raw8078step2Labels := by
      have ha : raw8078step2 = raw8078step1 := by apply Matrix.ext; unfold raw8078step2 raw8078step1; decide +kernel
      have hl : raw8078step1Labels = labelEmbedding8 ∘ raw8078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8078step1 raw8078step1Labels raw8078step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw8079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8079 raw8079Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw8079 raw8079Labels = mixedMoment B raw8079step0 raw8079step0Labels := by
      have hz : ∀ j, raw8079 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8079step0 = (fun i j => raw8079 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8079step0 raw8079; decide +kernel
      have hl : raw8079step0Labels = raw8079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8079 raw8079Labels permutation346 hz
    mixedMoment B raw8079step0 raw8079step0Labels = mixedMoment B raw8079step1 raw8079step1Labels := by
      have ha : raw8079step1 = (fun i j => raw8079step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8079step1 raw8079step0; decide +kernel
      have hl : raw8079step1Labels = raw8079step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8079step0 raw8079step0Labels permutation42 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw8080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8080step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8080step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8080 raw8080Labels = mixedMoment B node4596 node4596Labels := by
  calc
    mixedMoment B raw8080 raw8080Labels = mixedMoment B raw8080step0 raw8080step0Labels := by
      have hz : ∀ j, raw8080 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8080step0 = (fun i j => raw8080 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8080step0 raw8080; decide +kernel
      have hl : raw8080step0Labels = raw8080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8080 raw8080Labels permutation265 hz
    mixedMoment B raw8080step0 raw8080step0Labels = mixedMoment B raw8080step1 raw8080step1Labels := by
      have ha : raw8080step1 = (fun i j => raw8080step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8080step1 raw8080step0; decide +kernel
      have hl : raw8080step1Labels = raw8080step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8080step0 raw8080step0Labels permutation40 permutation3
    mixedMoment B raw8080step1 raw8080step1Labels = mixedMoment B raw8080step2 raw8080step2Labels := by
      have ha : raw8080step2 = raw8080step1 := by apply Matrix.ext; unfold raw8080step2 raw8080step1; decide +kernel
      have hl : raw8080step1Labels = labelEmbedding6 ∘ raw8080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8080step1 raw8080step1Labels raw8080step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4596 node4596Labels := by rfl

def raw8081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8081step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8081 raw8081Labels = mixedMoment B node5091 node5091Labels := by
  calc
    mixedMoment B raw8081 raw8081Labels = mixedMoment B raw8081step0 raw8081step0Labels := by
      have ha : raw8081step0 = (fun i j => raw8081 (permutation646 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8081step0 raw8081; decide +kernel
      have hl : raw8081step0Labels = raw8081Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8081 raw8081Labels permutation646 permutation5
    mixedMoment B raw8081step0 raw8081step0Labels = mixedMoment B raw8081step1 raw8081step1Labels := by
      have ha : raw8081step1 = raw8081step0 := by apply Matrix.ext; unfold raw8081step1 raw8081step0; decide +kernel
      have hl : raw8081step0Labels = labelEmbedding8 ∘ raw8081step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8081step0 raw8081step0Labels raw8081step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5091 node5091Labels := by rfl

def raw8082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8082step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8082 raw8082Labels = mixedMoment B node5096 node5096Labels := by
  calc
    mixedMoment B raw8082 raw8082Labels = mixedMoment B raw8082step0 raw8082step0Labels := by
      have hz : ∀ j, raw8082 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8082step0 = (fun i j => raw8082 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8082step0 raw8082; decide +kernel
      have hl : raw8082step0Labels = raw8082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8082 raw8082Labels permutation265 hz
    mixedMoment B raw8082step0 raw8082step0Labels = mixedMoment B raw8082step1 raw8082step1Labels := by
      have ha : raw8082step1 = (fun i j => raw8082step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8082step1 raw8082step0; decide +kernel
      have hl : raw8082step1Labels = raw8082step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8082step0 raw8082step0Labels permutation138 permutation5
    mixedMoment B raw8082step1 raw8082step1Labels = mixedMoment B raw8082step2 raw8082step2Labels := by
      have ha : raw8082step2 = raw8082step1 := by apply Matrix.ext; unfold raw8082step2 raw8082step1; decide +kernel
      have hl : raw8082step1Labels = labelEmbedding8 ∘ raw8082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8082step1 raw8082step1Labels raw8082step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5096 node5096Labels := by rfl

def raw8083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8083step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8083step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8083 raw8083Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw8083 raw8083Labels = mixedMoment B raw8083step0 raw8083step0Labels := by
      have hz : ∀ j, raw8083 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8083step0 = (fun i j => raw8083 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8083step0 raw8083; decide +kernel
      have hl : raw8083step0Labels = raw8083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8083 raw8083Labels permutation265 hz
    mixedMoment B raw8083step0 raw8083step0Labels = mixedMoment B raw8083step1 raw8083step1Labels := by
      have ha : raw8083step1 = (fun i j => raw8083step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8083step1 raw8083step0; decide +kernel
      have hl : raw8083step1Labels = raw8083step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8083step0 raw8083step0Labels permutation136 permutation5
    mixedMoment B raw8083step1 raw8083step1Labels = mixedMoment B raw8083step2 raw8083step2Labels := by
      have ha : raw8083step2 = raw8083step1 := by apply Matrix.ext; unfold raw8083step2 raw8083step1; decide +kernel
      have hl : raw8083step1Labels = labelEmbedding8 ∘ raw8083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8083step1 raw8083step1Labels raw8083step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw8084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8084 raw8084Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw8084 raw8084Labels = mixedMoment B raw8084step0 raw8084step0Labels := by
      have hz : ∀ j, raw8084 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8084step0 = (fun i j => raw8084 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8084step0 raw8084; decide +kernel
      have hl : raw8084step0Labels = raw8084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8084 raw8084Labels permutation265 hz
    mixedMoment B raw8084step0 raw8084step0Labels = mixedMoment B raw8084step1 raw8084step1Labels := by
      have ha : raw8084step1 = (fun i j => raw8084step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8084step1 raw8084step0; decide +kernel
      have hl : raw8084step1Labels = raw8084step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8084step0 raw8084step0Labels permutation42 permutation2
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw8085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8085step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8085step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8085step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8085 raw8085Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw8085 raw8085Labels = mixedMoment B raw8085step0 raw8085step0Labels := by
      have hz : ∀ j, raw8085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8085step0 = (fun i j => raw8085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8085step0 raw8085; decide +kernel
      have hl : raw8085step0Labels = raw8085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8085 raw8085Labels permutation346 hz
    mixedMoment B raw8085step0 raw8085step0Labels = mixedMoment B raw8085step1 raw8085step1Labels := by
      have hz : ∀ j, raw8085step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8085step1 = (fun i j => raw8085step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8085step1 raw8085step0; decide +kernel
      have hl : raw8085step1Labels = raw8085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8085step0 raw8085step0Labels permutation56 hz
    mixedMoment B raw8085step1 raw8085step1Labels = mixedMoment B raw8085step2 raw8085step2Labels := by
      have ha : raw8085step2 = (fun i j => raw8085step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8085step2 raw8085step1; decide +kernel
      have hl : raw8085step2Labels = raw8085step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8085step1 raw8085step1Labels permutation10 permutation3
    mixedMoment B raw8085step2 raw8085step2Labels = mixedMoment B raw8085step3 raw8085step3Labels := by
      have ha : raw8085step3 = raw8085step2 := by apply Matrix.ext; unfold raw8085step3 raw8085step2; decide +kernel
      have hl : raw8085step2Labels = labelEmbedding6 ∘ raw8085step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8085step2 raw8085step2Labels raw8085step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw8086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8086 raw8086Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw8086 raw8086Labels = mixedMoment B raw8086step0 raw8086step0Labels := by
      have hz : ∀ j, raw8086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8086step0 = (fun i j => raw8086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8086step0 raw8086; decide +kernel
      have hl : raw8086step0Labels = raw8086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8086 raw8086Labels permutation346 hz
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw8087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8087 raw8087Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw8087 raw8087Labels = mixedMoment B raw8087step0 raw8087step0Labels := by
      have hz : ∀ j, raw8087 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8087step0 = (fun i j => raw8087 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8087step0 raw8087; decide +kernel
      have hl : raw8087step0Labels = raw8087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8087 raw8087Labels permutation265 hz
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw8088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8088step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8088step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8088 raw8088Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw8088 raw8088Labels = mixedMoment B raw8088step0 raw8088step0Labels := by
      have hz : ∀ j, raw8088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8088step0 = (fun i j => raw8088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8088step0 raw8088; decide +kernel
      have hl : raw8088step0Labels = raw8088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8088 raw8088Labels permutation346 hz
    mixedMoment B raw8088step0 raw8088step0Labels = mixedMoment B raw8088step1 raw8088step1Labels := by
      have hz : ∀ j, raw8088step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8088step1 = (fun i j => raw8088step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8088step1 raw8088step0; decide +kernel
      have hl : raw8088step1Labels = raw8088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8088step0 raw8088step0Labels permutation56 hz
    mixedMoment B raw8088step1 raw8088step1Labels = mixedMoment B raw8088step2 raw8088step2Labels := by
      have ha : raw8088step2 = (fun i j => raw8088step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8088step2 raw8088step1; decide +kernel
      have hl : raw8088step2Labels = raw8088step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8088step1 raw8088step1Labels permutation28 permutation5
    mixedMoment B raw8088step2 raw8088step2Labels = mixedMoment B raw8088step3 raw8088step3Labels := by
      have ha : raw8088step3 = raw8088step2 := by apply Matrix.ext; unfold raw8088step3 raw8088step2; decide +kernel
      have hl : raw8088step2Labels = labelEmbedding8 ∘ raw8088step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8088step2 raw8088step2Labels raw8088step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw8089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8089 raw8089Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw8089 raw8089Labels = mixedMoment B raw8089step0 raw8089step0Labels := by
      have hz : ∀ j, raw8089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8089step0 = (fun i j => raw8089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8089step0 raw8089; decide +kernel
      have hl : raw8089step0Labels = raw8089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8089 raw8089Labels permutation346 hz
    mixedMoment B raw8089step0 raw8089step0Labels = mixedMoment B raw8089step1 raw8089step1Labels := by
      have hz : ∀ j, raw8089step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8089step1 = (fun i j => raw8089step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8089step1 raw8089step0; decide +kernel
      have hl : raw8089step1Labels = raw8089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8089step0 raw8089step0Labels permutation56 hz
    mixedMoment B raw8089step1 raw8089step1Labels = mixedMoment B raw8089step2 raw8089step2Labels := by
      have ha : raw8089step2 = (fun i j => raw8089step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8089step2 raw8089step1; decide +kernel
      have hl : raw8089step2Labels = raw8089step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8089step1 raw8089step1Labels permutation12 permutation2
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw8090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw8090step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8090step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw8090step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8090 raw8090Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw8090 raw8090Labels = mixedMoment B raw8090step0 raw8090step0Labels := by
      have hz : ∀ j, raw8090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8090step0 = (fun i j => raw8090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8090step0 raw8090; decide +kernel
      have hl : raw8090step0Labels = raw8090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8090 raw8090Labels permutation346 hz
    mixedMoment B raw8090step0 raw8090step0Labels = mixedMoment B raw8090step1 raw8090step1Labels := by
      have hz : ∀ j, raw8090step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8090step1 = (fun i j => raw8090step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8090step1 raw8090step0; decide +kernel
      have hl : raw8090step1Labels = raw8090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8090step0 raw8090step0Labels permutation56 hz
    mixedMoment B raw8090step1 raw8090step1Labels = mixedMoment B raw8090step2 raw8090step2Labels := by
      have ha : raw8090step2 = (fun i j => raw8090step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8090step2 raw8090step1; decide +kernel
      have hl : raw8090step2Labels = raw8090step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8090step1 raw8090step1Labels permutation8 permutation3
    mixedMoment B raw8090step2 raw8090step2Labels = mixedMoment B raw8090step3 raw8090step3Labels := by
      have ha : raw8090step3 = raw8090step2 := by apply Matrix.ext; unfold raw8090step3 raw8090step2; decide +kernel
      have hl : raw8090step2Labels = labelEmbedding6 ∘ raw8090step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8090step2 raw8090step2Labels raw8090step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw8091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8091 raw8091Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw8091 raw8091Labels = mixedMoment B raw8091step0 raw8091step0Labels := by
      have hz : ∀ j, raw8091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8091step0 = (fun i j => raw8091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8091step0 raw8091; decide +kernel
      have hl : raw8091step0Labels = raw8091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8091 raw8091Labels permutation346 hz
    mixedMoment B raw8091step0 raw8091step0Labels = mixedMoment B raw8091step1 raw8091step1Labels := by
      have ha : raw8091step1 = (fun i j => raw8091step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8091step1 raw8091step0; decide +kernel
      have hl : raw8091step1Labels = raw8091step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8091step0 raw8091step0Labels permutation33 permutation2
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw8092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8092 raw8092Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw8092 raw8092Labels = mixedMoment B raw8092step0 raw8092step0Labels := by
      have hz : ∀ j, raw8092 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8092step0 = (fun i j => raw8092 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8092step0 raw8092; decide +kernel
      have hl : raw8092step0Labels = raw8092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8092 raw8092Labels permutation265 hz
    mixedMoment B raw8092step0 raw8092step0Labels = mixedMoment B raw8092step1 raw8092step1Labels := by
      have ha : raw8092step1 = (fun i j => raw8092step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8092step1 raw8092step0; decide +kernel
      have hl : raw8092step1Labels = raw8092step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8092step0 raw8092step0Labels permutation33 permutation2
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw8093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8093step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8093 raw8093Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw8093 raw8093Labels = mixedMoment B raw8093step0 raw8093step0Labels := by
      have hz : ∀ j, raw8093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8093step0 = (fun i j => raw8093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8093step0 raw8093; decide +kernel
      have hl : raw8093step0Labels = raw8093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8093 raw8093Labels permutation346 hz
    mixedMoment B raw8093step0 raw8093step0Labels = mixedMoment B raw8093step1 raw8093step1Labels := by
      have hz : ∀ j, raw8093step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8093step1 = (fun i j => raw8093step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8093step1 raw8093step0; decide +kernel
      have hl : raw8093step1Labels = raw8093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8093step0 raw8093step0Labels permutation56 hz
    mixedMoment B raw8093step1 raw8093step1Labels = mixedMoment B raw8093step2 raw8093step2Labels := by
      have ha : raw8093step2 = (fun i j => raw8093step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8093step2 raw8093step1; decide +kernel
      have hl : raw8093step2Labels = raw8093step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8093step1 raw8093step1Labels permutation9 permutation2
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw8094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8094step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8094 raw8094Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw8094 raw8094Labels = mixedMoment B raw8094step0 raw8094step0Labels := by
      have hz : ∀ j, raw8094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8094step0 = (fun i j => raw8094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8094step0 raw8094; decide +kernel
      have hl : raw8094step0Labels = raw8094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8094 raw8094Labels permutation346 hz
    mixedMoment B raw8094step0 raw8094step0Labels = mixedMoment B raw8094step1 raw8094step1Labels := by
      have hz : ∀ j, raw8094step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8094step1 = (fun i j => raw8094step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8094step1 raw8094step0; decide +kernel
      have hl : raw8094step1Labels = raw8094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8094step0 raw8094step0Labels permutation56 hz
    mixedMoment B raw8094step1 raw8094step1Labels = mixedMoment B raw8094step2 raw8094step2Labels := by
      have ha : raw8094step2 = (fun i j => raw8094step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8094step2 raw8094step1; decide +kernel
      have hl : raw8094step2Labels = raw8094step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8094step1 raw8094step1Labels permutation9 permutation2
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw8095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8095step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8095step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8095step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8095 raw8095Labels = mixedMoment B node4488 node4488Labels := by
  calc
    mixedMoment B raw8095 raw8095Labels = mixedMoment B raw8095step0 raw8095step0Labels := by
      have hz : ∀ j, raw8095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8095step0 = (fun i j => raw8095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8095step0 raw8095; decide +kernel
      have hl : raw8095step0Labels = raw8095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8095 raw8095Labels permutation346 hz
    mixedMoment B raw8095step0 raw8095step0Labels = mixedMoment B raw8095step1 raw8095step1Labels := by
      have hz : ∀ j, raw8095step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8095step1 = (fun i j => raw8095step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8095step1 raw8095step0; decide +kernel
      have hl : raw8095step1Labels = raw8095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8095step0 raw8095step0Labels permutation56 hz
    mixedMoment B raw8095step1 raw8095step1Labels = mixedMoment B raw8095step2 raw8095step2Labels := by
      have ha : raw8095step2 = (fun i j => raw8095step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8095step2 raw8095step1; decide +kernel
      have hl : raw8095step2Labels = raw8095step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8095step1 raw8095step1Labels permutation31 permutation5
    mixedMoment B raw8095step2 raw8095step2Labels = mixedMoment B raw8095step3 raw8095step3Labels := by
      have ha : raw8095step3 = raw8095step2 := by apply Matrix.ext; unfold raw8095step3 raw8095step2; decide +kernel
      have hl : raw8095step2Labels = labelEmbedding8 ∘ raw8095step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8095step2 raw8095step2Labels raw8095step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4488 node4488Labels := by rfl

def raw8096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8096step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8096step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8096 raw8096Labels = mixedMoment B node4486 node4486Labels := by
  calc
    mixedMoment B raw8096 raw8096Labels = mixedMoment B raw8096step0 raw8096step0Labels := by
      have hz : ∀ j, raw8096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8096step0 = (fun i j => raw8096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8096step0 raw8096; decide +kernel
      have hl : raw8096step0Labels = raw8096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8096 raw8096Labels permutation346 hz
    mixedMoment B raw8096step0 raw8096step0Labels = mixedMoment B raw8096step1 raw8096step1Labels := by
      have ha : raw8096step1 = (fun i j => raw8096step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8096step1 raw8096step0; decide +kernel
      have hl : raw8096step1Labels = raw8096step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8096step0 raw8096step0Labels permutation151 permutation5
    mixedMoment B raw8096step1 raw8096step1Labels = mixedMoment B raw8096step2 raw8096step2Labels := by
      have ha : raw8096step2 = raw8096step1 := by apply Matrix.ext; unfold raw8096step2 raw8096step1; decide +kernel
      have hl : raw8096step1Labels = labelEmbedding8 ∘ raw8096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8096step1 raw8096step1Labels raw8096step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4486 node4486Labels := by rfl

def raw8097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8097step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8097step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8097 raw8097Labels = mixedMoment B node4486 node4486Labels := by
  calc
    mixedMoment B raw8097 raw8097Labels = mixedMoment B raw8097step0 raw8097step0Labels := by
      have hz : ∀ j, raw8097 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8097step0 = (fun i j => raw8097 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8097step0 raw8097; decide +kernel
      have hl : raw8097step0Labels = raw8097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8097 raw8097Labels permutation265 hz
    mixedMoment B raw8097step0 raw8097step0Labels = mixedMoment B raw8097step1 raw8097step1Labels := by
      have ha : raw8097step1 = (fun i j => raw8097step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8097step1 raw8097step0; decide +kernel
      have hl : raw8097step1Labels = raw8097step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8097step0 raw8097step0Labels permutation151 permutation5
    mixedMoment B raw8097step1 raw8097step1Labels = mixedMoment B raw8097step2 raw8097step2Labels := by
      have ha : raw8097step2 = raw8097step1 := by apply Matrix.ext; unfold raw8097step2 raw8097step1; decide +kernel
      have hl : raw8097step1Labels = labelEmbedding8 ∘ raw8097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8097step1 raw8097step1Labels raw8097step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4486 node4486Labels := by rfl

def raw8098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8098step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8098step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8098step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8098step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8098 raw8098Labels = mixedMoment B node4492 node4492Labels := by
  calc
    mixedMoment B raw8098 raw8098Labels = mixedMoment B raw8098step0 raw8098step0Labels := by
      have hz : ∀ j, raw8098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8098step0 = (fun i j => raw8098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8098step0 raw8098; decide +kernel
      have hl : raw8098step0Labels = raw8098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8098 raw8098Labels permutation346 hz
    mixedMoment B raw8098step0 raw8098step0Labels = mixedMoment B raw8098step1 raw8098step1Labels := by
      have hz : ∀ j, raw8098step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8098step1 = (fun i j => raw8098step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8098step1 raw8098step0; decide +kernel
      have hl : raw8098step1Labels = raw8098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8098step0 raw8098step0Labels permutation56 hz
    mixedMoment B raw8098step1 raw8098step1Labels = mixedMoment B raw8098step2 raw8098step2Labels := by
      have ha : raw8098step2 = (fun i j => raw8098step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8098step2 raw8098step1; decide +kernel
      have hl : raw8098step2Labels = raw8098step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8098step1 raw8098step1Labels permutation30 permutation5
    mixedMoment B raw8098step2 raw8098step2Labels = mixedMoment B raw8098step3 raw8098step3Labels := by
      have ha : raw8098step3 = raw8098step2 := by apply Matrix.ext; unfold raw8098step3 raw8098step2; decide +kernel
      have hl : raw8098step2Labels = labelEmbedding8 ∘ raw8098step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8098step2 raw8098step2Labels raw8098step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4492 node4492Labels := by rfl

def raw8099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8099step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8099step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw8099step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8099step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8099 raw8099Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw8099 raw8099Labels = mixedMoment B raw8099step0 raw8099step0Labels := by
      have hz : ∀ j, raw8099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8099step0 = (fun i j => raw8099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8099step0 raw8099; decide +kernel
      have hl : raw8099step0Labels = raw8099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8099 raw8099Labels permutation346 hz
    mixedMoment B raw8099step0 raw8099step0Labels = mixedMoment B raw8099step1 raw8099step1Labels := by
      have hz : ∀ j, raw8099step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8099step1 = (fun i j => raw8099step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8099step1 raw8099step0; decide +kernel
      have hl : raw8099step1Labels = raw8099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8099step0 raw8099step0Labels permutation56 hz
    mixedMoment B raw8099step1 raw8099step1Labels = mixedMoment B raw8099step2 raw8099step2Labels := by
      have ha : raw8099step2 = (fun i j => raw8099step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8099step2 raw8099step1; decide +kernel
      have hl : raw8099step2Labels = raw8099step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8099step1 raw8099step1Labels permutation28 permutation5
    mixedMoment B raw8099step2 raw8099step2Labels = mixedMoment B raw8099step3 raw8099step3Labels := by
      have ha : raw8099step3 = raw8099step2 := by apply Matrix.ext; unfold raw8099step3 raw8099step2; decide +kernel
      have hl : raw8099step2Labels = labelEmbedding8 ∘ raw8099step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8099step2 raw8099step2Labels raw8099step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw8100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8100 raw8100Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw8100 raw8100Labels = mixedMoment B raw8100step0 raw8100step0Labels := by
      have hz : ∀ j, raw8100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8100step0 = (fun i j => raw8100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8100step0 raw8100; decide +kernel
      have hl : raw8100step0Labels = raw8100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8100 raw8100Labels permutation346 hz
    mixedMoment B raw8100step0 raw8100step0Labels = mixedMoment B raw8100step1 raw8100step1Labels := by
      have ha : raw8100step1 = (fun i j => raw8100step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8100step1 raw8100step0; decide +kernel
      have hl : raw8100step1Labels = raw8100step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8100step0 raw8100step0Labels permutation151 permutation3
    mixedMoment B raw8100step1 raw8100step1Labels = mixedMoment B raw8100step2 raw8100step2Labels := by
      have ha : raw8100step2 = -raw8100step1 := by apply Matrix.ext; change ∀ i j, raw8100step2 i j = -(raw8100step1 i j); unfold raw8100step2 raw8100step1; decide +kernel
      have hl : raw8100step2Labels = raw8100step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw8101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8101step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw8101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw8101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8101 raw8101Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw8101 raw8101Labels = mixedMoment B raw8101step0 raw8101step0Labels := by
      have hz : ∀ j, raw8101 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8101step0 = (fun i j => raw8101 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8101step0 raw8101; decide +kernel
      have hl : raw8101step0Labels = raw8101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8101 raw8101Labels permutation265 hz
    mixedMoment B raw8101step0 raw8101step0Labels = mixedMoment B raw8101step1 raw8101step1Labels := by
      have ha : raw8101step1 = (fun i j => raw8101step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8101step1 raw8101step0; decide +kernel
      have hl : raw8101step1Labels = raw8101step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8101step0 raw8101step0Labels permutation151 permutation3
    mixedMoment B raw8101step1 raw8101step1Labels = mixedMoment B raw8101step2 raw8101step2Labels := by
      have ha : raw8101step2 = -raw8101step1 := by apply Matrix.ext; change ∀ i j, raw8101step2 i j = -(raw8101step1 i j); unfold raw8101step2 raw8101step1; decide +kernel
      have hl : raw8101step2Labels = raw8101step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw8102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8102step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw8102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw8102step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8102 raw8102Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw8102 raw8102Labels = mixedMoment B raw8102step0 raw8102step0Labels := by
      have hz : ∀ j, raw8102 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8102step0 = (fun i j => raw8102 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8102step0 raw8102; decide +kernel
      have hl : raw8102step0Labels = raw8102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8102 raw8102Labels permutation346 hz
    mixedMoment B raw8102step0 raw8102step0Labels = mixedMoment B raw8102step1 raw8102step1Labels := by
      have hz : ∀ j, raw8102step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8102step1 = (fun i j => raw8102step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8102step1 raw8102step0; decide +kernel
      have hl : raw8102step1Labels = raw8102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8102step0 raw8102step0Labels permutation56 hz
    mixedMoment B raw8102step1 raw8102step1Labels = mixedMoment B raw8102step2 raw8102step2Labels := by
      have ha : raw8102step2 = (fun i j => raw8102step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8102step2 raw8102step1; decide +kernel
      have hl : raw8102step2Labels = raw8102step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8102step1 raw8102step1Labels permutation31 permutation3
    mixedMoment B raw8102step2 raw8102step2Labels = mixedMoment B raw8102step3 raw8102step3Labels := by
      have ha : raw8102step3 = -raw8102step2 := by apply Matrix.ext; change ∀ i j, raw8102step3 i j = -(raw8102step2 i j); unfold raw8102step3 raw8102step2; decide +kernel
      have hl : raw8102step3Labels = raw8102step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw8103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8103step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8103step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw8103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8103step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw8103step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8103 raw8103Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw8103 raw8103Labels = mixedMoment B raw8103step0 raw8103step0Labels := by
      have hz : ∀ j, raw8103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8103step0 = (fun i j => raw8103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8103step0 raw8103; decide +kernel
      have hl : raw8103step0Labels = raw8103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8103 raw8103Labels permutation346 hz
    mixedMoment B raw8103step0 raw8103step0Labels = mixedMoment B raw8103step1 raw8103step1Labels := by
      have hz : ∀ j, raw8103step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8103step1 = (fun i j => raw8103step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8103step1 raw8103step0; decide +kernel
      have hl : raw8103step1Labels = raw8103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8103step0 raw8103step0Labels permutation56 hz
    mixedMoment B raw8103step1 raw8103step1Labels = mixedMoment B raw8103step2 raw8103step2Labels := by
      have ha : raw8103step2 = (fun i j => raw8103step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8103step2 raw8103step1; decide +kernel
      have hl : raw8103step2Labels = raw8103step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8103step1 raw8103step1Labels permutation29 permutation3
    mixedMoment B raw8103step2 raw8103step2Labels = mixedMoment B raw8103step3 raw8103step3Labels := by
      have ha : raw8103step3 = -raw8103step2 := by apply Matrix.ext; change ∀ i j, raw8103step3 i j = -(raw8103step2 i j); unfold raw8103step3 raw8103step2; decide +kernel
      have hl : raw8103step3Labels = raw8103step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw8104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8104step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8104 raw8104Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw8104 raw8104Labels = mixedMoment B raw8104step0 raw8104step0Labels := by
      have hz : ∀ j, raw8104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8104step0 = (fun i j => raw8104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8104step0 raw8104; decide +kernel
      have hl : raw8104step0Labels = raw8104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8104 raw8104Labels permutation346 hz
    mixedMoment B raw8104step0 raw8104step0Labels = mixedMoment B raw8104step1 raw8104step1Labels := by
      have hz : ∀ j, raw8104step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8104step1 = (fun i j => raw8104step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8104step1 raw8104step0; decide +kernel
      have hl : raw8104step1Labels = raw8104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8104step0 raw8104step0Labels permutation56 hz
    mixedMoment B raw8104step1 raw8104step1Labels = mixedMoment B raw8104step2 raw8104step2Labels := by
      have ha : raw8104step2 = (fun i j => raw8104step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8104step2 raw8104step1; decide +kernel
      have hl : raw8104step2Labels = raw8104step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8104step1 raw8104step1Labels permutation23 permutation6
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw8105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8105 raw8105Labels = mixedMoment B node1229 node1229Labels := by
  calc
    mixedMoment B raw8105 raw8105Labels = mixedMoment B raw8105step0 raw8105step0Labels := by
      have hz : ∀ j, raw8105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8105step0 = (fun i j => raw8105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8105step0 raw8105; decide +kernel
      have hl : raw8105step0Labels = raw8105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8105 raw8105Labels permutation346 hz
    mixedMoment B raw8105step0 raw8105step0Labels = mixedMoment B raw8105step1 raw8105step1Labels := by
      have ha : raw8105step1 = (fun i j => raw8105step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8105step1 raw8105step0; decide +kernel
      have hl : raw8105step1Labels = raw8105step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8105step0 raw8105step0Labels permutation40 permutation3
    _ = mixedMoment B node1229 node1229Labels := by rfl

def raw8106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8106step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8106 raw8106Labels = mixedMoment B node2921 node2921Labels := by
  calc
    mixedMoment B raw8106 raw8106Labels = mixedMoment B raw8106step0 raw8106step0Labels := by
      have ha : raw8106step0 = (fun i j => raw8106 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8106step0 raw8106; decide +kernel
      have hl : raw8106step0Labels = raw8106Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8106 raw8106Labels permutation184 permutation3
    _ = mixedMoment B node2921 node2921Labels := by rfl

def raw8107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8107 raw8107Labels = mixedMoment B node2875 node2875Labels := by
  calc
    mixedMoment B raw8107 raw8107Labels = mixedMoment B raw8107step0 raw8107step0Labels := by
      have hz : ∀ j, raw8107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8107step0 = (fun i j => raw8107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8107step0 raw8107; decide +kernel
      have hl : raw8107step0Labels = raw8107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8107 raw8107Labels permutation346 hz
    mixedMoment B raw8107step0 raw8107step0Labels = mixedMoment B raw8107step1 raw8107step1Labels := by
      have ha : raw8107step1 = (fun i j => raw8107step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8107step1 raw8107step0; decide +kernel
      have hl : raw8107step1Labels = raw8107step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8107step0 raw8107step0Labels permutation40 permutation3
    _ = mixedMoment B node2875 node2875Labels := by rfl

def raw8108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8108step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8108 raw8108Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw8108 raw8108Labels = mixedMoment B raw8108step0 raw8108step0Labels := by
      have hz : ∀ j, raw8108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8108step0 = (fun i j => raw8108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8108step0 raw8108; decide +kernel
      have hl : raw8108step0Labels = raw8108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8108 raw8108Labels permutation346 hz
    mixedMoment B raw8108step0 raw8108step0Labels = mixedMoment B raw8108step1 raw8108step1Labels := by
      have ha : raw8108step1 = (fun i j => raw8108step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8108step1 raw8108step0; decide +kernel
      have hl : raw8108step1Labels = raw8108step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8108step0 raw8108step0Labels permutation46 permutation3
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw8109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8109 raw8109Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw8109 raw8109Labels = mixedMoment B raw8109step0 raw8109step0Labels := by
      have hz : ∀ j, raw8109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8109step0 = (fun i j => raw8109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8109step0 raw8109; decide +kernel
      have hl : raw8109step0Labels = raw8109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8109 raw8109Labels permutation346 hz
    mixedMoment B raw8109step0 raw8109step0Labels = mixedMoment B raw8109step1 raw8109step1Labels := by
      have ha : raw8109step1 = (fun i j => raw8109step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8109step1 raw8109step0; decide +kernel
      have hl : raw8109step1Labels = raw8109step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8109step0 raw8109step0Labels permutation40 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw8110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8110 raw8110Labels = mixedMoment B node1229 node1229Labels := by
  calc
    mixedMoment B raw8110 raw8110Labels = mixedMoment B raw8110step0 raw8110step0Labels := by
      have hz : ∀ j, raw8110 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8110step0 = (fun i j => raw8110 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8110step0 raw8110; decide +kernel
      have hl : raw8110step0Labels = raw8110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8110 raw8110Labels permutation265 hz
    mixedMoment B raw8110step0 raw8110step0Labels = mixedMoment B raw8110step1 raw8110step1Labels := by
      have ha : raw8110step1 = (fun i j => raw8110step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8110step1 raw8110step0; decide +kernel
      have hl : raw8110step1Labels = raw8110step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8110step0 raw8110step0Labels permutation40 permutation3
    _ = mixedMoment B node1229 node1229Labels := by rfl

def raw8111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8111 raw8111Labels = mixedMoment B node2921 node2921Labels := by
  calc
    mixedMoment B raw8111 raw8111Labels = mixedMoment B raw8111step0 raw8111step0Labels := by
      have ha : raw8111step0 = (fun i j => raw8111 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8111step0 raw8111; decide +kernel
      have hl : raw8111step0Labels = raw8111Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8111 raw8111Labels permutation160 permutation3
    _ = mixedMoment B node2921 node2921Labels := by rfl

def raw8112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8112 raw8112Labels = mixedMoment B node2875 node2875Labels := by
  calc
    mixedMoment B raw8112 raw8112Labels = mixedMoment B raw8112step0 raw8112step0Labels := by
      have hz : ∀ j, raw8112 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8112step0 = (fun i j => raw8112 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8112step0 raw8112; decide +kernel
      have hl : raw8112step0Labels = raw8112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8112 raw8112Labels permutation265 hz
    mixedMoment B raw8112step0 raw8112step0Labels = mixedMoment B raw8112step1 raw8112step1Labels := by
      have ha : raw8112step1 = (fun i j => raw8112step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8112step1 raw8112step0; decide +kernel
      have hl : raw8112step1Labels = raw8112step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8112step0 raw8112step0Labels permutation40 permutation3
    _ = mixedMoment B node2875 node2875Labels := by rfl

def raw8113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8113step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw8113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8113 raw8113Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw8113 raw8113Labels = mixedMoment B raw8113step0 raw8113step0Labels := by
      have hz : ∀ j, raw8113 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8113step0 = (fun i j => raw8113 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8113step0 raw8113; decide +kernel
      have hl : raw8113step0Labels = raw8113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8113 raw8113Labels permutation265 hz
    mixedMoment B raw8113step0 raw8113step0Labels = mixedMoment B raw8113step1 raw8113step1Labels := by
      have ha : raw8113step1 = (fun i j => raw8113step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8113step1 raw8113step0; decide +kernel
      have hl : raw8113step1Labels = raw8113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8113step0 raw8113step0Labels permutation46 permutation3
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw8114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8114 raw8114Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw8114 raw8114Labels = mixedMoment B raw8114step0 raw8114step0Labels := by
      have hz : ∀ j, raw8114 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8114step0 = (fun i j => raw8114 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8114step0 raw8114; decide +kernel
      have hl : raw8114step0Labels = raw8114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8114 raw8114Labels permutation265 hz
    mixedMoment B raw8114step0 raw8114step0Labels = mixedMoment B raw8114step1 raw8114step1Labels := by
      have ha : raw8114step1 = (fun i j => raw8114step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8114step1 raw8114step0; decide +kernel
      have hl : raw8114step1Labels = raw8114step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8114step0 raw8114step0Labels permutation40 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw8115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8115step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8115step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8115 raw8115Labels = mixedMoment B node1292 node1292Labels := by
  calc
    mixedMoment B raw8115 raw8115Labels = mixedMoment B raw8115step0 raw8115step0Labels := by
      have hz : ∀ j, raw8115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8115step0 = (fun i j => raw8115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8115step0 raw8115; decide +kernel
      have hl : raw8115step0Labels = raw8115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8115 raw8115Labels permutation346 hz
    mixedMoment B raw8115step0 raw8115step0Labels = mixedMoment B raw8115step1 raw8115step1Labels := by
      have hz : ∀ j, raw8115step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8115step1 = (fun i j => raw8115step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8115step1 raw8115step0; decide +kernel
      have hl : raw8115step1Labels = raw8115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8115step0 raw8115step0Labels permutation56 hz
    mixedMoment B raw8115step1 raw8115step1Labels = mixedMoment B raw8115step2 raw8115step2Labels := by
      have ha : raw8115step2 = (fun i j => raw8115step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8115step2 raw8115step1; decide +kernel
      have hl : raw8115step2Labels = raw8115step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8115step1 raw8115step1Labels permutation10 permutation3
    _ = mixedMoment B node1292 node1292Labels := by rfl

def raw8116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8116 raw8116Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw8116 raw8116Labels = mixedMoment B raw8116step0 raw8116step0Labels := by
      have hz : ∀ j, raw8116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8116step0 = (fun i j => raw8116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8116step0 raw8116; decide +kernel
      have hl : raw8116step0Labels = raw8116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8116 raw8116Labels permutation346 hz
    mixedMoment B raw8116step0 raw8116step0Labels = mixedMoment B raw8116step1 raw8116step1Labels := by
      have ha : raw8116step1 = (fun i j => raw8116step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8116step1 raw8116step0; decide +kernel
      have hl : raw8116step1Labels = raw8116step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8116step0 raw8116step0Labels permutation34 permutation3
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw8117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw8117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8117 raw8117Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw8117 raw8117Labels = mixedMoment B raw8117step0 raw8117step0Labels := by
      have hz : ∀ j, raw8117 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8117step0 = (fun i j => raw8117 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8117step0 raw8117; decide +kernel
      have hl : raw8117step0Labels = raw8117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8117 raw8117Labels permutation265 hz
    mixedMoment B raw8117step0 raw8117step0Labels = mixedMoment B raw8117step1 raw8117step1Labels := by
      have ha : raw8117step1 = (fun i j => raw8117step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8117step1 raw8117step0; decide +kernel
      have hl : raw8117step1Labels = raw8117step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8117step0 raw8117step0Labels permutation34 permutation3
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw8118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8118step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8118step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8118step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw8118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8118 raw8118Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw8118 raw8118Labels = mixedMoment B raw8118step0 raw8118step0Labels := by
      have hz : ∀ j, raw8118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8118step0 = (fun i j => raw8118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8118step0 raw8118; decide +kernel
      have hl : raw8118step0Labels = raw8118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8118 raw8118Labels permutation346 hz
    mixedMoment B raw8118step0 raw8118step0Labels = mixedMoment B raw8118step1 raw8118step1Labels := by
      have hz : ∀ j, raw8118step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8118step1 = (fun i j => raw8118step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8118step1 raw8118step0; decide +kernel
      have hl : raw8118step1Labels = raw8118step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8118step0 raw8118step0Labels permutation56 hz
    mixedMoment B raw8118step1 raw8118step1Labels = mixedMoment B raw8118step2 raw8118step2Labels := by
      have ha : raw8118step2 = (fun i j => raw8118step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8118step2 raw8118step1; decide +kernel
      have hl : raw8118step2Labels = raw8118step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8118step1 raw8118step1Labels permutation10 permutation3
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw8119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8119step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8119 raw8119Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw8119 raw8119Labels = mixedMoment B raw8119step0 raw8119step0Labels := by
      have hz : ∀ j, raw8119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8119step0 = (fun i j => raw8119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8119step0 raw8119; decide +kernel
      have hl : raw8119step0Labels = raw8119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8119 raw8119Labels permutation346 hz
    mixedMoment B raw8119step0 raw8119step0Labels = mixedMoment B raw8119step1 raw8119step1Labels := by
      have hz : ∀ j, raw8119step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8119step1 = (fun i j => raw8119step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8119step1 raw8119step0; decide +kernel
      have hl : raw8119step1Labels = raw8119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8119step0 raw8119step0Labels permutation56 hz
    mixedMoment B raw8119step1 raw8119step1Labels = mixedMoment B raw8119step2 raw8119step2Labels := by
      have ha : raw8119step2 = (fun i j => raw8119step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8119step2 raw8119step1; decide +kernel
      have hl : raw8119step2Labels = raw8119step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8119step1 raw8119step1Labels permutation10 permutation3
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw8120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8120step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw8120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8120 raw8120Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw8120 raw8120Labels = mixedMoment B raw8120step0 raw8120step0Labels := by
      have hz : ∀ j, raw8120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8120step0 = (fun i j => raw8120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8120step0 raw8120; decide +kernel
      have hl : raw8120step0Labels = raw8120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8120 raw8120Labels permutation346 hz
    mixedMoment B raw8120step0 raw8120step0Labels = mixedMoment B raw8120step1 raw8120step1Labels := by
      have hz : ∀ j, raw8120step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8120step1 = (fun i j => raw8120step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8120step1 raw8120step0; decide +kernel
      have hl : raw8120step1Labels = raw8120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8120step0 raw8120step0Labels permutation56 hz
    mixedMoment B raw8120step1 raw8120step1Labels = mixedMoment B raw8120step2 raw8120step2Labels := by
      have ha : raw8120step2 = (fun i j => raw8120step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8120step2 raw8120step1; decide +kernel
      have hl : raw8120step2Labels = raw8120step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8120step1 raw8120step1Labels permutation8 permutation3
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw8121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw8121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8121 raw8121Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw8121 raw8121Labels = mixedMoment B raw8121step0 raw8121step0Labels := by
      have hz : ∀ j, raw8121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8121step0 = (fun i j => raw8121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8121step0 raw8121; decide +kernel
      have hl : raw8121step0Labels = raw8121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8121 raw8121Labels permutation346 hz
    mixedMoment B raw8121step0 raw8121step0Labels = mixedMoment B raw8121step1 raw8121step1Labels := by
      have ha : raw8121step1 = (fun i j => raw8121step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8121step1 raw8121step0; decide +kernel
      have hl : raw8121step1Labels = raw8121step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8121step0 raw8121step0Labels permutation32 permutation3
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw8122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw8122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8122 raw8122Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw8122 raw8122Labels = mixedMoment B raw8122step0 raw8122step0Labels := by
      have hz : ∀ j, raw8122 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8122step0 = (fun i j => raw8122 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8122step0 raw8122; decide +kernel
      have hl : raw8122step0Labels = raw8122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8122 raw8122Labels permutation265 hz
    mixedMoment B raw8122step0 raw8122step0Labels = mixedMoment B raw8122step1 raw8122step1Labels := by
      have ha : raw8122step1 = (fun i j => raw8122step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8122step1 raw8122step0; decide +kernel
      have hl : raw8122step1Labels = raw8122step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8122step0 raw8122step0Labels permutation32 permutation3
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw8123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8123step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -2, 0], ![2, 1, -3]]
def raw8123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8123 raw8123Labels = mixedMoment B node2888 node2888Labels := by
  calc
    mixedMoment B raw8123 raw8123Labels = mixedMoment B raw8123step0 raw8123step0Labels := by
      have hz : ∀ j, raw8123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8123step0 = (fun i j => raw8123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8123step0 raw8123; decide +kernel
      have hl : raw8123step0Labels = raw8123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8123 raw8123Labels permutation346 hz
    mixedMoment B raw8123step0 raw8123step0Labels = mixedMoment B raw8123step1 raw8123step1Labels := by
      have hz : ∀ j, raw8123step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8123step1 = (fun i j => raw8123step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8123step1 raw8123step0; decide +kernel
      have hl : raw8123step1Labels = raw8123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8123step0 raw8123step0Labels permutation56 hz
    mixedMoment B raw8123step1 raw8123step1Labels = mixedMoment B raw8123step2 raw8123step2Labels := by
      have ha : raw8123step2 = (fun i j => raw8123step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8123step2 raw8123step1; decide +kernel
      have hl : raw8123step2Labels = raw8123step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8123step1 raw8123step1Labels permutation8 permutation3
    _ = mixedMoment B node2888 node2888Labels := by rfl

def raw8124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8124step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8124step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw8124step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8124 raw8124Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw8124 raw8124Labels = mixedMoment B raw8124step0 raw8124step0Labels := by
      have hz : ∀ j, raw8124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8124step0 = (fun i j => raw8124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8124step0 raw8124; decide +kernel
      have hl : raw8124step0Labels = raw8124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8124 raw8124Labels permutation346 hz
    mixedMoment B raw8124step0 raw8124step0Labels = mixedMoment B raw8124step1 raw8124step1Labels := by
      have hz : ∀ j, raw8124step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8124step1 = (fun i j => raw8124step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8124step1 raw8124step0; decide +kernel
      have hl : raw8124step1Labels = raw8124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8124step0 raw8124step0Labels permutation56 hz
    mixedMoment B raw8124step1 raw8124step1Labels = mixedMoment B raw8124step2 raw8124step2Labels := by
      have ha : raw8124step2 = (fun i j => raw8124step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8124step2 raw8124step1; decide +kernel
      have hl : raw8124step2Labels = raw8124step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8124step1 raw8124step1Labels permutation9 permutation3
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw8125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8125step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8125step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw8125step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8125 raw8125Labels = mixedMoment B node1231 node1231Labels := by
  calc
    mixedMoment B raw8125 raw8125Labels = mixedMoment B raw8125step0 raw8125step0Labels := by
      have hz : ∀ j, raw8125 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8125step0 = (fun i j => raw8125 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8125step0 raw8125; decide +kernel
      have hl : raw8125step0Labels = raw8125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8125 raw8125Labels permutation346 hz
    mixedMoment B raw8125step0 raw8125step0Labels = mixedMoment B raw8125step1 raw8125step1Labels := by
      have hz : ∀ j, raw8125step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8125step1 = (fun i j => raw8125step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8125step1 raw8125step0; decide +kernel
      have hl : raw8125step1Labels = raw8125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8125step0 raw8125step0Labels permutation56 hz
    mixedMoment B raw8125step1 raw8125step1Labels = mixedMoment B raw8125step2 raw8125step2Labels := by
      have ha : raw8125step2 = (fun i j => raw8125step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8125step2 raw8125step1; decide +kernel
      have hl : raw8125step2Labels = raw8125step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8125step1 raw8125step1Labels permutation8 permutation3
    _ = mixedMoment B node1231 node1231Labels := by rfl

def raw8126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8126step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw8126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8126 raw8126Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw8126 raw8126Labels = mixedMoment B raw8126step0 raw8126step0Labels := by
      have hz : ∀ j, raw8126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8126step0 = (fun i j => raw8126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8126step0 raw8126; decide +kernel
      have hl : raw8126step0Labels = raw8126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8126 raw8126Labels permutation346 hz
    mixedMoment B raw8126step0 raw8126step0Labels = mixedMoment B raw8126step1 raw8126step1Labels := by
      have ha : raw8126step1 = (fun i j => raw8126step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8126step1 raw8126step0; decide +kernel
      have hl : raw8126step1Labels = raw8126step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8126step0 raw8126step0Labels permutation151 permutation3
    mixedMoment B raw8126step1 raw8126step1Labels = mixedMoment B raw8126step2 raw8126step2Labels := by
      have ha : raw8126step2 = -raw8126step1 := by apply Matrix.ext; change ∀ i j, raw8126step2 i j = -(raw8126step1 i j); unfold raw8126step2 raw8126step1; decide +kernel
      have hl : raw8126step2Labels = raw8126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1639 node1639Labels := by rfl

def raw8127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw8127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw8127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8127 raw8127Labels = mixedMoment B node1639 node1639Labels := by
  calc
    mixedMoment B raw8127 raw8127Labels = mixedMoment B raw8127step0 raw8127step0Labels := by
      have hz : ∀ j, raw8127 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8127step0 = (fun i j => raw8127 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8127step0 raw8127; decide +kernel
      have hl : raw8127step0Labels = raw8127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8127 raw8127Labels permutation265 hz
    mixedMoment B raw8127step0 raw8127step0Labels = mixedMoment B raw8127step1 raw8127step1Labels := by
      have ha : raw8127step1 = (fun i j => raw8127step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8127step1 raw8127step0; decide +kernel
      have hl : raw8127step1Labels = raw8127step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8127step0 raw8127step0Labels permutation151 permutation3
    mixedMoment B raw8127step1 raw8127step1Labels = mixedMoment B raw8127step2 raw8127step2Labels := by
      have ha : raw8127step2 = -raw8127step1 := by apply Matrix.ext; change ∀ i j, raw8127step2 i j = -(raw8127step1 i j); unfold raw8127step2 raw8127step1; decide +kernel
      have hl : raw8127step2Labels = raw8127step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1639 node1639Labels := by rfl

def raw8128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8128step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8128step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw8128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 1, -2], ![3, -2, -1]]
def raw8128step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8128 raw8128Labels = mixedMoment B node1651 node1651Labels := by
  calc
    mixedMoment B raw8128 raw8128Labels = mixedMoment B raw8128step0 raw8128step0Labels := by
      have hz : ∀ j, raw8128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8128step0 = (fun i j => raw8128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8128step0 raw8128; decide +kernel
      have hl : raw8128step0Labels = raw8128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8128 raw8128Labels permutation346 hz
    mixedMoment B raw8128step0 raw8128step0Labels = mixedMoment B raw8128step1 raw8128step1Labels := by
      have hz : ∀ j, raw8128step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8128step1 = (fun i j => raw8128step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8128step1 raw8128step0; decide +kernel
      have hl : raw8128step1Labels = raw8128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8128step0 raw8128step0Labels permutation56 hz
    mixedMoment B raw8128step1 raw8128step1Labels = mixedMoment B raw8128step2 raw8128step2Labels := by
      have ha : raw8128step2 = (fun i j => raw8128step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8128step2 raw8128step1; decide +kernel
      have hl : raw8128step2Labels = raw8128step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8128step1 raw8128step1Labels permutation31 permutation3
    mixedMoment B raw8128step2 raw8128step2Labels = mixedMoment B raw8128step3 raw8128step3Labels := by
      have ha : raw8128step3 = -raw8128step2 := by apply Matrix.ext; change ∀ i j, raw8128step3 i j = -(raw8128step2 i j); unfold raw8128step3 raw8128step2; decide +kernel
      have hl : raw8128step3Labels = raw8128step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1651 node1651Labels := by rfl

def raw8129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8129step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8129step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw8129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw8129step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw8129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8129 raw8129Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw8129 raw8129Labels = mixedMoment B raw8129step0 raw8129step0Labels := by
      have hz : ∀ j, raw8129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8129step0 = (fun i j => raw8129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8129step0 raw8129; decide +kernel
      have hl : raw8129step0Labels = raw8129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8129 raw8129Labels permutation346 hz
    mixedMoment B raw8129step0 raw8129step0Labels = mixedMoment B raw8129step1 raw8129step1Labels := by
      have hz : ∀ j, raw8129step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8129step1 = (fun i j => raw8129step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8129step1 raw8129step0; decide +kernel
      have hl : raw8129step1Labels = raw8129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8129step0 raw8129step0Labels permutation56 hz
    mixedMoment B raw8129step1 raw8129step1Labels = mixedMoment B raw8129step2 raw8129step2Labels := by
      have ha : raw8129step2 = (fun i j => raw8129step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8129step2 raw8129step1; decide +kernel
      have hl : raw8129step2Labels = raw8129step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8129step1 raw8129step1Labels permutation29 permutation3
    mixedMoment B raw8129step2 raw8129step2Labels = mixedMoment B raw8129step3 raw8129step3Labels := by
      have ha : raw8129step3 = -raw8129step2 := by apply Matrix.ext; change ∀ i j, raw8129step3 i j = -(raw8129step2 i j); unfold raw8129step3 raw8129step2; decide +kernel
      have hl : raw8129step3Labels = raw8129step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw8130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8130step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8130 raw8130Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw8130 raw8130Labels = mixedMoment B raw8130step0 raw8130step0Labels := by
      have hz : ∀ j, raw8130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8130step0 = (fun i j => raw8130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8130step0 raw8130; decide +kernel
      have hl : raw8130step0Labels = raw8130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8130 raw8130Labels permutation346 hz
    mixedMoment B raw8130step0 raw8130step0Labels = mixedMoment B raw8130step1 raw8130step1Labels := by
      have ha : raw8130step1 = (fun i j => raw8130step0 (permutation133 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8130step1 raw8130step0; decide +kernel
      have hl : raw8130step1Labels = raw8130step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8130step0 raw8130step0Labels permutation133 permutation5
    mixedMoment B raw8130step1 raw8130step1Labels = mixedMoment B raw8130step2 raw8130step2Labels := by
      have ha : raw8130step2 = raw8130step1 := by apply Matrix.ext; unfold raw8130step2 raw8130step1; decide +kernel
      have hl : raw8130step1Labels = labelEmbedding1 ∘ raw8130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8130step1 raw8130step1Labels raw8130step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw8131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8131step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw8131step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8131 raw8131Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw8131 raw8131Labels = mixedMoment B raw8131step0 raw8131step0Labels := by
      have hz : ∀ j, raw8131 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8131step0 = (fun i j => raw8131 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8131step0 raw8131; decide +kernel
      have hl : raw8131step0Labels = raw8131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8131 raw8131Labels permutation265 hz
    mixedMoment B raw8131step0 raw8131step0Labels = mixedMoment B raw8131step1 raw8131step1Labels := by
      have ha : raw8131step1 = (fun i j => raw8131step0 (permutation133 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8131step1 raw8131step0; decide +kernel
      have hl : raw8131step1Labels = raw8131step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8131step0 raw8131step0Labels permutation133 permutation5
    mixedMoment B raw8131step1 raw8131step1Labels = mixedMoment B raw8131step2 raw8131step2Labels := by
      have ha : raw8131step2 = raw8131step1 := by apply Matrix.ext; unfold raw8131step2 raw8131step1; decide +kernel
      have hl : raw8131step1Labels = labelEmbedding1 ∘ raw8131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8131step1 raw8131step1Labels raw8131step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw8132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8132step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8132step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8132step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw8132step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8132 raw8132Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw8132 raw8132Labels = mixedMoment B raw8132step0 raw8132step0Labels := by
      have hz : ∀ j, raw8132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8132step0 = (fun i j => raw8132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8132step0 raw8132; decide +kernel
      have hl : raw8132step0Labels = raw8132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8132 raw8132Labels permutation346 hz
    mixedMoment B raw8132step0 raw8132step0Labels = mixedMoment B raw8132step1 raw8132step1Labels := by
      have hz : ∀ j, raw8132step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8132step1 = (fun i j => raw8132step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8132step1 raw8132step0; decide +kernel
      have hl : raw8132step1Labels = raw8132step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8132step0 raw8132step0Labels permutation56 hz
    mixedMoment B raw8132step1 raw8132step1Labels = mixedMoment B raw8132step2 raw8132step2Labels := by
      have ha : raw8132step2 = (fun i j => raw8132step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8132step2 raw8132step1; decide +kernel
      have hl : raw8132step2Labels = raw8132step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8132step1 raw8132step1Labels permutation27 permutation5
    mixedMoment B raw8132step2 raw8132step2Labels = mixedMoment B raw8132step3 raw8132step3Labels := by
      have ha : raw8132step3 = raw8132step2 := by apply Matrix.ext; unfold raw8132step3 raw8132step2; decide +kernel
      have hl : raw8132step2Labels = labelEmbedding1 ∘ raw8132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8132step2 raw8132step2Labels raw8132step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw8133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8133step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8133step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8133step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw8133step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8133 raw8133Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw8133 raw8133Labels = mixedMoment B raw8133step0 raw8133step0Labels := by
      have hz : ∀ j, raw8133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8133step0 = (fun i j => raw8133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8133step0 raw8133; decide +kernel
      have hl : raw8133step0Labels = raw8133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8133 raw8133Labels permutation346 hz
    mixedMoment B raw8133step0 raw8133step0Labels = mixedMoment B raw8133step1 raw8133step1Labels := by
      have hz : ∀ j, raw8133step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8133step1 = (fun i j => raw8133step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8133step1 raw8133step0; decide +kernel
      have hl : raw8133step1Labels = raw8133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8133step0 raw8133step0Labels permutation56 hz
    mixedMoment B raw8133step1 raw8133step1Labels = mixedMoment B raw8133step2 raw8133step2Labels := by
      have ha : raw8133step2 = (fun i j => raw8133step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8133step2 raw8133step1; decide +kernel
      have hl : raw8133step2Labels = raw8133step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8133step1 raw8133step1Labels permutation26 permutation5
    mixedMoment B raw8133step2 raw8133step2Labels = mixedMoment B raw8133step3 raw8133step3Labels := by
      have ha : raw8133step3 = raw8133step2 := by apply Matrix.ext; unfold raw8133step3 raw8133step2; decide +kernel
      have hl : raw8133step2Labels = labelEmbedding1 ∘ raw8133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8133step2 raw8133step2Labels raw8133step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw8134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8134step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8134step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8134step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8134step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8134step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8134step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8134step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8134 raw8134Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw8134 raw8134Labels = mixedMoment B raw8134step0 raw8134step0Labels := by
      have hz : ∀ j, raw8134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8134step0 = (fun i j => raw8134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8134step0 raw8134; decide +kernel
      have hl : raw8134step0Labels = raw8134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8134 raw8134Labels permutation346 hz
    mixedMoment B raw8134step0 raw8134step0Labels = mixedMoment B raw8134step1 raw8134step1Labels := by
      have hz : ∀ j, raw8134step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8134step1 = (fun i j => raw8134step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8134step1 raw8134step0; decide +kernel
      have hl : raw8134step1Labels = raw8134step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8134step0 raw8134step0Labels permutation56 hz
    mixedMoment B raw8134step1 raw8134step1Labels = mixedMoment B raw8134step2 raw8134step2Labels := by
      have ha : raw8134step2 = (fun i j => raw8134step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8134step2 raw8134step1; decide +kernel
      have hl : raw8134step2Labels = raw8134step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8134step1 raw8134step1Labels permutation12 permutation7
    mixedMoment B raw8134step2 raw8134step2Labels = mixedMoment B raw8134step3 raw8134step3Labels := by
      have ha : raw8134step3 = -raw8134step2 := by apply Matrix.ext; change ∀ i j, raw8134step3 i j = -(raw8134step2 i j); unfold raw8134step3 raw8134step2; decide +kernel
      have hl : raw8134step3Labels = raw8134step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8134step3 raw8134step3Labels = mixedMoment B raw8134step4 raw8134step4Labels := by
      have ha : raw8134step4 = raw8134step3 := by apply Matrix.ext; unfold raw8134step4 raw8134step3; decide +kernel
      have hl : raw8134step3Labels = labelEmbedding1 ∘ raw8134step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8134step3 raw8134step3Labels raw8134step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw8135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8135step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8135step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8135 raw8135Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw8135 raw8135Labels = mixedMoment B raw8135step0 raw8135step0Labels := by
      have hz : ∀ j, raw8135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8135step0 = (fun i j => raw8135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8135step0 raw8135; decide +kernel
      have hl : raw8135step0Labels = raw8135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8135 raw8135Labels permutation346 hz
    mixedMoment B raw8135step0 raw8135step0Labels = mixedMoment B raw8135step1 raw8135step1Labels := by
      have ha : raw8135step1 = (fun i j => raw8135step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8135step1 raw8135step0; decide +kernel
      have hl : raw8135step1Labels = raw8135step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8135step0 raw8135step0Labels permutation139 permutation5
    mixedMoment B raw8135step1 raw8135step1Labels = mixedMoment B raw8135step2 raw8135step2Labels := by
      have ha : raw8135step2 = raw8135step1 := by apply Matrix.ext; unfold raw8135step2 raw8135step1; decide +kernel
      have hl : raw8135step1Labels = labelEmbedding1 ∘ raw8135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8135step1 raw8135step1Labels raw8135step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2502 node2502Labels := by rfl

def raw8136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8136step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8136 raw8136Labels = mixedMoment B node2500 node2500Labels := by
  calc
    mixedMoment B raw8136 raw8136Labels = mixedMoment B raw8136step0 raw8136step0Labels := by
      have ha : raw8136step0 = (fun i j => raw8136 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8136step0 raw8136; decide +kernel
      have hl : raw8136step0Labels = raw8136Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8136 raw8136Labels permutation622 permutation5
    mixedMoment B raw8136step0 raw8136step0Labels = mixedMoment B raw8136step1 raw8136step1Labels := by
      have ha : raw8136step1 = raw8136step0 := by apply Matrix.ext; unfold raw8136step1 raw8136step0; decide +kernel
      have hl : raw8136step0Labels = labelEmbedding1 ∘ raw8136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8136step0 raw8136step0Labels raw8136step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2500 node2500Labels := by rfl

def raw8137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8137step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8137step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8137step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8137 raw8137Labels = mixedMoment B node2506 node2506Labels := by
  calc
    mixedMoment B raw8137 raw8137Labels = mixedMoment B raw8137step0 raw8137step0Labels := by
      have hz : ∀ j, raw8137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8137step0 = (fun i j => raw8137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8137step0 raw8137; decide +kernel
      have hl : raw8137step0Labels = raw8137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8137 raw8137Labels permutation346 hz
    mixedMoment B raw8137step0 raw8137step0Labels = mixedMoment B raw8137step1 raw8137step1Labels := by
      have ha : raw8137step1 = (fun i j => raw8137step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8137step1 raw8137step0; decide +kernel
      have hl : raw8137step1Labels = raw8137step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8137step0 raw8137step0Labels permutation138 permutation5
    mixedMoment B raw8137step1 raw8137step1Labels = mixedMoment B raw8137step2 raw8137step2Labels := by
      have ha : raw8137step2 = raw8137step1 := by apply Matrix.ext; unfold raw8137step2 raw8137step1; decide +kernel
      have hl : raw8137step1Labels = labelEmbedding1 ∘ raw8137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8137step1 raw8137step1Labels raw8137step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2506 node2506Labels := by rfl

def raw8138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8138step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8138step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8138step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8138 raw8138Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw8138 raw8138Labels = mixedMoment B raw8138step0 raw8138step0Labels := by
      have hz : ∀ j, raw8138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8138step0 = (fun i j => raw8138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8138step0 raw8138; decide +kernel
      have hl : raw8138step0Labels = raw8138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8138 raw8138Labels permutation346 hz
    mixedMoment B raw8138step0 raw8138step0Labels = mixedMoment B raw8138step1 raw8138step1Labels := by
      have ha : raw8138step1 = (fun i j => raw8138step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8138step1 raw8138step0; decide +kernel
      have hl : raw8138step1Labels = raw8138step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8138step0 raw8138step0Labels permutation136 permutation5
    mixedMoment B raw8138step1 raw8138step1Labels = mixedMoment B raw8138step2 raw8138step2Labels := by
      have ha : raw8138step2 = raw8138step1 := by apply Matrix.ext; unfold raw8138step2 raw8138step1; decide +kernel
      have hl : raw8138step1Labels = labelEmbedding1 ∘ raw8138step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8138step1 raw8138step1Labels raw8138step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw8139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8139step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8139step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8139step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8139step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8139 raw8139Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw8139 raw8139Labels = mixedMoment B raw8139step0 raw8139step0Labels := by
      have hz : ∀ j, raw8139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8139step0 = (fun i j => raw8139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8139step0 raw8139; decide +kernel
      have hl : raw8139step0Labels = raw8139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8139 raw8139Labels permutation346 hz
    mixedMoment B raw8139step0 raw8139step0Labels = mixedMoment B raw8139step1 raw8139step1Labels := by
      have ha : raw8139step1 = (fun i j => raw8139step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8139step1 raw8139step0; decide +kernel
      have hl : raw8139step1Labels = raw8139step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8139step0 raw8139step0Labels permutation50 permutation7
    mixedMoment B raw8139step1 raw8139step1Labels = mixedMoment B raw8139step2 raw8139step2Labels := by
      have ha : raw8139step2 = -raw8139step1 := by apply Matrix.ext; change ∀ i j, raw8139step2 i j = -(raw8139step1 i j); unfold raw8139step2 raw8139step1; decide +kernel
      have hl : raw8139step2Labels = raw8139step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8139step2 raw8139step2Labels = mixedMoment B raw8139step3 raw8139step3Labels := by
      have ha : raw8139step3 = raw8139step2 := by apply Matrix.ext; unfold raw8139step3 raw8139step2; decide +kernel
      have hl : raw8139step2Labels = labelEmbedding1 ∘ raw8139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8139step2 raw8139step2Labels raw8139step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw8140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8140step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8140step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8140step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8140 raw8140Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw8140 raw8140Labels = mixedMoment B raw8140step0 raw8140step0Labels := by
      have hz : ∀ j, raw8140 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8140step0 = (fun i j => raw8140 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8140step0 raw8140; decide +kernel
      have hl : raw8140step0Labels = raw8140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8140 raw8140Labels permutation265 hz
    mixedMoment B raw8140step0 raw8140step0Labels = mixedMoment B raw8140step1 raw8140step1Labels := by
      have ha : raw8140step1 = (fun i j => raw8140step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8140step1 raw8140step0; decide +kernel
      have hl : raw8140step1Labels = raw8140step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8140step0 raw8140step0Labels permutation139 permutation5
    mixedMoment B raw8140step1 raw8140step1Labels = mixedMoment B raw8140step2 raw8140step2Labels := by
      have ha : raw8140step2 = raw8140step1 := by apply Matrix.ext; unfold raw8140step2 raw8140step1; decide +kernel
      have hl : raw8140step1Labels = labelEmbedding1 ∘ raw8140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8140step1 raw8140step1Labels raw8140step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2502 node2502Labels := by rfl

def raw8141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8141Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8141step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8141 raw8141Labels = mixedMoment B node2500 node2500Labels := by
  calc
    mixedMoment B raw8141 raw8141Labels = mixedMoment B raw8141step0 raw8141step0Labels := by
      have ha : raw8141step0 = (fun i j => raw8141 (permutation646 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8141step0 raw8141; decide +kernel
      have hl : raw8141step0Labels = raw8141Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8141 raw8141Labels permutation646 permutation5
    mixedMoment B raw8141step0 raw8141step0Labels = mixedMoment B raw8141step1 raw8141step1Labels := by
      have ha : raw8141step1 = raw8141step0 := by apply Matrix.ext; unfold raw8141step1 raw8141step0; decide +kernel
      have hl : raw8141step0Labels = labelEmbedding1 ∘ raw8141step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8141step0 raw8141step0Labels raw8141step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2500 node2500Labels := by rfl

def raw8142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8142step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8142step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8142step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8142 raw8142Labels = mixedMoment B node2506 node2506Labels := by
  calc
    mixedMoment B raw8142 raw8142Labels = mixedMoment B raw8142step0 raw8142step0Labels := by
      have hz : ∀ j, raw8142 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8142step0 = (fun i j => raw8142 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8142step0 raw8142; decide +kernel
      have hl : raw8142step0Labels = raw8142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8142 raw8142Labels permutation265 hz
    mixedMoment B raw8142step0 raw8142step0Labels = mixedMoment B raw8142step1 raw8142step1Labels := by
      have ha : raw8142step1 = (fun i j => raw8142step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8142step1 raw8142step0; decide +kernel
      have hl : raw8142step1Labels = raw8142step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8142step0 raw8142step0Labels permutation138 permutation5
    mixedMoment B raw8142step1 raw8142step1Labels = mixedMoment B raw8142step2 raw8142step2Labels := by
      have ha : raw8142step2 = raw8142step1 := by apply Matrix.ext; unfold raw8142step2 raw8142step1; decide +kernel
      have hl : raw8142step1Labels = labelEmbedding1 ∘ raw8142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8142step1 raw8142step1Labels raw8142step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2506 node2506Labels := by rfl

def raw8143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8143Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8143step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8143step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8143 raw8143Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw8143 raw8143Labels = mixedMoment B raw8143step0 raw8143step0Labels := by
      have hz : ∀ j, raw8143 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8143step0 = (fun i j => raw8143 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8143step0 raw8143; decide +kernel
      have hl : raw8143step0Labels = raw8143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8143 raw8143Labels permutation265 hz
    mixedMoment B raw8143step0 raw8143step0Labels = mixedMoment B raw8143step1 raw8143step1Labels := by
      have ha : raw8143step1 = (fun i j => raw8143step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8143step1 raw8143step0; decide +kernel
      have hl : raw8143step1Labels = raw8143step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8143step0 raw8143step0Labels permutation136 permutation5
    mixedMoment B raw8143step1 raw8143step1Labels = mixedMoment B raw8143step2 raw8143step2Labels := by
      have ha : raw8143step2 = raw8143step1 := by apply Matrix.ext; unfold raw8143step2 raw8143step1; decide +kernel
      have hl : raw8143step1Labels = labelEmbedding1 ∘ raw8143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8143step1 raw8143step1Labels raw8143step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw8144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8144Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8144step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw8144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8144step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8144step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw8144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8144 raw8144Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw8144 raw8144Labels = mixedMoment B raw8144step0 raw8144step0Labels := by
      have hz : ∀ j, raw8144 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8144step0 = (fun i j => raw8144 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8144step0 raw8144; decide +kernel
      have hl : raw8144step0Labels = raw8144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8144 raw8144Labels permutation265 hz
    mixedMoment B raw8144step0 raw8144step0Labels = mixedMoment B raw8144step1 raw8144step1Labels := by
      have ha : raw8144step1 = (fun i j => raw8144step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8144step1 raw8144step0; decide +kernel
      have hl : raw8144step1Labels = raw8144step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8144step0 raw8144step0Labels permutation50 permutation7
    mixedMoment B raw8144step1 raw8144step1Labels = mixedMoment B raw8144step2 raw8144step2Labels := by
      have ha : raw8144step2 = -raw8144step1 := by apply Matrix.ext; change ∀ i j, raw8144step2 i j = -(raw8144step1 i j); unfold raw8144step2 raw8144step1; decide +kernel
      have hl : raw8144step2Labels = raw8144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8144step2 raw8144step2Labels = mixedMoment B raw8144step3 raw8144step3Labels := by
      have ha : raw8144step3 = raw8144step2 := by apply Matrix.ext; unfold raw8144step3 raw8144step2; decide +kernel
      have hl : raw8144step2Labels = labelEmbedding1 ∘ raw8144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8144step2 raw8144step2Labels raw8144step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw8145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8145Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8145step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8145step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8145step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8145step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw8145step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8145 raw8145Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw8145 raw8145Labels = mixedMoment B raw8145step0 raw8145step0Labels := by
      have hz : ∀ j, raw8145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8145step0 = (fun i j => raw8145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8145step0 raw8145; decide +kernel
      have hl : raw8145step0Labels = raw8145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8145 raw8145Labels permutation346 hz
    mixedMoment B raw8145step0 raw8145step0Labels = mixedMoment B raw8145step1 raw8145step1Labels := by
      have hz : ∀ j, raw8145step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8145step1 = (fun i j => raw8145step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8145step1 raw8145step0; decide +kernel
      have hl : raw8145step1Labels = raw8145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8145step0 raw8145step0Labels permutation56 hz
    mixedMoment B raw8145step1 raw8145step1Labels = mixedMoment B raw8145step2 raw8145step2Labels := by
      have ha : raw8145step2 = (fun i j => raw8145step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8145step2 raw8145step1; decide +kernel
      have hl : raw8145step2Labels = raw8145step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8145step1 raw8145step1Labels permutation29 permutation5
    mixedMoment B raw8145step2 raw8145step2Labels = mixedMoment B raw8145step3 raw8145step3Labels := by
      have ha : raw8145step3 = raw8145step2 := by apply Matrix.ext; unfold raw8145step3 raw8145step2; decide +kernel
      have hl : raw8145step2Labels = labelEmbedding1 ∘ raw8145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8145step2 raw8145step2Labels raw8145step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw8146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8146step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8146step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8146step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8146 raw8146Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw8146 raw8146Labels = mixedMoment B raw8146step0 raw8146step0Labels := by
      have hz : ∀ j, raw8146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8146step0 = (fun i j => raw8146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8146step0 raw8146; decide +kernel
      have hl : raw8146step0Labels = raw8146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8146 raw8146Labels permutation346 hz
    mixedMoment B raw8146step0 raw8146step0Labels = mixedMoment B raw8146step1 raw8146step1Labels := by
      have ha : raw8146step1 = (fun i j => raw8146step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8146step1 raw8146step0; decide +kernel
      have hl : raw8146step1Labels = raw8146step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8146step0 raw8146step0Labels permutation145 permutation5
    mixedMoment B raw8146step1 raw8146step1Labels = mixedMoment B raw8146step2 raw8146step2Labels := by
      have ha : raw8146step2 = raw8146step1 := by apply Matrix.ext; unfold raw8146step2 raw8146step1; decide +kernel
      have hl : raw8146step1Labels = labelEmbedding1 ∘ raw8146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8146step1 raw8146step1Labels raw8146step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw8147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8147step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw8147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8147 raw8147Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw8147 raw8147Labels = mixedMoment B raw8147step0 raw8147step0Labels := by
      have hz : ∀ j, raw8147 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8147step0 = (fun i j => raw8147 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8147step0 raw8147; decide +kernel
      have hl : raw8147step0Labels = raw8147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8147 raw8147Labels permutation265 hz
    mixedMoment B raw8147step0 raw8147step0Labels = mixedMoment B raw8147step1 raw8147step1Labels := by
      have ha : raw8147step1 = (fun i j => raw8147step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8147step1 raw8147step0; decide +kernel
      have hl : raw8147step1Labels = raw8147step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8147step0 raw8147step0Labels permutation145 permutation5
    mixedMoment B raw8147step1 raw8147step1Labels = mixedMoment B raw8147step2 raw8147step2Labels := by
      have ha : raw8147step2 = raw8147step1 := by apply Matrix.ext; unfold raw8147step2 raw8147step1; decide +kernel
      have hl : raw8147step1Labels = labelEmbedding1 ∘ raw8147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8147step1 raw8147step1Labels raw8147step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw8148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8148Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8148step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8148step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8148step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8148step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw8148step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8148 raw8148Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw8148 raw8148Labels = mixedMoment B raw8148step0 raw8148step0Labels := by
      have hz : ∀ j, raw8148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8148step0 = (fun i j => raw8148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8148step0 raw8148; decide +kernel
      have hl : raw8148step0Labels = raw8148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8148 raw8148Labels permutation346 hz
    mixedMoment B raw8148step0 raw8148step0Labels = mixedMoment B raw8148step1 raw8148step1Labels := by
      have hz : ∀ j, raw8148step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8148step1 = (fun i j => raw8148step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8148step1 raw8148step0; decide +kernel
      have hl : raw8148step1Labels = raw8148step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8148step0 raw8148step0Labels permutation56 hz
    mixedMoment B raw8148step1 raw8148step1Labels = mixedMoment B raw8148step2 raw8148step2Labels := by
      have ha : raw8148step2 = (fun i j => raw8148step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8148step2 raw8148step1; decide +kernel
      have hl : raw8148step2Labels = raw8148step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8148step1 raw8148step1Labels permutation28 permutation5
    mixedMoment B raw8148step2 raw8148step2Labels = mixedMoment B raw8148step3 raw8148step3Labels := by
      have ha : raw8148step3 = raw8148step2 := by apply Matrix.ext; unfold raw8148step3 raw8148step2; decide +kernel
      have hl : raw8148step2Labels = labelEmbedding1 ∘ raw8148step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8148step2 raw8148step2Labels raw8148step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw8149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8149Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8149step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8149step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8149step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw8149step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8149step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8149step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8149step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw8149step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8149 raw8149Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw8149 raw8149Labels = mixedMoment B raw8149step0 raw8149step0Labels := by
      have hz : ∀ j, raw8149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8149step0 = (fun i j => raw8149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8149step0 raw8149; decide +kernel
      have hl : raw8149step0Labels = raw8149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8149 raw8149Labels permutation346 hz
    mixedMoment B raw8149step0 raw8149step0Labels = mixedMoment B raw8149step1 raw8149step1Labels := by
      have hz : ∀ j, raw8149step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8149step1 = (fun i j => raw8149step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8149step1 raw8149step0; decide +kernel
      have hl : raw8149step1Labels = raw8149step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8149step0 raw8149step0Labels permutation56 hz
    mixedMoment B raw8149step1 raw8149step1Labels = mixedMoment B raw8149step2 raw8149step2Labels := by
      have ha : raw8149step2 = (fun i j => raw8149step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8149step2 raw8149step1; decide +kernel
      have hl : raw8149step2Labels = raw8149step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8149step1 raw8149step1Labels permutation12 permutation7
    mixedMoment B raw8149step2 raw8149step2Labels = mixedMoment B raw8149step3 raw8149step3Labels := by
      have ha : raw8149step3 = -raw8149step2 := by apply Matrix.ext; change ∀ i j, raw8149step3 i j = -(raw8149step2 i j); unfold raw8149step3 raw8149step2; decide +kernel
      have hl : raw8149step3Labels = raw8149step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8149step3 raw8149step3Labels = mixedMoment B raw8149step4 raw8149step4Labels := by
      have ha : raw8149step4 = raw8149step3 := by apply Matrix.ext; unfold raw8149step4 raw8149step3; decide +kernel
      have hl : raw8149step3Labels = labelEmbedding1 ∘ raw8149step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8149step3 raw8149step3Labels raw8149step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw8150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8150Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8150step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8150step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8150step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw8150step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8150step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw8150step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8150 raw8150Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw8150 raw8150Labels = mixedMoment B raw8150step0 raw8150step0Labels := by
      have hz : ∀ j, raw8150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8150step0 = (fun i j => raw8150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8150step0 raw8150; decide +kernel
      have hl : raw8150step0Labels = raw8150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8150 raw8150Labels permutation346 hz
    mixedMoment B raw8150step0 raw8150step0Labels = mixedMoment B raw8150step1 raw8150step1Labels := by
      have hz : ∀ j, raw8150step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8150step1 = (fun i j => raw8150step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8150step1 raw8150step0; decide +kernel
      have hl : raw8150step1Labels = raw8150step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8150step0 raw8150step0Labels permutation56 hz
    mixedMoment B raw8150step1 raw8150step1Labels = mixedMoment B raw8150step2 raw8150step2Labels := by
      have ha : raw8150step2 = (fun i j => raw8150step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8150step2 raw8150step1; decide +kernel
      have hl : raw8150step2Labels = raw8150step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8150step1 raw8150step1Labels permutation31 permutation5
    mixedMoment B raw8150step2 raw8150step2Labels = mixedMoment B raw8150step3 raw8150step3Labels := by
      have ha : raw8150step3 = raw8150step2 := by apply Matrix.ext; unfold raw8150step3 raw8150step2; decide +kernel
      have hl : raw8150step2Labels = labelEmbedding1 ∘ raw8150step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8150step2 raw8150step2Labels raw8150step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw8151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8151Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8151step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8151step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8151 raw8151Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw8151 raw8151Labels = mixedMoment B raw8151step0 raw8151step0Labels := by
      have hz : ∀ j, raw8151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8151step0 = (fun i j => raw8151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8151step0 raw8151; decide +kernel
      have hl : raw8151step0Labels = raw8151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8151 raw8151Labels permutation346 hz
    mixedMoment B raw8151step0 raw8151step0Labels = mixedMoment B raw8151step1 raw8151step1Labels := by
      have ha : raw8151step1 = (fun i j => raw8151step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8151step1 raw8151step0; decide +kernel
      have hl : raw8151step1Labels = raw8151step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8151step0 raw8151step0Labels permutation151 permutation5
    mixedMoment B raw8151step1 raw8151step1Labels = mixedMoment B raw8151step2 raw8151step2Labels := by
      have ha : raw8151step2 = raw8151step1 := by apply Matrix.ext; unfold raw8151step2 raw8151step1; decide +kernel
      have hl : raw8151step1Labels = labelEmbedding1 ∘ raw8151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8151step1 raw8151step1Labels raw8151step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw8152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8152Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8152step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8152step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8152 raw8152Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw8152 raw8152Labels = mixedMoment B raw8152step0 raw8152step0Labels := by
      have hz : ∀ j, raw8152 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8152step0 = (fun i j => raw8152 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8152step0 raw8152; decide +kernel
      have hl : raw8152step0Labels = raw8152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8152 raw8152Labels permutation265 hz
    mixedMoment B raw8152step0 raw8152step0Labels = mixedMoment B raw8152step1 raw8152step1Labels := by
      have ha : raw8152step1 = (fun i j => raw8152step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8152step1 raw8152step0; decide +kernel
      have hl : raw8152step1Labels = raw8152step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8152step0 raw8152step0Labels permutation151 permutation5
    mixedMoment B raw8152step1 raw8152step1Labels = mixedMoment B raw8152step2 raw8152step2Labels := by
      have ha : raw8152step2 = raw8152step1 := by apply Matrix.ext; unfold raw8152step2 raw8152step1; decide +kernel
      have hl : raw8152step1Labels = labelEmbedding1 ∘ raw8152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8152step1 raw8152step1Labels raw8152step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw8153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8153Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8153step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8153step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8153step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw8153step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8153step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw8153step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8153 raw8153Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw8153 raw8153Labels = mixedMoment B raw8153step0 raw8153step0Labels := by
      have hz : ∀ j, raw8153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8153step0 = (fun i j => raw8153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8153step0 raw8153; decide +kernel
      have hl : raw8153step0Labels = raw8153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8153 raw8153Labels permutation346 hz
    mixedMoment B raw8153step0 raw8153step0Labels = mixedMoment B raw8153step1 raw8153step1Labels := by
      have hz : ∀ j, raw8153step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8153step1 = (fun i j => raw8153step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8153step1 raw8153step0; decide +kernel
      have hl : raw8153step1Labels = raw8153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8153step0 raw8153step0Labels permutation56 hz
    mixedMoment B raw8153step1 raw8153step1Labels = mixedMoment B raw8153step2 raw8153step2Labels := by
      have ha : raw8153step2 = (fun i j => raw8153step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8153step2 raw8153step1; decide +kernel
      have hl : raw8153step2Labels = raw8153step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8153step1 raw8153step1Labels permutation30 permutation5
    mixedMoment B raw8153step2 raw8153step2Labels = mixedMoment B raw8153step3 raw8153step3Labels := by
      have ha : raw8153step3 = raw8153step2 := by apply Matrix.ext; unfold raw8153step3 raw8153step2; decide +kernel
      have hl : raw8153step2Labels = labelEmbedding1 ∘ raw8153step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8153step2 raw8153step2Labels raw8153step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw8154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8154Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8154step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8154step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8154step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8154step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw8154step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8154step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw8154step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8154step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw8154step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8154 raw8154Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw8154 raw8154Labels = mixedMoment B raw8154step0 raw8154step0Labels := by
      have hz : ∀ j, raw8154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8154step0 = (fun i j => raw8154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8154step0 raw8154; decide +kernel
      have hl : raw8154step0Labels = raw8154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8154 raw8154Labels permutation346 hz
    mixedMoment B raw8154step0 raw8154step0Labels = mixedMoment B raw8154step1 raw8154step1Labels := by
      have hz : ∀ j, raw8154step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8154step1 = (fun i j => raw8154step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8154step1 raw8154step0; decide +kernel
      have hl : raw8154step1Labels = raw8154step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8154step0 raw8154step0Labels permutation56 hz
    mixedMoment B raw8154step1 raw8154step1Labels = mixedMoment B raw8154step2 raw8154step2Labels := by
      have ha : raw8154step2 = (fun i j => raw8154step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8154step2 raw8154step1; decide +kernel
      have hl : raw8154step2Labels = raw8154step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8154step1 raw8154step1Labels permutation12 permutation7
    mixedMoment B raw8154step2 raw8154step2Labels = mixedMoment B raw8154step3 raw8154step3Labels := by
      have ha : raw8154step3 = -raw8154step2 := by apply Matrix.ext; change ∀ i j, raw8154step3 i j = -(raw8154step2 i j); unfold raw8154step3 raw8154step2; decide +kernel
      have hl : raw8154step3Labels = raw8154step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw8154step3 raw8154step3Labels = mixedMoment B raw8154step4 raw8154step4Labels := by
      have ha : raw8154step4 = raw8154step3 := by apply Matrix.ext; unfold raw8154step4 raw8154step3; decide +kernel
      have hl : raw8154step3Labels = labelEmbedding1 ∘ raw8154step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8154step3 raw8154step3Labels raw8154step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw8155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8155Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8155step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8155step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8155step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8155step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8155step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8155step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw8155step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8155 raw8155Labels = mixedMoment B node1072 node1072Labels := by
  calc
    mixedMoment B raw8155 raw8155Labels = mixedMoment B raw8155step0 raw8155step0Labels := by
      have hz : ∀ j, raw8155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8155step0 = (fun i j => raw8155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8155step0 raw8155; decide +kernel
      have hl : raw8155step0Labels = raw8155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8155 raw8155Labels permutation346 hz
    mixedMoment B raw8155step0 raw8155step0Labels = mixedMoment B raw8155step1 raw8155step1Labels := by
      have hz : ∀ j, raw8155step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8155step1 = (fun i j => raw8155step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8155step1 raw8155step0; decide +kernel
      have hl : raw8155step1Labels = raw8155step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8155step0 raw8155step0Labels permutation56 hz
    mixedMoment B raw8155step1 raw8155step1Labels = mixedMoment B raw8155step2 raw8155step2Labels := by
      have ha : raw8155step2 = (fun i j => raw8155step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8155step2 raw8155step1; decide +kernel
      have hl : raw8155step2Labels = raw8155step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8155step1 raw8155step1Labels permutation31 permutation5
    mixedMoment B raw8155step2 raw8155step2Labels = mixedMoment B raw8155step3 raw8155step3Labels := by
      have ha : raw8155step3 = raw8155step2 := by apply Matrix.ext; unfold raw8155step3 raw8155step2; decide +kernel
      have hl : raw8155step2Labels = labelEmbedding1 ∘ raw8155step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8155step2 raw8155step2Labels raw8155step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1072 node1072Labels := by rfl

def raw8156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8156step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8156 raw8156Labels = mixedMoment B node1070 node1070Labels := by
  calc
    mixedMoment B raw8156 raw8156Labels = mixedMoment B raw8156step0 raw8156step0Labels := by
      have hz : ∀ j, raw8156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8156step0 = (fun i j => raw8156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8156step0 raw8156; decide +kernel
      have hl : raw8156step0Labels = raw8156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8156 raw8156Labels permutation346 hz
    mixedMoment B raw8156step0 raw8156step0Labels = mixedMoment B raw8156step1 raw8156step1Labels := by
      have ha : raw8156step1 = (fun i j => raw8156step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8156step1 raw8156step0; decide +kernel
      have hl : raw8156step1Labels = raw8156step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8156step0 raw8156step0Labels permutation151 permutation5
    mixedMoment B raw8156step1 raw8156step1Labels = mixedMoment B raw8156step2 raw8156step2Labels := by
      have ha : raw8156step2 = raw8156step1 := by apply Matrix.ext; unfold raw8156step2 raw8156step1; decide +kernel
      have hl : raw8156step1Labels = labelEmbedding1 ∘ raw8156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8156step1 raw8156step1Labels raw8156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1070 node1070Labels := by rfl

def raw8157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8157Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8157step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8157step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8157step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8157step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw8157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8157 raw8157Labels = mixedMoment B node1070 node1070Labels := by
  calc
    mixedMoment B raw8157 raw8157Labels = mixedMoment B raw8157step0 raw8157step0Labels := by
      have hz : ∀ j, raw8157 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8157step0 = (fun i j => raw8157 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8157step0 raw8157; decide +kernel
      have hl : raw8157step0Labels = raw8157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8157 raw8157Labels permutation265 hz
    mixedMoment B raw8157step0 raw8157step0Labels = mixedMoment B raw8157step1 raw8157step1Labels := by
      have ha : raw8157step1 = (fun i j => raw8157step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8157step1 raw8157step0; decide +kernel
      have hl : raw8157step1Labels = raw8157step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8157step0 raw8157step0Labels permutation151 permutation5
    mixedMoment B raw8157step1 raw8157step1Labels = mixedMoment B raw8157step2 raw8157step2Labels := by
      have ha : raw8157step2 = raw8157step1 := by apply Matrix.ext; unfold raw8157step2 raw8157step1; decide +kernel
      have hl : raw8157step1Labels = labelEmbedding1 ∘ raw8157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8157step1 raw8157step1Labels raw8157step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1070 node1070Labels := by rfl

def raw8158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8158step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8158step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8158step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8158step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8158step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8158step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw8158step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8158 raw8158Labels = mixedMoment B node1076 node1076Labels := by
  calc
    mixedMoment B raw8158 raw8158Labels = mixedMoment B raw8158step0 raw8158step0Labels := by
      have hz : ∀ j, raw8158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8158step0 = (fun i j => raw8158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8158step0 raw8158; decide +kernel
      have hl : raw8158step0Labels = raw8158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8158 raw8158Labels permutation346 hz
    mixedMoment B raw8158step0 raw8158step0Labels = mixedMoment B raw8158step1 raw8158step1Labels := by
      have hz : ∀ j, raw8158step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8158step1 = (fun i j => raw8158step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8158step1 raw8158step0; decide +kernel
      have hl : raw8158step1Labels = raw8158step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8158step0 raw8158step0Labels permutation56 hz
    mixedMoment B raw8158step1 raw8158step1Labels = mixedMoment B raw8158step2 raw8158step2Labels := by
      have ha : raw8158step2 = (fun i j => raw8158step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8158step2 raw8158step1; decide +kernel
      have hl : raw8158step2Labels = raw8158step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8158step1 raw8158step1Labels permutation30 permutation5
    mixedMoment B raw8158step2 raw8158step2Labels = mixedMoment B raw8158step3 raw8158step3Labels := by
      have ha : raw8158step3 = raw8158step2 := by apply Matrix.ext; unfold raw8158step3 raw8158step2; decide +kernel
      have hl : raw8158step2Labels = labelEmbedding1 ∘ raw8158step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8158step2 raw8158step2Labels raw8158step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1076 node1076Labels := by rfl

def raw8159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8159step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8159step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw8159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8159step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw8159step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw8159step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8159 raw8159Labels = mixedMoment B node1084 node1084Labels := by
  calc
    mixedMoment B raw8159 raw8159Labels = mixedMoment B raw8159step0 raw8159step0Labels := by
      have hz : ∀ j, raw8159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8159step0 = (fun i j => raw8159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8159step0 raw8159; decide +kernel
      have hl : raw8159step0Labels = raw8159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8159 raw8159Labels permutation346 hz
    mixedMoment B raw8159step0 raw8159step0Labels = mixedMoment B raw8159step1 raw8159step1Labels := by
      have hz : ∀ j, raw8159step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8159step1 = (fun i j => raw8159step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8159step1 raw8159step0; decide +kernel
      have hl : raw8159step1Labels = raw8159step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8159step0 raw8159step0Labels permutation56 hz
    mixedMoment B raw8159step1 raw8159step1Labels = mixedMoment B raw8159step2 raw8159step2Labels := by
      have ha : raw8159step2 = (fun i j => raw8159step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw8159step2 raw8159step1; decide +kernel
      have hl : raw8159step2Labels = raw8159step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8159step1 raw8159step1Labels permutation28 permutation5
    mixedMoment B raw8159step2 raw8159step2Labels = mixedMoment B raw8159step3 raw8159step3Labels := by
      have ha : raw8159step3 = raw8159step2 := by apply Matrix.ext; unfold raw8159step3 raw8159step2; decide +kernel
      have hl : raw8159step2Labels = labelEmbedding1 ∘ raw8159step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8159step2 raw8159step2Labels raw8159step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1084 node1084Labels := by rfl

def raw8160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8160Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8160step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8160step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8160 raw8160Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw8160 raw8160Labels = mixedMoment B raw8160step0 raw8160step0Labels := by
      have hz : ∀ j, raw8160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8160step0 = (fun i j => raw8160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8160step0 raw8160; decide +kernel
      have hl : raw8160step0Labels = raw8160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8160 raw8160Labels permutation346 hz
    mixedMoment B raw8160step0 raw8160step0Labels = mixedMoment B raw8160step1 raw8160step1Labels := by
      have hz : ∀ j, raw8160step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8160step1 = (fun i j => raw8160step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8160step1 raw8160step0; decide +kernel
      have hl : raw8160step1Labels = raw8160step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8160step0 raw8160step0Labels permutation56 hz
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw8161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8161Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8161 raw8161Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw8161 raw8161Labels = mixedMoment B raw8161step0 raw8161step0Labels := by
      have hz : ∀ j, raw8161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8161step0 = (fun i j => raw8161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8161step0 raw8161; decide +kernel
      have hl : raw8161step0Labels = raw8161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8161 raw8161Labels permutation346 hz
    mixedMoment B raw8161step0 raw8161step0Labels = mixedMoment B raw8161step1 raw8161step1Labels := by
      have ha : raw8161step1 = (fun i j => raw8161step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8161step1 raw8161step0; decide +kernel
      have hl : raw8161step1Labels = raw8161step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8161step0 raw8161step0Labels permutation128 permutation4
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw8162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8162Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8162 raw8162Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw8162 raw8162Labels = mixedMoment B raw8162step0 raw8162step0Labels := by
      have hz : ∀ j, raw8162 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8162step0 = (fun i j => raw8162 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8162step0 raw8162; decide +kernel
      have hl : raw8162step0Labels = raw8162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8162 raw8162Labels permutation265 hz
    mixedMoment B raw8162step0 raw8162step0Labels = mixedMoment B raw8162step1 raw8162step1Labels := by
      have ha : raw8162step1 = (fun i j => raw8162step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8162step1 raw8162step0; decide +kernel
      have hl : raw8162step1Labels = raw8162step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8162step0 raw8162step0Labels permutation128 permutation4
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw8163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8163Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8163 raw8163Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw8163 raw8163Labels = mixedMoment B raw8163step0 raw8163step0Labels := by
      have hz : ∀ j, raw8163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8163step0 = (fun i j => raw8163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8163step0 raw8163; decide +kernel
      have hl : raw8163step0Labels = raw8163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8163 raw8163Labels permutation346 hz
    mixedMoment B raw8163step0 raw8163step0Labels = mixedMoment B raw8163step1 raw8163step1Labels := by
      have hz : ∀ j, raw8163step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8163step1 = (fun i j => raw8163step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8163step1 raw8163step0; decide +kernel
      have hl : raw8163step1Labels = raw8163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8163step0 raw8163step0Labels permutation56 hz
    mixedMoment B raw8163step1 raw8163step1Labels = mixedMoment B raw8163step2 raw8163step2Labels := by
      have ha : raw8163step2 = (fun i j => raw8163step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8163step2 raw8163step1; decide +kernel
      have hl : raw8163step2Labels = raw8163step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8163step1 raw8163step1Labels permutation27 permutation4
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw8164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8164Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8164step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8164step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8164 raw8164Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw8164 raw8164Labels = mixedMoment B raw8164step0 raw8164step0Labels := by
      have hz : ∀ j, raw8164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8164step0 = (fun i j => raw8164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8164step0 raw8164; decide +kernel
      have hl : raw8164step0Labels = raw8164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8164 raw8164Labels permutation346 hz
    mixedMoment B raw8164step0 raw8164step0Labels = mixedMoment B raw8164step1 raw8164step1Labels := by
      have hz : ∀ j, raw8164step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8164step1 = (fun i j => raw8164step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8164step1 raw8164step0; decide +kernel
      have hl : raw8164step1Labels = raw8164step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8164step0 raw8164step0Labels permutation56 hz
    mixedMoment B raw8164step1 raw8164step1Labels = mixedMoment B raw8164step2 raw8164step2Labels := by
      have ha : raw8164step2 = (fun i j => raw8164step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8164step2 raw8164step1; decide +kernel
      have hl : raw8164step2Labels = raw8164step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8164step1 raw8164step1Labels permutation26 permutation4
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw8165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8165Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw8165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8165 raw8165Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw8165 raw8165Labels = mixedMoment B raw8165step0 raw8165step0Labels := by
      have hz : ∀ j, raw8165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8165step0 = (fun i j => raw8165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8165step0 raw8165; decide +kernel
      have hl : raw8165step0Labels = raw8165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8165 raw8165Labels permutation346 hz
    mixedMoment B raw8165step0 raw8165step0Labels = mixedMoment B raw8165step1 raw8165step1Labels := by
      have hz : ∀ j, raw8165step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8165step1 = (fun i j => raw8165step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8165step1 raw8165step0; decide +kernel
      have hl : raw8165step1Labels = raw8165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8165step0 raw8165step0Labels permutation56 hz
    mixedMoment B raw8165step1 raw8165step1Labels = mixedMoment B raw8165step2 raw8165step2Labels := by
      have ha : raw8165step2 = (fun i j => raw8165step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8165step2 raw8165step1; decide +kernel
      have hl : raw8165step2Labels = raw8165step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8165step1 raw8165step1Labels permutation9 permutation2
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw8166 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![2, -2], ![-1, 1]]
def raw8166Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8166step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![2, -2], ![-1, 1]]
def raw8166step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8166step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![2, -2], ![-1, 1]]
def raw8166step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw8166step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw8166step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical8166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8166 raw8166Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw8166 raw8166Labels = mixedMoment B raw8166step0 raw8166step0Labels := by
      have hz : ∀ j, raw8166 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8166step0 = (fun i j => raw8166 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8166step0 raw8166; decide +kernel
      have hl : raw8166step0Labels = raw8166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8166 raw8166Labels permutation346 hz
    mixedMoment B raw8166step0 raw8166step0Labels = mixedMoment B raw8166step1 raw8166step1Labels := by
      have hz : ∀ j, raw8166step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8166step1 = (fun i j => raw8166step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8166step1 raw8166step0; decide +kernel
      have hl : raw8166step1Labels = raw8166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8166step0 raw8166step0Labels permutation56 hz
    mixedMoment B raw8166step1 raw8166step1Labels = mixedMoment B raw8166step2 raw8166step2Labels := by
      have ha : raw8166step2 = (fun i j => raw8166step1 (permutation12 i) (permutation0 j)) := by apply Matrix.ext; unfold raw8166step2 raw8166step1; decide +kernel
      have hl : raw8166step2Labels = raw8166step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8166step1 raw8166step1Labels permutation12 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw8167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8167Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8167 raw8167Labels = mixedMoment B node1268 node1268Labels := by
  calc
    mixedMoment B raw8167 raw8167Labels = mixedMoment B raw8167step0 raw8167step0Labels := by
      have hz : ∀ j, raw8167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8167step0 = (fun i j => raw8167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8167step0 raw8167; decide +kernel
      have hl : raw8167step0Labels = raw8167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8167 raw8167Labels permutation346 hz
    mixedMoment B raw8167step0 raw8167step0Labels = mixedMoment B raw8167step1 raw8167step1Labels := by
      have ha : raw8167step1 = (fun i j => raw8167step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8167step1 raw8167step0; decide +kernel
      have hl : raw8167step1Labels = raw8167step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8167step0 raw8167step0Labels permutation38 permutation2
    _ = mixedMoment B node1268 node1268Labels := by rfl

def raw8168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8168Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8168 raw8168Labels = mixedMoment B node1268 node1268Labels := by
  calc
    mixedMoment B raw8168 raw8168Labels = mixedMoment B raw8168step0 raw8168step0Labels := by
      have hz : ∀ j, raw8168 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8168step0 = (fun i j => raw8168 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8168step0 raw8168; decide +kernel
      have hl : raw8168step0Labels = raw8168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8168 raw8168Labels permutation265 hz
    mixedMoment B raw8168step0 raw8168step0Labels = mixedMoment B raw8168step1 raw8168step1Labels := by
      have ha : raw8168step1 = (fun i j => raw8168step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8168step1 raw8168step0; decide +kernel
      have hl : raw8168step1Labels = raw8168step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8168step0 raw8168step0Labels permutation38 permutation2
    _ = mixedMoment B node1268 node1268Labels := by rfl

def raw8169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8169Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8169step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8169 raw8169Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw8169 raw8169Labels = mixedMoment B raw8169step0 raw8169step0Labels := by
      have hz : ∀ j, raw8169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8169step0 = (fun i j => raw8169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8169step0 raw8169; decide +kernel
      have hl : raw8169step0Labels = raw8169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8169 raw8169Labels permutation346 hz
    mixedMoment B raw8169step0 raw8169step0Labels = mixedMoment B raw8169step1 raw8169step1Labels := by
      have hz : ∀ j, raw8169step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8169step1 = (fun i j => raw8169step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8169step1 raw8169step0; decide +kernel
      have hl : raw8169step1Labels = raw8169step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8169step0 raw8169step0Labels permutation56 hz
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw8170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8170Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8170step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8170step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8170 raw8170Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw8170 raw8170Labels = mixedMoment B raw8170step0 raw8170step0Labels := by
      have hz : ∀ j, raw8170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8170step0 = (fun i j => raw8170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8170step0 raw8170; decide +kernel
      have hl : raw8170step0Labels = raw8170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8170 raw8170Labels permutation346 hz
    mixedMoment B raw8170step0 raw8170step0Labels = mixedMoment B raw8170step1 raw8170step1Labels := by
      have hz : ∀ j, raw8170step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8170step1 = (fun i j => raw8170step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8170step1 raw8170step0; decide +kernel
      have hl : raw8170step1Labels = raw8170step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8170step0 raw8170step0Labels permutation56 hz
    mixedMoment B raw8170step1 raw8170step1Labels = mixedMoment B raw8170step2 raw8170step2Labels := by
      have ha : raw8170step2 = (fun i j => raw8170step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8170step2 raw8170step1; decide +kernel
      have hl : raw8170step2Labels = raw8170step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8170step1 raw8170step1Labels permutation9 permutation2
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw8171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8171Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8171step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8171 raw8171Labels = mixedMoment B node1272 node1272Labels := by
  calc
    mixedMoment B raw8171 raw8171Labels = mixedMoment B raw8171step0 raw8171step0Labels := by
      have hz : ∀ j, raw8171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8171step0 = (fun i j => raw8171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8171step0 raw8171; decide +kernel
      have hl : raw8171step0Labels = raw8171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8171 raw8171Labels permutation346 hz
    mixedMoment B raw8171step0 raw8171step0Labels = mixedMoment B raw8171step1 raw8171step1Labels := by
      have hz : ∀ j, raw8171step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8171step1 = (fun i j => raw8171step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8171step1 raw8171step0; decide +kernel
      have hl : raw8171step1Labels = raw8171step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8171step0 raw8171step0Labels permutation56 hz
    _ = mixedMoment B node1272 node1272Labels := by rfl

def raw8172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8172Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8172 raw8172Labels = mixedMoment B node2571 node2571Labels := by
  calc
    mixedMoment B raw8172 raw8172Labels = mixedMoment B raw8172step0 raw8172step0Labels := by
      have ha : raw8172step0 = (fun i j => raw8172 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8172step0 raw8172; decide +kernel
      have hl : raw8172step0Labels = raw8172Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8172 raw8172Labels permutation182 permutation2
    _ = mixedMoment B node2571 node2571Labels := by rfl

def raw8173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8173Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8173 raw8173Labels = mixedMoment B node2639 node2639Labels := by
  calc
    mixedMoment B raw8173 raw8173Labels = mixedMoment B raw8173step0 raw8173step0Labels := by
      have hz : ∀ j, raw8173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8173step0 = (fun i j => raw8173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8173step0 raw8173; decide +kernel
      have hl : raw8173step0Labels = raw8173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8173 raw8173Labels permutation346 hz
    mixedMoment B raw8173step0 raw8173step0Labels = mixedMoment B raw8173step1 raw8173step1Labels := by
      have ha : raw8173step1 = (fun i j => raw8173step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8173step1 raw8173step0; decide +kernel
      have hl : raw8173step1Labels = raw8173step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8173step0 raw8173step0Labels permutation38 permutation2
    _ = mixedMoment B node2639 node2639Labels := by rfl

def raw8174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8174Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -3, 1]]
def raw8174step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw8174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8174 raw8174Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw8174 raw8174Labels = mixedMoment B raw8174step0 raw8174step0Labels := by
      have hz : ∀ j, raw8174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8174step0 = (fun i j => raw8174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8174step0 raw8174; decide +kernel
      have hl : raw8174step0Labels = raw8174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8174 raw8174Labels permutation346 hz
    mixedMoment B raw8174step0 raw8174step0Labels = mixedMoment B raw8174step1 raw8174step1Labels := by
      have ha : raw8174step1 = (fun i j => raw8174step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8174step1 raw8174step0; decide +kernel
      have hl : raw8174step1Labels = raw8174step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8174step0 raw8174step0Labels permutation40 permutation2
    _ = mixedMoment B node2759 node2759Labels := by rfl

def raw8175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8175Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1]]
def raw8175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8175 raw8175Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw8175 raw8175Labels = mixedMoment B raw8175step0 raw8175step0Labels := by
      have hz : ∀ j, raw8175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8175step0 = (fun i j => raw8175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8175step0 raw8175; decide +kernel
      have hl : raw8175step0Labels = raw8175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8175 raw8175Labels permutation346 hz
    mixedMoment B raw8175step0 raw8175step0Labels = mixedMoment B raw8175step1 raw8175step1Labels := by
      have ha : raw8175step1 = (fun i j => raw8175step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8175step1 raw8175step0; decide +kernel
      have hl : raw8175step1Labels = raw8175step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8175step0 raw8175step0Labels permutation42 permutation2
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw8176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8176Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8176 raw8176Labels = mixedMoment B node2571 node2571Labels := by
  calc
    mixedMoment B raw8176 raw8176Labels = mixedMoment B raw8176step0 raw8176step0Labels := by
      have ha : raw8176step0 = (fun i j => raw8176 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8176step0 raw8176; decide +kernel
      have hl : raw8176step0Labels = raw8176Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8176 raw8176Labels permutation158 permutation2
    _ = mixedMoment B node2571 node2571Labels := by rfl

def raw8177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8177Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8177 raw8177Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw8177 raw8177Labels = mixedMoment B raw8177step0 raw8177step0Labels := by
      have hz : ∀ j, raw8177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8177step0 = (fun i j => raw8177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8177step0 raw8177; decide +kernel
      have hl : raw8177step0Labels = raw8177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8177 raw8177Labels permutation346 hz
    _ = mixedMoment B node2600 node2600Labels := by rfl

def raw8178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8178Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8178 raw8178Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw8178 raw8178Labels = mixedMoment B raw8178step0 raw8178step0Labels := by
      have hz : ∀ j, raw8178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8178step0 = (fun i j => raw8178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8178step0 raw8178; decide +kernel
      have hl : raw8178step0Labels = raw8178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8178 raw8178Labels permutation346 hz
    mixedMoment B raw8178step0 raw8178step0Labels = mixedMoment B raw8178step1 raw8178step1Labels := by
      have ha : raw8178step1 = (fun i j => raw8178step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8178step1 raw8178step0; decide +kernel
      have hl : raw8178step1Labels = raw8178step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8178step0 raw8178step0Labels permutation33 permutation2
    _ = mixedMoment B node2575 node2575Labels := by rfl

def raw8179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8179 raw8179Labels = mixedMoment B node1433 node1433Labels := by
  calc
    mixedMoment B raw8179 raw8179Labels = mixedMoment B raw8179step0 raw8179step0Labels := by
      have hz : ∀ j, raw8179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8179step0 = (fun i j => raw8179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8179step0 raw8179; decide +kernel
      have hl : raw8179step0Labels = raw8179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8179 raw8179Labels permutation346 hz
    mixedMoment B raw8179step0 raw8179step0Labels = mixedMoment B raw8179step1 raw8179step1Labels := by
      have ha : raw8179step1 = (fun i j => raw8179step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8179step1 raw8179step0; decide +kernel
      have hl : raw8179step1Labels = raw8179step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8179step0 raw8179step0Labels permutation128 permutation4
    _ = mixedMoment B node1433 node1433Labels := by rfl

def raw8180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8180step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw8180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8180 raw8180Labels = mixedMoment B node2639 node2639Labels := by
  calc
    mixedMoment B raw8180 raw8180Labels = mixedMoment B raw8180step0 raw8180step0Labels := by
      have hz : ∀ j, raw8180 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8180step0 = (fun i j => raw8180 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8180step0 raw8180; decide +kernel
      have hl : raw8180step0Labels = raw8180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8180 raw8180Labels permutation265 hz
    mixedMoment B raw8180step0 raw8180step0Labels = mixedMoment B raw8180step1 raw8180step1Labels := by
      have ha : raw8180step1 = (fun i j => raw8180step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8180step1 raw8180step0; decide +kernel
      have hl : raw8180step1Labels = raw8180step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8180step0 raw8180step0Labels permutation38 permutation2
    _ = mixedMoment B node2639 node2639Labels := by rfl

def raw8181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8181step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8181 raw8181Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw8181 raw8181Labels = mixedMoment B raw8181step0 raw8181step0Labels := by
      have hz : ∀ j, raw8181 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8181step0 = (fun i j => raw8181 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8181step0 raw8181; decide +kernel
      have hl : raw8181step0Labels = raw8181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8181 raw8181Labels permutation346 hz
    mixedMoment B raw8181step0 raw8181step0Labels = mixedMoment B raw8181step1 raw8181step1Labels := by
      have hz : ∀ j, raw8181step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8181step1 = (fun i j => raw8181step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8181step1 raw8181step0; decide +kernel
      have hl : raw8181step1Labels = raw8181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8181step0 raw8181step0Labels permutation56 hz
    mixedMoment B raw8181step1 raw8181step1Labels = mixedMoment B raw8181step2 raw8181step2Labels := by
      have ha : raw8181step2 = (fun i j => raw8181step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8181step2 raw8181step1; decide +kernel
      have hl : raw8181step2Labels = raw8181step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8181step1 raw8181step1Labels permutation9 permutation2
    _ = mixedMoment B node2643 node2643Labels := by rfl

def raw8182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 1, -2], ![2, -1, -1]]
def raw8182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8182 raw8182Labels = mixedMoment B node1437 node1437Labels := by
  calc
    mixedMoment B raw8182 raw8182Labels = mixedMoment B raw8182step0 raw8182step0Labels := by
      have hz : ∀ j, raw8182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8182step0 = (fun i j => raw8182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8182step0 raw8182; decide +kernel
      have hl : raw8182step0Labels = raw8182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8182 raw8182Labels permutation346 hz
    mixedMoment B raw8182step0 raw8182step0Labels = mixedMoment B raw8182step1 raw8182step1Labels := by
      have hz : ∀ j, raw8182step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8182step1 = (fun i j => raw8182step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8182step1 raw8182step0; decide +kernel
      have hl : raw8182step1Labels = raw8182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8182step0 raw8182step0Labels permutation56 hz
    mixedMoment B raw8182step1 raw8182step1Labels = mixedMoment B raw8182step2 raw8182step2Labels := by
      have ha : raw8182step2 = (fun i j => raw8182step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8182step2 raw8182step1; decide +kernel
      have hl : raw8182step2Labels = raw8182step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8182step1 raw8182step1Labels permutation27 permutation4
    _ = mixedMoment B node1437 node1437Labels := by rfl

def raw8183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -3, 1]]
def raw8183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw8183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8183 raw8183Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw8183 raw8183Labels = mixedMoment B raw8183step0 raw8183step0Labels := by
      have hz : ∀ j, raw8183 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8183step0 = (fun i j => raw8183 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8183step0 raw8183; decide +kernel
      have hl : raw8183step0Labels = raw8183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8183 raw8183Labels permutation265 hz
    mixedMoment B raw8183step0 raw8183step0Labels = mixedMoment B raw8183step1 raw8183step1Labels := by
      have ha : raw8183step1 = (fun i j => raw8183step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8183step1 raw8183step0; decide +kernel
      have hl : raw8183step1Labels = raw8183step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8183step0 raw8183step0Labels permutation33 permutation2
    _ = mixedMoment B node2575 node2575Labels := by rfl

def raw8184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, 0, -2], ![1, -2, 1]]
def raw8184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw8184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8184 raw8184Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw8184 raw8184Labels = mixedMoment B raw8184step0 raw8184step0Labels := by
      have hz : ∀ j, raw8184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8184step0 = (fun i j => raw8184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8184step0 raw8184; decide +kernel
      have hl : raw8184step0Labels = raw8184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8184 raw8184Labels permutation346 hz
    mixedMoment B raw8184step0 raw8184step0Labels = mixedMoment B raw8184step1 raw8184step1Labels := by
      have hz : ∀ j, raw8184step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8184step1 = (fun i j => raw8184step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8184step1 raw8184step0; decide +kernel
      have hl : raw8184step1Labels = raw8184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8184step0 raw8184step0Labels permutation56 hz
    mixedMoment B raw8184step1 raw8184step1Labels = mixedMoment B raw8184step2 raw8184step2Labels := by
      have ha : raw8184step2 = (fun i j => raw8184step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw8184step2 raw8184step1; decide +kernel
      have hl : raw8184step2Labels = raw8184step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8184step1 raw8184step1Labels permutation9 permutation2
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw8185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8185Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -4, 1]]
def raw8185step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw8185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8185 raw8185Labels = mixedMoment B node1433 node1433Labels := by
  calc
    mixedMoment B raw8185 raw8185Labels = mixedMoment B raw8185step0 raw8185step0Labels := by
      have hz : ∀ j, raw8185 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8185step0 = (fun i j => raw8185 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8185step0 raw8185; decide +kernel
      have hl : raw8185step0Labels = raw8185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8185 raw8185Labels permutation265 hz
    mixedMoment B raw8185step0 raw8185step0Labels = mixedMoment B raw8185step1 raw8185step1Labels := by
      have ha : raw8185step1 = (fun i j => raw8185step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8185step1 raw8185step0; decide +kernel
      have hl : raw8185step1Labels = raw8185step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8185step0 raw8185step0Labels permutation128 permutation4
    _ = mixedMoment B node1433 node1433Labels := by rfl

def raw8186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8186step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8186step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![3, -4, 1]]
def raw8186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw8186step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw8186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical8186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8186 raw8186Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw8186 raw8186Labels = mixedMoment B raw8186step0 raw8186step0Labels := by
      have hz : ∀ j, raw8186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8186step0 = (fun i j => raw8186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8186step0 raw8186; decide +kernel
      have hl : raw8186step0Labels = raw8186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8186 raw8186Labels permutation346 hz
    mixedMoment B raw8186step0 raw8186step0Labels = mixedMoment B raw8186step1 raw8186step1Labels := by
      have hz : ∀ j, raw8186step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8186step1 = (fun i j => raw8186step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8186step1 raw8186step0; decide +kernel
      have hl : raw8186step1Labels = raw8186step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8186step0 raw8186step0Labels permutation56 hz
    mixedMoment B raw8186step1 raw8186step1Labels = mixedMoment B raw8186step2 raw8186step2Labels := by
      have ha : raw8186step2 = (fun i j => raw8186step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw8186step2 raw8186step1; decide +kernel
      have hl : raw8186step2Labels = raw8186step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8186step1 raw8186step1Labels permutation26 permutation4
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw8187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8187step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8187step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8187 raw8187Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw8187 raw8187Labels = mixedMoment B raw8187step0 raw8187step0Labels := by
      have hz : ∀ j, raw8187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8187step0 = (fun i j => raw8187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8187step0 raw8187; decide +kernel
      have hl : raw8187step0Labels = raw8187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8187 raw8187Labels permutation346 hz
    mixedMoment B raw8187step0 raw8187step0Labels = mixedMoment B raw8187step1 raw8187step1Labels := by
      have ha : raw8187step1 = (fun i j => raw8187step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8187step1 raw8187step0; decide +kernel
      have hl : raw8187step1Labels = raw8187step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8187step0 raw8187step0Labels permutation139 permutation7
    mixedMoment B raw8187step1 raw8187step1Labels = mixedMoment B raw8187step2 raw8187step2Labels := by
      have ha : raw8187step2 = raw8187step1 := by apply Matrix.ext; unfold raw8187step2 raw8187step1; decide +kernel
      have hl : raw8187step1Labels = labelEmbedding10 ∘ raw8187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8187step1 raw8187step1Labels raw8187step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw8188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8188step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw8188step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8188 raw8188Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw8188 raw8188Labels = mixedMoment B raw8188step0 raw8188step0Labels := by
      have hz : ∀ j, raw8188 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw8188step0 = (fun i j => raw8188 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw8188step0 raw8188; decide +kernel
      have hl : raw8188step0Labels = raw8188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8188 raw8188Labels permutation265 hz
    mixedMoment B raw8188step0 raw8188step0Labels = mixedMoment B raw8188step1 raw8188step1Labels := by
      have ha : raw8188step1 = (fun i j => raw8188step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8188step1 raw8188step0; decide +kernel
      have hl : raw8188step1Labels = raw8188step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8188step0 raw8188step0Labels permutation139 permutation7
    mixedMoment B raw8188step1 raw8188step1Labels = mixedMoment B raw8188step2 raw8188step2Labels := by
      have ha : raw8188step2 = raw8188step1 := by apply Matrix.ext; unfold raw8188step2 raw8188step1; decide +kernel
      have hl : raw8188step1Labels = labelEmbedding10 ∘ raw8188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8188step1 raw8188step1Labels raw8188step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw8189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8189step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8189step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8189step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8189step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw8189step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8189step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8189 raw8189Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw8189 raw8189Labels = mixedMoment B raw8189step0 raw8189step0Labels := by
      have hz : ∀ j, raw8189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8189step0 = (fun i j => raw8189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8189step0 raw8189; decide +kernel
      have hl : raw8189step0Labels = raw8189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8189 raw8189Labels permutation346 hz
    mixedMoment B raw8189step0 raw8189step0Labels = mixedMoment B raw8189step1 raw8189step1Labels := by
      have hz : ∀ j, raw8189step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8189step1 = (fun i j => raw8189step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8189step1 raw8189step0; decide +kernel
      have hl : raw8189step1Labels = raw8189step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8189step0 raw8189step0Labels permutation56 hz
    mixedMoment B raw8189step1 raw8189step1Labels = mixedMoment B raw8189step2 raw8189step2Labels := by
      have ha : raw8189step2 = (fun i j => raw8189step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw8189step2 raw8189step1; decide +kernel
      have hl : raw8189step2Labels = raw8189step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8189step1 raw8189step1Labels permutation31 permutation7
    mixedMoment B raw8189step2 raw8189step2Labels = mixedMoment B raw8189step3 raw8189step3Labels := by
      have ha : raw8189step3 = raw8189step2 := by apply Matrix.ext; unfold raw8189step3 raw8189step2; decide +kernel
      have hl : raw8189step2Labels = labelEmbedding10 ∘ raw8189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8189step2 raw8189step2Labels raw8189step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw8190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8190step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 2, -3]]
def raw8190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8190step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8190step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw8190step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw8190step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8190 raw8190Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw8190 raw8190Labels = mixedMoment B raw8190step0 raw8190step0Labels := by
      have hz : ∀ j, raw8190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8190step0 = (fun i j => raw8190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8190step0 raw8190; decide +kernel
      have hl : raw8190step0Labels = raw8190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8190 raw8190Labels permutation346 hz
    mixedMoment B raw8190step0 raw8190step0Labels = mixedMoment B raw8190step1 raw8190step1Labels := by
      have hz : ∀ j, raw8190step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw8190step1 = (fun i j => raw8190step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw8190step1 raw8190step0; decide +kernel
      have hl : raw8190step1Labels = raw8190step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8190step0 raw8190step0Labels permutation56 hz
    mixedMoment B raw8190step1 raw8190step1Labels = mixedMoment B raw8190step2 raw8190step2Labels := by
      have ha : raw8190step2 = (fun i j => raw8190step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw8190step2 raw8190step1; decide +kernel
      have hl : raw8190step2Labels = raw8190step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8190step1 raw8190step1Labels permutation26 permutation6
    mixedMoment B raw8190step2 raw8190step2Labels = mixedMoment B raw8190step3 raw8190step3Labels := by
      have ha : raw8190step3 = raw8190step2 := by apply Matrix.ext; unfold raw8190step3 raw8190step2; decide +kernel
      have hl : raw8190step2Labels = labelEmbedding9 ∘ raw8190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8190step2 raw8190step2Labels raw8190step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw8191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw8191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw8191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8191step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw8191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw8191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical8191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw8191 raw8191Labels = mixedMoment B node4462 node4462Labels := by
  calc
    mixedMoment B raw8191 raw8191Labels = mixedMoment B raw8191step0 raw8191step0Labels := by
      have hz : ∀ j, raw8191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw8191step0 = (fun i j => raw8191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw8191step0 raw8191; decide +kernel
      have hl : raw8191step0Labels = raw8191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw8191 raw8191Labels permutation346 hz
    mixedMoment B raw8191step0 raw8191step0Labels = mixedMoment B raw8191step1 raw8191step1Labels := by
      have ha : raw8191step1 = (fun i j => raw8191step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw8191step1 raw8191step0; decide +kernel
      have hl : raw8191step1Labels = raw8191step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw8191step0 raw8191step0Labels permutation38 permutation3
    mixedMoment B raw8191step1 raw8191step1Labels = mixedMoment B raw8191step2 raw8191step2Labels := by
      have ha : raw8191step2 = raw8191step1 := by apply Matrix.ext; unfold raw8191step2 raw8191step1; decide +kernel
      have hl : raw8191step1Labels = labelEmbedding6 ∘ raw8191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw8191step1 raw8191step1Labels raw8191step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4462 node4462Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
