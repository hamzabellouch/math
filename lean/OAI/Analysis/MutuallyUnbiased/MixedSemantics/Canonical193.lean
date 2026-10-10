import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24704Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24704step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24704step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24704 raw24704Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw24704 raw24704Labels = mixedMoment B raw24704step0 raw24704step0Labels := by
      have hz : ∀ j, raw24704 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24704step0 = (fun i j => raw24704 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24704step0 raw24704; decide +kernel
      have hl : raw24704step0Labels = raw24704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24704 raw24704Labels permutation265 hz
    mixedMoment B raw24704step0 raw24704step0Labels = mixedMoment B raw24704step1 raw24704step1Labels := by
      have ha : raw24704step1 = (fun i j => raw24704step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24704step1 raw24704step0; decide +kernel
      have hl : raw24704step1Labels = raw24704step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24704step0 raw24704step0Labels permutation36 permutation3
    _ = mixedMoment B node1261 node1261Labels := by rfl

def raw24705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24705Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24705step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24705step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24705 raw24705Labels = mixedMoment B node581 node581Labels := by
  calc
    mixedMoment B raw24705 raw24705Labels = mixedMoment B raw24705step0 raw24705step0Labels := by
      have hz : ∀ j, raw24705 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24705step0 = (fun i j => raw24705 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24705step0 raw24705; decide +kernel
      have hl : raw24705step0Labels = raw24705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24705 raw24705Labels permutation265 hz
    mixedMoment B raw24705step0 raw24705step0Labels = mixedMoment B raw24705step1 raw24705step1Labels := by
      have ha : raw24705step1 = (fun i j => raw24705step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24705step1 raw24705step0; decide +kernel
      have hl : raw24705step1Labels = raw24705step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24705step0 raw24705step0Labels permutation32 permutation3
    _ = mixedMoment B node581 node581Labels := by rfl

def raw24706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24706Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24706step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24706 raw24706Labels = mixedMoment B node1112 node1112Labels := by
  calc
    mixedMoment B raw24706 raw24706Labels = mixedMoment B raw24706step0 raw24706step0Labels := by
      have ha : raw24706step0 = (fun i j => raw24706 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24706step0 raw24706; decide +kernel
      have hl : raw24706step0Labels = raw24706Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24706 raw24706Labels permutation152 permutation3
    _ = mixedMoment B node1112 node1112Labels := by rfl

def raw24707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24707Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24707step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24707step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24707step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw24707step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24707 raw24707Labels = mixedMoment B node1165 node1165Labels := by
  calc
    mixedMoment B raw24707 raw24707Labels = mixedMoment B raw24707step0 raw24707step0Labels := by
      have hz : ∀ j, raw24707 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24707step0 = (fun i j => raw24707 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24707step0 raw24707; decide +kernel
      have hl : raw24707step0Labels = raw24707Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24707 raw24707Labels permutation265 hz
    mixedMoment B raw24707step0 raw24707step0Labels = mixedMoment B raw24707step1 raw24707step1Labels := by
      have ha : raw24707step1 = (fun i j => raw24707step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24707step1 raw24707step0; decide +kernel
      have hl : raw24707step1Labels = raw24707step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24707step0 raw24707step0Labels permutation32 permutation3
    _ = mixedMoment B node1165 node1165Labels := by rfl

def raw24708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24708Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24708step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw24708step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24708 raw24708Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw24708 raw24708Labels = mixedMoment B raw24708step0 raw24708step0Labels := by
      have hz : ∀ j, raw24708 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24708step0 = (fun i j => raw24708 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24708step0 raw24708; decide +kernel
      have hl : raw24708step0Labels = raw24708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24708 raw24708Labels permutation265 hz
    mixedMoment B raw24708step0 raw24708step0Labels = mixedMoment B raw24708step1 raw24708step1Labels := by
      have ha : raw24708step1 = (fun i j => raw24708step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24708step1 raw24708step0; decide +kernel
      have hl : raw24708step1Labels = raw24708step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24708step0 raw24708step0Labels permutation38 permutation3
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw24709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw24709Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24709step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24709step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24709step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24709step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24709 raw24709Labels = mixedMoment B node1269 node1269Labels := by
  calc
    mixedMoment B raw24709 raw24709Labels = mixedMoment B raw24709step0 raw24709step0Labels := by
      have hz : ∀ j, raw24709 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24709step0 = (fun i j => raw24709 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24709step0 raw24709; decide +kernel
      have hl : raw24709step0Labels = raw24709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24709 raw24709Labels permutation520 hz
    mixedMoment B raw24709step0 raw24709step0Labels = mixedMoment B raw24709step1 raw24709step1Labels := by
      have hz : ∀ j, raw24709step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24709step1 = (fun i j => raw24709step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24709step1 raw24709step0; decide +kernel
      have hl : raw24709step1Labels = raw24709step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24709step0 raw24709step0Labels permutation56 hz
    mixedMoment B raw24709step1 raw24709step1Labels = mixedMoment B raw24709step2 raw24709step2Labels := by
      have ha : raw24709step2 = (fun i j => raw24709step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24709step2 raw24709step1; decide +kernel
      have hl : raw24709step2Labels = raw24709step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24709step1 raw24709step1Labels permutation8 permutation3
    _ = mixedMoment B node1269 node1269Labels := by rfl

def raw24710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24710step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24710step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24710step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24710step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24710 raw24710Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw24710 raw24710Labels = mixedMoment B raw24710step0 raw24710step0Labels := by
      have ha : raw24710step0 = (fun i j => raw24710 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24710step0 raw24710; decide +kernel
      have hl : raw24710step0Labels = raw24710Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24710 raw24710Labels permutation178 permutation7
    mixedMoment B raw24710step0 raw24710step0Labels = mixedMoment B raw24710step1 raw24710step1Labels := by
      have ha : raw24710step1 = -raw24710step0 := by apply Matrix.ext; change ∀ i j, raw24710step1 i j = -(raw24710step0 i j); unfold raw24710step1 raw24710step0; decide +kernel
      have hl : raw24710step1Labels = raw24710step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24710step1 raw24710step1Labels = mixedMoment B raw24710step2 raw24710step2Labels := by
      have ha : raw24710step2 = raw24710step1 := by apply Matrix.ext; unfold raw24710step2 raw24710step1; decide +kernel
      have hl : raw24710step1Labels = labelEmbedding1 ∘ raw24710step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24710step1 raw24710step1Labels raw24710step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw24711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24711step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24711step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24711step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24711 raw24711Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw24711 raw24711Labels = mixedMoment B raw24711step0 raw24711step0Labels := by
      have hz : ∀ j, raw24711 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24711step0 = (fun i j => raw24711 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24711step0 raw24711; decide +kernel
      have hl : raw24711step0Labels = raw24711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24711 raw24711Labels permutation265 hz
    mixedMoment B raw24711step0 raw24711step0Labels = mixedMoment B raw24711step1 raw24711step1Labels := by
      have ha : raw24711step1 = (fun i j => raw24711step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24711step1 raw24711step0; decide +kernel
      have hl : raw24711step1Labels = raw24711step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24711step0 raw24711step0Labels permutation34 permutation7
    mixedMoment B raw24711step1 raw24711step1Labels = mixedMoment B raw24711step2 raw24711step2Labels := by
      have ha : raw24711step2 = -raw24711step1 := by apply Matrix.ext; change ∀ i j, raw24711step2 i j = -(raw24711step1 i j); unfold raw24711step2 raw24711step1; decide +kernel
      have hl : raw24711step2Labels = raw24711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24711step2 raw24711step2Labels = mixedMoment B raw24711step3 raw24711step3Labels := by
      have ha : raw24711step3 = raw24711step2 := by apply Matrix.ext; unfold raw24711step3 raw24711step2; decide +kernel
      have hl : raw24711step2Labels = labelEmbedding1 ∘ raw24711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24711step2 raw24711step2Labels raw24711step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

def raw24712 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24712Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24712step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24712step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24712step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24712step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24712step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24712 raw24712Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw24712 raw24712Labels = mixedMoment B raw24712step0 raw24712step0Labels := by
      have hz : ∀ j, raw24712 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24712step0 = (fun i j => raw24712 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24712step0 raw24712; decide +kernel
      have hl : raw24712step0Labels = raw24712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24712 raw24712Labels permutation265 hz
    mixedMoment B raw24712step0 raw24712step0Labels = mixedMoment B raw24712step1 raw24712step1Labels := by
      have ha : raw24712step1 = (fun i j => raw24712step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24712step1 raw24712step0; decide +kernel
      have hl : raw24712step1Labels = raw24712step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24712step0 raw24712step0Labels permutation34 permutation7
    mixedMoment B raw24712step1 raw24712step1Labels = mixedMoment B raw24712step2 raw24712step2Labels := by
      have ha : raw24712step2 = -raw24712step1 := by apply Matrix.ext; change ∀ i j, raw24712step2 i j = -(raw24712step1 i j); unfold raw24712step2 raw24712step1; decide +kernel
      have hl : raw24712step2Labels = raw24712step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24712step2 raw24712step2Labels = mixedMoment B raw24712step3 raw24712step3Labels := by
      have ha : raw24712step3 = raw24712step2 := by apply Matrix.ext; unfold raw24712step3 raw24712step2; decide +kernel
      have hl : raw24712step2Labels = labelEmbedding1 ∘ raw24712step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24712step2 raw24712step2Labels raw24712step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw24713 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24713Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24713step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24713step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24713step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24713step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24713step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24713step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24713 raw24713Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw24713 raw24713Labels = mixedMoment B raw24713step0 raw24713step0Labels := by
      have hz : ∀ j, raw24713 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24713step0 = (fun i j => raw24713 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24713step0 raw24713; decide +kernel
      have hl : raw24713step0Labels = raw24713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24713 raw24713Labels permutation520 hz
    mixedMoment B raw24713step0 raw24713step0Labels = mixedMoment B raw24713step1 raw24713step1Labels := by
      have hz : ∀ j, raw24713step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24713step1 = (fun i j => raw24713step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24713step1 raw24713step0; decide +kernel
      have hl : raw24713step1Labels = raw24713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24713step0 raw24713step0Labels permutation56 hz
    mixedMoment B raw24713step1 raw24713step1Labels = mixedMoment B raw24713step2 raw24713step2Labels := by
      have ha : raw24713step2 = (fun i j => raw24713step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24713step2 raw24713step1; decide +kernel
      have hl : raw24713step2Labels = raw24713step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24713step1 raw24713step1Labels permutation8 permutation7
    mixedMoment B raw24713step2 raw24713step2Labels = mixedMoment B raw24713step3 raw24713step3Labels := by
      have ha : raw24713step3 = -raw24713step2 := by apply Matrix.ext; change ∀ i j, raw24713step3 i j = -(raw24713step2 i j); unfold raw24713step3 raw24713step2; decide +kernel
      have hl : raw24713step3Labels = raw24713step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24713step3 raw24713step3Labels = mixedMoment B raw24713step4 raw24713step4Labels := by
      have ha : raw24713step4 = raw24713step3 := by apply Matrix.ext; unfold raw24713step4 raw24713step3; decide +kernel
      have hl : raw24713step3Labels = labelEmbedding1 ∘ raw24713step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24713step3 raw24713step3Labels raw24713step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw24714 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24714Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24714step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24714step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24714step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24714step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24714step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24714 raw24714Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw24714 raw24714Labels = mixedMoment B raw24714step0 raw24714step0Labels := by
      have hz : ∀ j, raw24714 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24714step0 = (fun i j => raw24714 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24714step0 raw24714; decide +kernel
      have hl : raw24714step0Labels = raw24714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24714 raw24714Labels permutation265 hz
    mixedMoment B raw24714step0 raw24714step0Labels = mixedMoment B raw24714step1 raw24714step1Labels := by
      have ha : raw24714step1 = (fun i j => raw24714step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24714step1 raw24714step0; decide +kernel
      have hl : raw24714step1Labels = raw24714step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24714step0 raw24714step0Labels permutation34 permutation7
    mixedMoment B raw24714step1 raw24714step1Labels = mixedMoment B raw24714step2 raw24714step2Labels := by
      have ha : raw24714step2 = -raw24714step1 := by apply Matrix.ext; change ∀ i j, raw24714step2 i j = -(raw24714step1 i j); unfold raw24714step2 raw24714step1; decide +kernel
      have hl : raw24714step2Labels = raw24714step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24714step2 raw24714step2Labels = mixedMoment B raw24714step3 raw24714step3Labels := by
      have ha : raw24714step3 = raw24714step2 := by apply Matrix.ext; unfold raw24714step3 raw24714step2; decide +kernel
      have hl : raw24714step2Labels = labelEmbedding1 ∘ raw24714step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24714step2 raw24714step2Labels raw24714step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw24715 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24715Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24715step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw24715step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24715step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24715step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24715step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24715step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24715 raw24715Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw24715 raw24715Labels = mixedMoment B raw24715step0 raw24715step0Labels := by
      have ha : raw24715step0 = (fun i j => raw24715 (permutation220 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24715step0 raw24715; decide +kernel
      have hl : raw24715step0Labels = raw24715Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24715 raw24715Labels permutation220 permutation5
    mixedMoment B raw24715step0 raw24715step0Labels = mixedMoment B raw24715step1 raw24715step1Labels := by
      have ha : raw24715step1 = -raw24715step0 := by apply Matrix.ext; change ∀ i j, raw24715step1 i j = -(raw24715step0 i j); unfold raw24715step1 raw24715step0; decide +kernel
      have hl : raw24715step1Labels = raw24715step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24715step1 raw24715step1Labels = mixedMoment B raw24715step2 raw24715step2Labels := by
      have ha : raw24715step2 = raw24715step1 := by apply Matrix.ext; unfold raw24715step2 raw24715step1; decide +kernel
      have hl : raw24715step1Labels = labelEmbedding1 ∘ raw24715step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24715step1 raw24715step1Labels raw24715step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

def raw24716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24716Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24716step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24716step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24716step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24716 raw24716Labels = mixedMoment B node3256 node3256Labels := by
  calc
    mixedMoment B raw24716 raw24716Labels = mixedMoment B raw24716step0 raw24716step0Labels := by
      have ha : raw24716step0 = (fun i j => raw24716 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24716step0 raw24716; decide +kernel
      have hl : raw24716step0Labels = raw24716Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24716 raw24716Labels permutation178 permutation7
    mixedMoment B raw24716step0 raw24716step0Labels = mixedMoment B raw24716step1 raw24716step1Labels := by
      have ha : raw24716step1 = -raw24716step0 := by apply Matrix.ext; change ∀ i j, raw24716step1 i j = -(raw24716step0 i j); unfold raw24716step1 raw24716step0; decide +kernel
      have hl : raw24716step1Labels = raw24716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24716step1 raw24716step1Labels = mixedMoment B raw24716step2 raw24716step2Labels := by
      have ha : raw24716step2 = raw24716step1 := by apply Matrix.ext; unfold raw24716step2 raw24716step1; decide +kernel
      have hl : raw24716step1Labels = labelEmbedding1 ∘ raw24716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24716step1 raw24716step1Labels raw24716step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3256 node3256Labels := by rfl

def raw24717 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24717Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24717step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24717step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24717step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24717step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24717 raw24717Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw24717 raw24717Labels = mixedMoment B raw24717step0 raw24717step0Labels := by
      have ha : raw24717step0 = (fun i j => raw24717 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24717step0 raw24717; decide +kernel
      have hl : raw24717step0Labels = raw24717Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24717 raw24717Labels permutation178 permutation7
    mixedMoment B raw24717step0 raw24717step0Labels = mixedMoment B raw24717step1 raw24717step1Labels := by
      have ha : raw24717step1 = -raw24717step0 := by apply Matrix.ext; change ∀ i j, raw24717step1 i j = -(raw24717step0 i j); unfold raw24717step1 raw24717step0; decide +kernel
      have hl : raw24717step1Labels = raw24717step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24717step1 raw24717step1Labels = mixedMoment B raw24717step2 raw24717step2Labels := by
      have ha : raw24717step2 = raw24717step1 := by apply Matrix.ext; unfold raw24717step2 raw24717step1; decide +kernel
      have hl : raw24717step1Labels = labelEmbedding1 ∘ raw24717step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24717step1 raw24717step1Labels raw24717step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw24718 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24718Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24718step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24718step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24718step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24718step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24718step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24718step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24718step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24718step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24718 raw24718Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw24718 raw24718Labels = mixedMoment B raw24718step0 raw24718step0Labels := by
      have hz : ∀ j, raw24718 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24718step0 = (fun i j => raw24718 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24718step0 raw24718; decide +kernel
      have hl : raw24718step0Labels = raw24718Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24718 raw24718Labels permutation520 hz
    mixedMoment B raw24718step0 raw24718step0Labels = mixedMoment B raw24718step1 raw24718step1Labels := by
      have ha : raw24718step1 = (fun i j => raw24718step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24718step1 raw24718step0; decide +kernel
      have hl : raw24718step1Labels = raw24718step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24718step0 raw24718step0Labels permutation38 permutation7
    mixedMoment B raw24718step1 raw24718step1Labels = mixedMoment B raw24718step2 raw24718step2Labels := by
      have ha : raw24718step2 = -raw24718step1 := by apply Matrix.ext; change ∀ i j, raw24718step2 i j = -(raw24718step1 i j); unfold raw24718step2 raw24718step1; decide +kernel
      have hl : raw24718step2Labels = raw24718step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24718step2 raw24718step2Labels = mixedMoment B raw24718step3 raw24718step3Labels := by
      have ha : raw24718step3 = raw24718step2 := by apply Matrix.ext; unfold raw24718step3 raw24718step2; decide +kernel
      have hl : raw24718step2Labels = labelEmbedding1 ∘ raw24718step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24718step2 raw24718step2Labels raw24718step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw24719 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24719Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24719step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24719step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24719step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24719step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24719step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24719 raw24719Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw24719 raw24719Labels = mixedMoment B raw24719step0 raw24719step0Labels := by
      have ha : raw24719step0 = (fun i j => raw24719 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24719step0 raw24719; decide +kernel
      have hl : raw24719step0Labels = raw24719Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24719 raw24719Labels permutation178 permutation7
    mixedMoment B raw24719step0 raw24719step0Labels = mixedMoment B raw24719step1 raw24719step1Labels := by
      have ha : raw24719step1 = -raw24719step0 := by apply Matrix.ext; change ∀ i j, raw24719step1 i j = -(raw24719step0 i j); unfold raw24719step1 raw24719step0; decide +kernel
      have hl : raw24719step1Labels = raw24719step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24719step1 raw24719step1Labels = mixedMoment B raw24719step2 raw24719step2Labels := by
      have ha : raw24719step2 = raw24719step1 := by apply Matrix.ext; unfold raw24719step2 raw24719step1; decide +kernel
      have hl : raw24719step1Labels = labelEmbedding1 ∘ raw24719step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24719step1 raw24719step1Labels raw24719step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw24720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24720Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24720step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24720step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24720step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24720step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24720step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24720step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24720 raw24720Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw24720 raw24720Labels = mixedMoment B raw24720step0 raw24720step0Labels := by
      have hz : ∀ j, raw24720 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24720step0 = (fun i j => raw24720 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24720step0 raw24720; decide +kernel
      have hl : raw24720step0Labels = raw24720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24720 raw24720Labels permutation265 hz
    mixedMoment B raw24720step0 raw24720step0Labels = mixedMoment B raw24720step1 raw24720step1Labels := by
      have ha : raw24720step1 = (fun i j => raw24720step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24720step1 raw24720step0; decide +kernel
      have hl : raw24720step1Labels = raw24720step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24720step0 raw24720step0Labels permutation43 permutation5
    mixedMoment B raw24720step1 raw24720step1Labels = mixedMoment B raw24720step2 raw24720step2Labels := by
      have ha : raw24720step2 = -raw24720step1 := by apply Matrix.ext; change ∀ i j, raw24720step2 i j = -(raw24720step1 i j); unfold raw24720step2 raw24720step1; decide +kernel
      have hl : raw24720step2Labels = raw24720step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24720step2 raw24720step2Labels = mixedMoment B raw24720step3 raw24720step3Labels := by
      have ha : raw24720step3 = raw24720step2 := by apply Matrix.ext; unfold raw24720step3 raw24720step2; decide +kernel
      have hl : raw24720step2Labels = labelEmbedding1 ∘ raw24720step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24720step2 raw24720step2Labels raw24720step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

def raw24721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24721Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24721step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24721step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24721step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24721step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24721step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24721step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24721 raw24721Labels = mixedMoment B node3259 node3259Labels := by
  calc
    mixedMoment B raw24721 raw24721Labels = mixedMoment B raw24721step0 raw24721step0Labels := by
      have ha : raw24721step0 = (fun i j => raw24721 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24721step0 raw24721; decide +kernel
      have hl : raw24721step0Labels = raw24721Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24721 raw24721Labels permutation163 permutation5
    mixedMoment B raw24721step0 raw24721step0Labels = mixedMoment B raw24721step1 raw24721step1Labels := by
      have ha : raw24721step1 = -raw24721step0 := by apply Matrix.ext; change ∀ i j, raw24721step1 i j = -(raw24721step0 i j); unfold raw24721step1 raw24721step0; decide +kernel
      have hl : raw24721step1Labels = raw24721step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24721step1 raw24721step1Labels = mixedMoment B raw24721step2 raw24721step2Labels := by
      have ha : raw24721step2 = raw24721step1 := by apply Matrix.ext; unfold raw24721step2 raw24721step1; decide +kernel
      have hl : raw24721step1Labels = labelEmbedding1 ∘ raw24721step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24721step1 raw24721step1Labels raw24721step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3259 node3259Labels := by rfl

def raw24722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24722Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24722step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24722step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24722step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24722step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24722step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24722step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24722step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24722 raw24722Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24722 raw24722Labels = mixedMoment B raw24722step0 raw24722step0Labels := by
      have hz : ∀ j, raw24722 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24722step0 = (fun i j => raw24722 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24722step0 raw24722; decide +kernel
      have hl : raw24722step0Labels = raw24722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24722 raw24722Labels permutation265 hz
    mixedMoment B raw24722step0 raw24722step0Labels = mixedMoment B raw24722step1 raw24722step1Labels := by
      have ha : raw24722step1 = (fun i j => raw24722step0 (permutation43 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24722step1 raw24722step0; decide +kernel
      have hl : raw24722step1Labels = raw24722step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24722step0 raw24722step0Labels permutation43 permutation5
    mixedMoment B raw24722step1 raw24722step1Labels = mixedMoment B raw24722step2 raw24722step2Labels := by
      have ha : raw24722step2 = -raw24722step1 := by apply Matrix.ext; change ∀ i j, raw24722step2 i j = -(raw24722step1 i j); unfold raw24722step2 raw24722step1; decide +kernel
      have hl : raw24722step2Labels = raw24722step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24722step2 raw24722step2Labels = mixedMoment B raw24722step3 raw24722step3Labels := by
      have ha : raw24722step3 = raw24722step2 := by apply Matrix.ext; unfold raw24722step3 raw24722step2; decide +kernel
      have hl : raw24722step2Labels = labelEmbedding1 ∘ raw24722step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24722step2 raw24722step2Labels raw24722step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw24723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24723Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24723step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24723step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24723step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24723step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24723step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24723step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24723 raw24723Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw24723 raw24723Labels = mixedMoment B raw24723step0 raw24723step0Labels := by
      have hz : ∀ j, raw24723 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24723step0 = (fun i j => raw24723 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24723step0 raw24723; decide +kernel
      have hl : raw24723step0Labels = raw24723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24723 raw24723Labels permutation520 hz
    mixedMoment B raw24723step0 raw24723step0Labels = mixedMoment B raw24723step1 raw24723step1Labels := by
      have hz : ∀ j, raw24723step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24723step1 = (fun i j => raw24723step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24723step1 raw24723step0; decide +kernel
      have hl : raw24723step1Labels = raw24723step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24723step0 raw24723step0Labels permutation56 hz
    mixedMoment B raw24723step1 raw24723step1Labels = mixedMoment B raw24723step2 raw24723step2Labels := by
      have ha : raw24723step2 = (fun i j => raw24723step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24723step2 raw24723step1; decide +kernel
      have hl : raw24723step2Labels = raw24723step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24723step1 raw24723step1Labels permutation8 permutation7
    mixedMoment B raw24723step2 raw24723step2Labels = mixedMoment B raw24723step3 raw24723step3Labels := by
      have ha : raw24723step3 = -raw24723step2 := by apply Matrix.ext; change ∀ i j, raw24723step3 i j = -(raw24723step2 i j); unfold raw24723step3 raw24723step2; decide +kernel
      have hl : raw24723step3Labels = raw24723step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24723step3 raw24723step3Labels = mixedMoment B raw24723step4 raw24723step4Labels := by
      have ha : raw24723step4 = raw24723step3 := by apply Matrix.ext; unfold raw24723step4 raw24723step3; decide +kernel
      have hl : raw24723step3Labels = labelEmbedding1 ∘ raw24723step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24723step3 raw24723step3Labels raw24723step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

def raw24724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24724Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24724step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24724step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24724step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24724step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24724step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24724 raw24724Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw24724 raw24724Labels = mixedMoment B raw24724step0 raw24724step0Labels := by
      have hz : ∀ j, raw24724 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24724step0 = (fun i j => raw24724 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24724step0 raw24724; decide +kernel
      have hl : raw24724step0Labels = raw24724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24724 raw24724Labels permutation265 hz
    mixedMoment B raw24724step0 raw24724step0Labels = mixedMoment B raw24724step1 raw24724step1Labels := by
      have ha : raw24724step1 = (fun i j => raw24724step0 (permutation53 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24724step1 raw24724step0; decide +kernel
      have hl : raw24724step1Labels = raw24724step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24724step0 raw24724step0Labels permutation53 permutation5
    mixedMoment B raw24724step1 raw24724step1Labels = mixedMoment B raw24724step2 raw24724step2Labels := by
      have ha : raw24724step2 = -raw24724step1 := by apply Matrix.ext; change ∀ i j, raw24724step2 i j = -(raw24724step1 i j); unfold raw24724step2 raw24724step1; decide +kernel
      have hl : raw24724step2Labels = raw24724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24724step2 raw24724step2Labels = mixedMoment B raw24724step3 raw24724step3Labels := by
      have ha : raw24724step3 = raw24724step2 := by apply Matrix.ext; unfold raw24724step3 raw24724step2; decide +kernel
      have hl : raw24724step2Labels = labelEmbedding1 ∘ raw24724step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24724step2 raw24724step2Labels raw24724step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw24725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24725Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24725step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24725step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24725step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24725step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24725step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24725step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24725step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24725 raw24725Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw24725 raw24725Labels = mixedMoment B raw24725step0 raw24725step0Labels := by
      have hz : ∀ j, raw24725 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24725step0 = (fun i j => raw24725 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24725step0 raw24725; decide +kernel
      have hl : raw24725step0Labels = raw24725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24725 raw24725Labels permutation265 hz
    mixedMoment B raw24725step0 raw24725step0Labels = mixedMoment B raw24725step1 raw24725step1Labels := by
      have ha : raw24725step1 = (fun i j => raw24725step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24725step1 raw24725step0; decide +kernel
      have hl : raw24725step1Labels = raw24725step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24725step0 raw24725step0Labels permutation51 permutation5
    mixedMoment B raw24725step1 raw24725step1Labels = mixedMoment B raw24725step2 raw24725step2Labels := by
      have ha : raw24725step2 = -raw24725step1 := by apply Matrix.ext; change ∀ i j, raw24725step2 i j = -(raw24725step1 i j); unfold raw24725step2 raw24725step1; decide +kernel
      have hl : raw24725step2Labels = raw24725step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24725step2 raw24725step2Labels = mixedMoment B raw24725step3 raw24725step3Labels := by
      have ha : raw24725step3 = raw24725step2 := by apply Matrix.ext; unfold raw24725step3 raw24725step2; decide +kernel
      have hl : raw24725step2Labels = labelEmbedding1 ∘ raw24725step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24725step2 raw24725step2Labels raw24725step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

def raw24726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24726Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24726step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw24726step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24726step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24726step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24726step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24726step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24726 raw24726Labels = mixedMoment B node3267 node3267Labels := by
  calc
    mixedMoment B raw24726 raw24726Labels = mixedMoment B raw24726step0 raw24726step0Labels := by
      have ha : raw24726step0 = (fun i j => raw24726 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24726step0 raw24726; decide +kernel
      have hl : raw24726step0Labels = raw24726Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24726 raw24726Labels permutation171 permutation5
    mixedMoment B raw24726step0 raw24726step0Labels = mixedMoment B raw24726step1 raw24726step1Labels := by
      have ha : raw24726step1 = -raw24726step0 := by apply Matrix.ext; change ∀ i j, raw24726step1 i j = -(raw24726step0 i j); unfold raw24726step1 raw24726step0; decide +kernel
      have hl : raw24726step1Labels = raw24726step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24726step1 raw24726step1Labels = mixedMoment B raw24726step2 raw24726step2Labels := by
      have ha : raw24726step2 = raw24726step1 := by apply Matrix.ext; unfold raw24726step2 raw24726step1; decide +kernel
      have hl : raw24726step1Labels = labelEmbedding1 ∘ raw24726step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24726step1 raw24726step1Labels raw24726step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3267 node3267Labels := by rfl

def raw24727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24727Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24727step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24727step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw24727step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24727step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw24727step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24727step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw24727step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24727 raw24727Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw24727 raw24727Labels = mixedMoment B raw24727step0 raw24727step0Labels := by
      have hz : ∀ j, raw24727 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24727step0 = (fun i j => raw24727 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24727step0 raw24727; decide +kernel
      have hl : raw24727step0Labels = raw24727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24727 raw24727Labels permutation265 hz
    mixedMoment B raw24727step0 raw24727step0Labels = mixedMoment B raw24727step1 raw24727step1Labels := by
      have ha : raw24727step1 = (fun i j => raw24727step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24727step1 raw24727step0; decide +kernel
      have hl : raw24727step1Labels = raw24727step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24727step0 raw24727step0Labels permutation34 permutation7
    mixedMoment B raw24727step1 raw24727step1Labels = mixedMoment B raw24727step2 raw24727step2Labels := by
      have ha : raw24727step2 = -raw24727step1 := by apply Matrix.ext; change ∀ i j, raw24727step2 i j = -(raw24727step1 i j); unfold raw24727step2 raw24727step1; decide +kernel
      have hl : raw24727step2Labels = raw24727step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24727step2 raw24727step2Labels = mixedMoment B raw24727step3 raw24727step3Labels := by
      have ha : raw24727step3 = raw24727step2 := by apply Matrix.ext; unfold raw24727step3 raw24727step2; decide +kernel
      have hl : raw24727step2Labels = labelEmbedding1 ∘ raw24727step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24727step2 raw24727step2Labels raw24727step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

def raw24728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw24728Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24728step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24728step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24728step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24728step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw24728step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24728step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24728step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24728step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24728step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24728 raw24728Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw24728 raw24728Labels = mixedMoment B raw24728step0 raw24728step0Labels := by
      have hz : ∀ j, raw24728 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24728step0 = (fun i j => raw24728 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24728step0 raw24728; decide +kernel
      have hl : raw24728step0Labels = raw24728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24728 raw24728Labels permutation520 hz
    mixedMoment B raw24728step0 raw24728step0Labels = mixedMoment B raw24728step1 raw24728step1Labels := by
      have hz : ∀ j, raw24728step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24728step1 = (fun i j => raw24728step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24728step1 raw24728step0; decide +kernel
      have hl : raw24728step1Labels = raw24728step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24728step0 raw24728step0Labels permutation56 hz
    mixedMoment B raw24728step1 raw24728step1Labels = mixedMoment B raw24728step2 raw24728step2Labels := by
      have ha : raw24728step2 = (fun i j => raw24728step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24728step2 raw24728step1; decide +kernel
      have hl : raw24728step2Labels = raw24728step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24728step1 raw24728step1Labels permutation8 permutation7
    mixedMoment B raw24728step2 raw24728step2Labels = mixedMoment B raw24728step3 raw24728step3Labels := by
      have ha : raw24728step3 = -raw24728step2 := by apply Matrix.ext; change ∀ i j, raw24728step3 i j = -(raw24728step2 i j); unfold raw24728step3 raw24728step2; decide +kernel
      have hl : raw24728step3Labels = raw24728step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24728step3 raw24728step3Labels = mixedMoment B raw24728step4 raw24728step4Labels := by
      have ha : raw24728step4 = raw24728step3 := by apply Matrix.ext; unfold raw24728step4 raw24728step3; decide +kernel
      have hl : raw24728step3Labels = labelEmbedding1 ∘ raw24728step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24728step3 raw24728step3Labels raw24728step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw24729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24729Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw24729step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24729step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24729step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24729step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24729 raw24729Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw24729 raw24729Labels = mixedMoment B raw24729step0 raw24729step0Labels := by
      have hz : ∀ j, raw24729 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24729step0 = (fun i j => raw24729 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24729step0 raw24729; decide +kernel
      have hl : raw24729step0Labels = raw24729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24729 raw24729Labels permutation265 hz
    mixedMoment B raw24729step0 raw24729step0Labels = mixedMoment B raw24729step1 raw24729step1Labels := by
      have ha : raw24729step1 = (fun i j => raw24729step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24729step1 raw24729step0; decide +kernel
      have hl : raw24729step1Labels = raw24729step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24729step0 raw24729step0Labels permutation34 permutation7
    mixedMoment B raw24729step1 raw24729step1Labels = mixedMoment B raw24729step2 raw24729step2Labels := by
      have ha : raw24729step2 = -raw24729step1 := by apply Matrix.ext; change ∀ i j, raw24729step2 i j = -(raw24729step1 i j); unfold raw24729step2 raw24729step1; decide +kernel
      have hl : raw24729step2Labels = raw24729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24729step2 raw24729step2Labels = mixedMoment B raw24729step3 raw24729step3Labels := by
      have ha : raw24729step3 = raw24729step2 := by apply Matrix.ext; unfold raw24729step3 raw24729step2; decide +kernel
      have hl : raw24729step2Labels = labelEmbedding1 ∘ raw24729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24729step2 raw24729step2Labels raw24729step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw24730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24730step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw24730step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24730step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24730step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24730 raw24730Labels = mixedMoment B node1511 node1511Labels := by
  calc
    mixedMoment B raw24730 raw24730Labels = mixedMoment B raw24730step0 raw24730step0Labels := by
      have hz : ∀ j, raw24730 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24730step0 = (fun i j => raw24730 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24730step0 raw24730; decide +kernel
      have hl : raw24730step0Labels = raw24730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24730 raw24730Labels permutation265 hz
    mixedMoment B raw24730step0 raw24730step0Labels = mixedMoment B raw24730step1 raw24730step1Labels := by
      have ha : raw24730step1 = (fun i j => raw24730step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24730step1 raw24730step0; decide +kernel
      have hl : raw24730step1Labels = raw24730step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24730step0 raw24730step0Labels permutation42 permutation5
    mixedMoment B raw24730step1 raw24730step1Labels = mixedMoment B raw24730step2 raw24730step2Labels := by
      have ha : raw24730step2 = -raw24730step1 := by apply Matrix.ext; change ∀ i j, raw24730step2 i j = -(raw24730step1 i j); unfold raw24730step2 raw24730step1; decide +kernel
      have hl : raw24730step2Labels = raw24730step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24730step2 raw24730step2Labels = mixedMoment B raw24730step3 raw24730step3Labels := by
      have ha : raw24730step3 = raw24730step2 := by apply Matrix.ext; unfold raw24730step3 raw24730step2; decide +kernel
      have hl : raw24730step2Labels = labelEmbedding1 ∘ raw24730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24730step2 raw24730step2Labels raw24730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1511 node1511Labels := by rfl

def raw24731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24731step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw24731step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24731step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24731step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24731 raw24731Labels = mixedMoment B node3258 node3258Labels := by
  calc
    mixedMoment B raw24731 raw24731Labels = mixedMoment B raw24731step0 raw24731step0Labels := by
      have ha : raw24731step0 = (fun i j => raw24731 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24731step0 raw24731; decide +kernel
      have hl : raw24731step0Labels = raw24731Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24731 raw24731Labels permutation162 permutation5
    mixedMoment B raw24731step0 raw24731step0Labels = mixedMoment B raw24731step1 raw24731step1Labels := by
      have ha : raw24731step1 = -raw24731step0 := by apply Matrix.ext; change ∀ i j, raw24731step1 i j = -(raw24731step0 i j); unfold raw24731step1 raw24731step0; decide +kernel
      have hl : raw24731step1Labels = raw24731step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24731step1 raw24731step1Labels = mixedMoment B raw24731step2 raw24731step2Labels := by
      have ha : raw24731step2 = raw24731step1 := by apply Matrix.ext; unfold raw24731step2 raw24731step1; decide +kernel
      have hl : raw24731step1Labels = labelEmbedding1 ∘ raw24731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24731step1 raw24731step1Labels raw24731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3258 node3258Labels := by rfl

def raw24732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw24732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw24732step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24732step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw24732step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24732 raw24732Labels = mixedMoment B node3270 node3270Labels := by
  calc
    mixedMoment B raw24732 raw24732Labels = mixedMoment B raw24732step0 raw24732step0Labels := by
      have hz : ∀ j, raw24732 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24732step0 = (fun i j => raw24732 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24732step0 raw24732; decide +kernel
      have hl : raw24732step0Labels = raw24732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24732 raw24732Labels permutation265 hz
    mixedMoment B raw24732step0 raw24732step0Labels = mixedMoment B raw24732step1 raw24732step1Labels := by
      have ha : raw24732step1 = (fun i j => raw24732step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24732step1 raw24732step0; decide +kernel
      have hl : raw24732step1Labels = raw24732step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24732step0 raw24732step0Labels permutation34 permutation7
    mixedMoment B raw24732step1 raw24732step1Labels = mixedMoment B raw24732step2 raw24732step2Labels := by
      have ha : raw24732step2 = -raw24732step1 := by apply Matrix.ext; change ∀ i j, raw24732step2 i j = -(raw24732step1 i j); unfold raw24732step2 raw24732step1; decide +kernel
      have hl : raw24732step2Labels = raw24732step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24732step2 raw24732step2Labels = mixedMoment B raw24732step3 raw24732step3Labels := by
      have ha : raw24732step3 = raw24732step2 := by apply Matrix.ext; unfold raw24732step3 raw24732step2; decide +kernel
      have hl : raw24732step2Labels = labelEmbedding1 ∘ raw24732step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24732step2 raw24732step2Labels raw24732step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3270 node3270Labels := by rfl

def raw24733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24733step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw24733step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24733step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24733step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24733step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24733 raw24733Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw24733 raw24733Labels = mixedMoment B raw24733step0 raw24733step0Labels := by
      have hz : ∀ j, raw24733 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24733step0 = (fun i j => raw24733 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24733step0 raw24733; decide +kernel
      have hl : raw24733step0Labels = raw24733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24733 raw24733Labels permutation265 hz
    mixedMoment B raw24733step0 raw24733step0Labels = mixedMoment B raw24733step1 raw24733step1Labels := by
      have ha : raw24733step1 = (fun i j => raw24733step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24733step1 raw24733step0; decide +kernel
      have hl : raw24733step1Labels = raw24733step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24733step0 raw24733step0Labels permutation42 permutation5
    mixedMoment B raw24733step1 raw24733step1Labels = mixedMoment B raw24733step2 raw24733step2Labels := by
      have ha : raw24733step2 = -raw24733step1 := by apply Matrix.ext; change ∀ i j, raw24733step2 i j = -(raw24733step1 i j); unfold raw24733step2 raw24733step1; decide +kernel
      have hl : raw24733step2Labels = raw24733step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24733step2 raw24733step2Labels = mixedMoment B raw24733step3 raw24733step3Labels := by
      have ha : raw24733step3 = raw24733step2 := by apply Matrix.ext; unfold raw24733step3 raw24733step2; decide +kernel
      have hl : raw24733step2Labels = labelEmbedding1 ∘ raw24733step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24733step2 raw24733step2Labels raw24733step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

def raw24734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw24734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24734step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24734step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24734step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24734step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24734step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24734step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24734 raw24734Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24734 raw24734Labels = mixedMoment B raw24734step0 raw24734step0Labels := by
      have hz : ∀ j, raw24734 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24734step0 = (fun i j => raw24734 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24734step0 raw24734; decide +kernel
      have hl : raw24734step0Labels = raw24734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24734 raw24734Labels permutation265 hz
    mixedMoment B raw24734step0 raw24734step0Labels = mixedMoment B raw24734step1 raw24734step1Labels := by
      have ha : raw24734step1 = (fun i j => raw24734step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24734step1 raw24734step0; decide +kernel
      have hl : raw24734step1Labels = raw24734step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24734step0 raw24734step0Labels permutation34 permutation7
    mixedMoment B raw24734step1 raw24734step1Labels = mixedMoment B raw24734step2 raw24734step2Labels := by
      have ha : raw24734step2 = -raw24734step1 := by apply Matrix.ext; change ∀ i j, raw24734step2 i j = -(raw24734step1 i j); unfold raw24734step2 raw24734step1; decide +kernel
      have hl : raw24734step2Labels = raw24734step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24734step2 raw24734step2Labels = mixedMoment B raw24734step3 raw24734step3Labels := by
      have ha : raw24734step3 = raw24734step2 := by apply Matrix.ext; unfold raw24734step3 raw24734step2; decide +kernel
      have hl : raw24734step2Labels = labelEmbedding1 ∘ raw24734step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24734step2 raw24734step2Labels raw24734step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw24735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24735step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw24735step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24735step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24735step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24735step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24735 raw24735Labels = mixedMoment B node1514 node1514Labels := by
  calc
    mixedMoment B raw24735 raw24735Labels = mixedMoment B raw24735step0 raw24735step0Labels := by
      have hz : ∀ j, raw24735 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24735step0 = (fun i j => raw24735 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24735step0 raw24735; decide +kernel
      have hl : raw24735step0Labels = raw24735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24735 raw24735Labels permutation265 hz
    mixedMoment B raw24735step0 raw24735step0Labels = mixedMoment B raw24735step1 raw24735step1Labels := by
      have ha : raw24735step1 = (fun i j => raw24735step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24735step1 raw24735step0; decide +kernel
      have hl : raw24735step1Labels = raw24735step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24735step0 raw24735step0Labels permutation38 permutation5
    mixedMoment B raw24735step1 raw24735step1Labels = mixedMoment B raw24735step2 raw24735step2Labels := by
      have ha : raw24735step2 = -raw24735step1 := by apply Matrix.ext; change ∀ i j, raw24735step2 i j = -(raw24735step1 i j); unfold raw24735step2 raw24735step1; decide +kernel
      have hl : raw24735step2Labels = raw24735step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24735step2 raw24735step2Labels = mixedMoment B raw24735step3 raw24735step3Labels := by
      have ha : raw24735step3 = raw24735step2 := by apply Matrix.ext; unfold raw24735step3 raw24735step2; decide +kernel
      have hl : raw24735step2Labels = labelEmbedding1 ∘ raw24735step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24735step2 raw24735step2Labels raw24735step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1514 node1514Labels := by rfl

def raw24736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24736step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw24736step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24736step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24736step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw24736step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24736 raw24736Labels = mixedMoment B node3260 node3260Labels := by
  calc
    mixedMoment B raw24736 raw24736Labels = mixedMoment B raw24736step0 raw24736step0Labels := by
      have ha : raw24736step0 = (fun i j => raw24736 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24736step0 raw24736; decide +kernel
      have hl : raw24736step0Labels = raw24736Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24736 raw24736Labels permutation158 permutation5
    mixedMoment B raw24736step0 raw24736step0Labels = mixedMoment B raw24736step1 raw24736step1Labels := by
      have ha : raw24736step1 = -raw24736step0 := by apply Matrix.ext; change ∀ i j, raw24736step1 i j = -(raw24736step0 i j); unfold raw24736step1 raw24736step0; decide +kernel
      have hl : raw24736step1Labels = raw24736step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24736step1 raw24736step1Labels = mixedMoment B raw24736step2 raw24736step2Labels := by
      have ha : raw24736step2 = raw24736step1 := by apply Matrix.ext; unfold raw24736step2 raw24736step1; decide +kernel
      have hl : raw24736step1Labels = labelEmbedding1 ∘ raw24736step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24736step1 raw24736step1Labels raw24736step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3260 node3260Labels := by rfl

def raw24737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw24737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw24737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw24737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24737 raw24737Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw24737 raw24737Labels = mixedMoment B raw24737step0 raw24737step0Labels := by
      have hz : ∀ j, raw24737 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24737step0 = (fun i j => raw24737 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24737step0 raw24737; decide +kernel
      have hl : raw24737step0Labels = raw24737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24737 raw24737Labels permutation265 hz
    mixedMoment B raw24737step0 raw24737step0Labels = mixedMoment B raw24737step1 raw24737step1Labels := by
      have ha : raw24737step1 = (fun i j => raw24737step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24737step1 raw24737step0; decide +kernel
      have hl : raw24737step1Labels = raw24737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24737step0 raw24737step0Labels permutation34 permutation7
    mixedMoment B raw24737step1 raw24737step1Labels = mixedMoment B raw24737step2 raw24737step2Labels := by
      have ha : raw24737step2 = -raw24737step1 := by apply Matrix.ext; change ∀ i j, raw24737step2 i j = -(raw24737step1 i j); unfold raw24737step2 raw24737step1; decide +kernel
      have hl : raw24737step2Labels = raw24737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24737step2 raw24737step2Labels = mixedMoment B raw24737step3 raw24737step3Labels := by
      have ha : raw24737step3 = raw24737step2 := by apply Matrix.ext; unfold raw24737step3 raw24737step2; decide +kernel
      have hl : raw24737step2Labels = labelEmbedding1 ∘ raw24737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24737step2 raw24737step2Labels raw24737step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

def raw24738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24738step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw24738step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24738step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24738step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw24738step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24738 raw24738Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw24738 raw24738Labels = mixedMoment B raw24738step0 raw24738step0Labels := by
      have hz : ∀ j, raw24738 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24738step0 = (fun i j => raw24738 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24738step0 raw24738; decide +kernel
      have hl : raw24738step0Labels = raw24738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24738 raw24738Labels permutation265 hz
    mixedMoment B raw24738step0 raw24738step0Labels = mixedMoment B raw24738step1 raw24738step1Labels := by
      have ha : raw24738step1 = (fun i j => raw24738step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24738step1 raw24738step0; decide +kernel
      have hl : raw24738step1Labels = raw24738step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24738step0 raw24738step0Labels permutation34 permutation7
    mixedMoment B raw24738step1 raw24738step1Labels = mixedMoment B raw24738step2 raw24738step2Labels := by
      have ha : raw24738step2 = -raw24738step1 := by apply Matrix.ext; change ∀ i j, raw24738step2 i j = -(raw24738step1 i j); unfold raw24738step2 raw24738step1; decide +kernel
      have hl : raw24738step2Labels = raw24738step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24738step2 raw24738step2Labels = mixedMoment B raw24738step3 raw24738step3Labels := by
      have ha : raw24738step3 = raw24738step2 := by apply Matrix.ext; unfold raw24738step3 raw24738step2; decide +kernel
      have hl : raw24738step2Labels = labelEmbedding1 ∘ raw24738step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24738step2 raw24738step2Labels raw24738step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw24739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw24739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24739step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24739step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24739step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw24739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24739step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24739step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24739step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24739step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24739 raw24739Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw24739 raw24739Labels = mixedMoment B raw24739step0 raw24739step0Labels := by
      have hz : ∀ j, raw24739 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24739step0 = (fun i j => raw24739 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24739step0 raw24739; decide +kernel
      have hl : raw24739step0Labels = raw24739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24739 raw24739Labels permutation520 hz
    mixedMoment B raw24739step0 raw24739step0Labels = mixedMoment B raw24739step1 raw24739step1Labels := by
      have hz : ∀ j, raw24739step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24739step1 = (fun i j => raw24739step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24739step1 raw24739step0; decide +kernel
      have hl : raw24739step1Labels = raw24739step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24739step0 raw24739step0Labels permutation56 hz
    mixedMoment B raw24739step1 raw24739step1Labels = mixedMoment B raw24739step2 raw24739step2Labels := by
      have ha : raw24739step2 = (fun i j => raw24739step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24739step2 raw24739step1; decide +kernel
      have hl : raw24739step2Labels = raw24739step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24739step1 raw24739step1Labels permutation8 permutation7
    mixedMoment B raw24739step2 raw24739step2Labels = mixedMoment B raw24739step3 raw24739step3Labels := by
      have ha : raw24739step3 = -raw24739step2 := by apply Matrix.ext; change ∀ i j, raw24739step3 i j = -(raw24739step2 i j); unfold raw24739step3 raw24739step2; decide +kernel
      have hl : raw24739step3Labels = raw24739step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24739step3 raw24739step3Labels = mixedMoment B raw24739step4 raw24739step4Labels := by
      have ha : raw24739step4 = raw24739step3 := by apply Matrix.ext; unfold raw24739step4 raw24739step3; decide +kernel
      have hl : raw24739step3Labels = labelEmbedding1 ∘ raw24739step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24739step3 raw24739step3Labels raw24739step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw24740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24740Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24740step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24740step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24740 raw24740Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24740 raw24740Labels = mixedMoment B raw24740step0 raw24740step0Labels := by
      have hz : ∀ j, raw24740 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24740step0 = (fun i j => raw24740 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24740step0 raw24740; decide +kernel
      have hl : raw24740step0Labels = raw24740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24740 raw24740Labels permutation265 hz
    mixedMoment B raw24740step0 raw24740step0Labels = mixedMoment B raw24740step1 raw24740step1Labels := by
      have ha : raw24740step1 = (fun i j => raw24740step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24740step1 raw24740step0; decide +kernel
      have hl : raw24740step1Labels = raw24740step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24740step0 raw24740step0Labels permutation34 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24741Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24741step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24741 raw24741Labels = mixedMoment B node623 node623Labels := by
  calc
    mixedMoment B raw24741 raw24741Labels = mixedMoment B raw24741step0 raw24741step0Labels := by
      have ha : raw24741step0 = (fun i j => raw24741 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24741step0 raw24741; decide +kernel
      have hl : raw24741step0Labels = raw24741Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24741 raw24741Labels permutation178 permutation2
    _ = mixedMoment B node623 node623Labels := by rfl

def raw24742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24742Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24742step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24742step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24742 raw24742Labels = mixedMoment B node638 node638Labels := by
  calc
    mixedMoment B raw24742 raw24742Labels = mixedMoment B raw24742step0 raw24742step0Labels := by
      have hz : ∀ j, raw24742 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24742step0 = (fun i j => raw24742 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24742step0 raw24742; decide +kernel
      have hl : raw24742step0Labels = raw24742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24742 raw24742Labels permutation265 hz
    mixedMoment B raw24742step0 raw24742step0Labels = mixedMoment B raw24742step1 raw24742step1Labels := by
      have ha : raw24742step1 = (fun i j => raw24742step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24742step1 raw24742step0; decide +kernel
      have hl : raw24742step1Labels = raw24742step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24742step0 raw24742step0Labels permutation34 permutation2
    _ = mixedMoment B node638 node638Labels := by rfl

def raw24743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24743Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24743step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24743step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24743 raw24743Labels = mixedMoment B node627 node627Labels := by
  calc
    mixedMoment B raw24743 raw24743Labels = mixedMoment B raw24743step0 raw24743step0Labels := by
      have hz : ∀ j, raw24743 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24743step0 = (fun i j => raw24743 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24743step0 raw24743; decide +kernel
      have hl : raw24743step0Labels = raw24743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24743 raw24743Labels permutation265 hz
    mixedMoment B raw24743step0 raw24743step0Labels = mixedMoment B raw24743step1 raw24743step1Labels := by
      have ha : raw24743step1 = (fun i j => raw24743step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24743step1 raw24743step0; decide +kernel
      have hl : raw24743step1Labels = raw24743step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24743step0 raw24743step0Labels permutation34 permutation2
    _ = mixedMoment B node627 node627Labels := by rfl

def raw24744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24744Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24744step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24744 raw24744Labels = mixedMoment B node631 node631Labels := by
  calc
    mixedMoment B raw24744 raw24744Labels = mixedMoment B raw24744step0 raw24744step0Labels := by
      have hz : ∀ j, raw24744 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24744step0 = (fun i j => raw24744 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24744step0 raw24744; decide +kernel
      have hl : raw24744step0Labels = raw24744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24744 raw24744Labels permutation265 hz
    _ = mixedMoment B node631 node631Labels := by rfl

def raw24745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24745Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24745step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw24745step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24745 raw24745Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw24745 raw24745Labels = mixedMoment B raw24745step0 raw24745step0Labels := by
      have hz : ∀ j, raw24745 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24745step0 = (fun i j => raw24745 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24745step0 raw24745; decide +kernel
      have hl : raw24745step0Labels = raw24745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24745 raw24745Labels permutation265 hz
    mixedMoment B raw24745step0 raw24745step0Labels = mixedMoment B raw24745step1 raw24745step1Labels := by
      have ha : raw24745step1 = (fun i j => raw24745step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24745step1 raw24745step0; decide +kernel
      have hl : raw24745step1Labels = raw24745step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24745step0 raw24745step0Labels permutation34 permutation2
    _ = mixedMoment B node626 node626Labels := by rfl

def raw24746 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![2, -2]]
def raw24746Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24746step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw24746step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24746step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw24746step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24746 raw24746Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw24746 raw24746Labels = mixedMoment B raw24746step0 raw24746step0Labels := by
      have hz : ∀ j, raw24746 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24746step0 = (fun i j => raw24746 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24746step0 raw24746; decide +kernel
      have hl : raw24746step0Labels = raw24746Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24746 raw24746Labels permutation520 hz
    mixedMoment B raw24746step0 raw24746step0Labels = mixedMoment B raw24746step1 raw24746step1Labels := by
      have hz : ∀ j, raw24746step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24746step1 = (fun i j => raw24746step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24746step1 raw24746step0; decide +kernel
      have hl : raw24746step1Labels = raw24746step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24746step0 raw24746step0Labels permutation56 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw24747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24747Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24747step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24747step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24747 raw24747Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw24747 raw24747Labels = mixedMoment B raw24747step0 raw24747step0Labels := by
      have ha : raw24747step0 = (fun i j => raw24747 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24747step0 raw24747; decide +kernel
      have hl : raw24747step0Labels = raw24747Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24747 raw24747Labels permutation154 permutation2
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw24748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24748Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24748step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24748step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24748 raw24748Labels = mixedMoment B node1156 node1156Labels := by
  calc
    mixedMoment B raw24748 raw24748Labels = mixedMoment B raw24748step0 raw24748step0Labels := by
      have ha : raw24748step0 = (fun i j => raw24748 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24748step0 raw24748; decide +kernel
      have hl : raw24748step0Labels = raw24748Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24748 raw24748Labels permutation154 permutation2
    _ = mixedMoment B node1156 node1156Labels := by rfl

def raw24749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24749Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24749step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw24749step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24749 raw24749Labels = mixedMoment B node1149 node1149Labels := by
  calc
    mixedMoment B raw24749 raw24749Labels = mixedMoment B raw24749step0 raw24749step0Labels := by
      have ha : raw24749step0 = (fun i j => raw24749 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24749step0 raw24749; decide +kernel
      have hl : raw24749step0Labels = raw24749Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24749 raw24749Labels permutation154 permutation2
    _ = mixedMoment B node1149 node1149Labels := by rfl

def raw24750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw24750Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24750 raw24750Labels = mixedMoment B node1151 node1151Labels := by
  calc
    _ = mixedMoment B node1151 node1151Labels := by rfl

def raw24751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw24751Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24751step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw24751step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24751 raw24751Labels = mixedMoment B node1148 node1148Labels := by
  calc
    mixedMoment B raw24751 raw24751Labels = mixedMoment B raw24751step0 raw24751step0Labels := by
      have ha : raw24751step0 = (fun i j => raw24751 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24751step0 raw24751; decide +kernel
      have hl : raw24751step0Labels = raw24751Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24751 raw24751Labels permutation154 permutation2
    _ = mixedMoment B node1148 node1148Labels := by rfl

def raw24752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24752Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24752 raw24752Labels = mixedMoment B node5149 node5149Labels := by
  calc
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw24753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24753Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24753step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24753 raw24753Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw24753 raw24753Labels = mixedMoment B raw24753step0 raw24753step0Labels := by
      have hz : ∀ j, raw24753 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24753step0 = (fun i j => raw24753 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24753step0 raw24753; decide +kernel
      have hl : raw24753step0Labels = raw24753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24753 raw24753Labels permutation265 hz
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw24754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24754Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24754step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24754step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24754 raw24754Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw24754 raw24754Labels = mixedMoment B raw24754step0 raw24754step0Labels := by
      have hz : ∀ j, raw24754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24754step0 = (fun i j => raw24754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24754step0 raw24754; decide +kernel
      have hl : raw24754step0Labels = raw24754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24754 raw24754Labels permutation434 hz
    mixedMoment B raw24754step0 raw24754step0Labels = mixedMoment B raw24754step1 raw24754step1Labels := by
      have hz : ∀ j, raw24754step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24754step1 = (fun i j => raw24754step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24754step1 raw24754step0; decide +kernel
      have hl : raw24754step1Labels = raw24754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24754step0 raw24754step0Labels permutation56 hz
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw24755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24755Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24755step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24755step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw24755step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24755 raw24755Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw24755 raw24755Labels = mixedMoment B raw24755step0 raw24755step0Labels := by
      have hz : ∀ j, raw24755 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24755step0 = (fun i j => raw24755 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24755step0 raw24755; decide +kernel
      have hl : raw24755step0Labels = raw24755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24755 raw24755Labels permutation265 hz
    mixedMoment B raw24755step0 raw24755step0Labels = mixedMoment B raw24755step1 raw24755step1Labels := by
      have ha : raw24755step1 = (fun i j => raw24755step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24755step1 raw24755step0; decide +kernel
      have hl : raw24755step1Labels = raw24755step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24755step0 raw24755step0Labels permutation34 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw24756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24756Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24756step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw24756step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24756 raw24756Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw24756 raw24756Labels = mixedMoment B raw24756step0 raw24756step0Labels := by
      have hz : ∀ j, raw24756 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24756step0 = (fun i j => raw24756 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24756step0 raw24756; decide +kernel
      have hl : raw24756step0Labels = raw24756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24756 raw24756Labels permutation265 hz
    mixedMoment B raw24756step0 raw24756step0Labels = mixedMoment B raw24756step1 raw24756step1Labels := by
      have ha : raw24756step1 = (fun i j => raw24756step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24756step1 raw24756step0; decide +kernel
      have hl : raw24756step1Labels = raw24756step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24756step0 raw24756step0Labels permutation33 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw24757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24757Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24757step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24757step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24757step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24757step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24757 raw24757Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw24757 raw24757Labels = mixedMoment B raw24757step0 raw24757step0Labels := by
      have ha : raw24757step0 = (fun i j => raw24757 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24757step0 raw24757; decide +kernel
      have hl : raw24757step0Labels = raw24757Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24757 raw24757Labels permutation188 permutation3
    mixedMoment B raw24757step0 raw24757step0Labels = mixedMoment B raw24757step1 raw24757step1Labels := by
      have ha : raw24757step1 = raw24757step0 := by apply Matrix.ext; unfold raw24757step1 raw24757step0; decide +kernel
      have hl : raw24757step0Labels = labelEmbedding6 ∘ raw24757step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24757step0 raw24757step0Labels raw24757step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4139 node4139Labels := by rfl

def raw24758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24758Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24758step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24758step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24758step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24758step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24758 raw24758Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw24758 raw24758Labels = mixedMoment B raw24758step0 raw24758step0Labels := by
      have ha : raw24758step0 = (fun i j => raw24758 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24758step0 raw24758; decide +kernel
      have hl : raw24758step0Labels = raw24758Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24758 raw24758Labels permutation188 permutation3
    mixedMoment B raw24758step0 raw24758step0Labels = mixedMoment B raw24758step1 raw24758step1Labels := by
      have ha : raw24758step1 = raw24758step0 := by apply Matrix.ext; unfold raw24758step1 raw24758step0; decide +kernel
      have hl : raw24758step0Labels = labelEmbedding6 ∘ raw24758step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24758step0 raw24758step0Labels raw24758step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

def raw24759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24759Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24759step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24759step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24759step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24759step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24759 raw24759Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24759 raw24759Labels = mixedMoment B raw24759step0 raw24759step0Labels := by
      have hz : ∀ j, raw24759 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24759step0 = (fun i j => raw24759 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24759step0 raw24759; decide +kernel
      have hl : raw24759step0Labels = raw24759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24759 raw24759Labels permutation434 hz
    mixedMoment B raw24759step0 raw24759step0Labels = mixedMoment B raw24759step1 raw24759step1Labels := by
      have ha : raw24759step1 = (fun i j => raw24759step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24759step1 raw24759step0; decide +kernel
      have hl : raw24759step1Labels = raw24759step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24759step0 raw24759step0Labels permutation40 permutation3
    mixedMoment B raw24759step1 raw24759step1Labels = mixedMoment B raw24759step2 raw24759step2Labels := by
      have ha : raw24759step2 = raw24759step1 := by apply Matrix.ext; unfold raw24759step2 raw24759step1; decide +kernel
      have hl : raw24759step1Labels = labelEmbedding6 ∘ raw24759step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24759step1 raw24759step1Labels raw24759step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24760Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24760step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24760step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24760step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24760 raw24760Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw24760 raw24760Labels = mixedMoment B raw24760step0 raw24760step0Labels := by
      have ha : raw24760step0 = (fun i j => raw24760 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24760step0 raw24760; decide +kernel
      have hl : raw24760step0Labels = raw24760Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24760 raw24760Labels permutation188 permutation3
    mixedMoment B raw24760step0 raw24760step0Labels = mixedMoment B raw24760step1 raw24760step1Labels := by
      have ha : raw24760step1 = raw24760step0 := by apply Matrix.ext; unfold raw24760step1 raw24760step0; decide +kernel
      have hl : raw24760step0Labels = labelEmbedding6 ∘ raw24760step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24760step0 raw24760step0Labels raw24760step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

def raw24761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24761Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24761step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24761step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24761step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24761step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24761 raw24761Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw24761 raw24761Labels = mixedMoment B raw24761step0 raw24761step0Labels := by
      have ha : raw24761step0 = (fun i j => raw24761 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24761step0 raw24761; decide +kernel
      have hl : raw24761step0Labels = raw24761Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24761 raw24761Labels permutation188 permutation3
    mixedMoment B raw24761step0 raw24761step0Labels = mixedMoment B raw24761step1 raw24761step1Labels := by
      have ha : raw24761step1 = raw24761step0 := by apply Matrix.ext; unfold raw24761step1 raw24761step0; decide +kernel
      have hl : raw24761step0Labels = labelEmbedding6 ∘ raw24761step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24761step0 raw24761step0Labels raw24761step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw24762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24762Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24762step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24762step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24762step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24762 raw24762Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw24762 raw24762Labels = mixedMoment B raw24762step0 raw24762step0Labels := by
      have hz : ∀ j, raw24762 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24762step0 = (fun i j => raw24762 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24762step0 raw24762; decide +kernel
      have hl : raw24762step0Labels = raw24762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24762 raw24762Labels permutation265 hz
    mixedMoment B raw24762step0 raw24762step0Labels = mixedMoment B raw24762step1 raw24762step1Labels := by
      have ha : raw24762step1 = (fun i j => raw24762step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24762step1 raw24762step0; decide +kernel
      have hl : raw24762step1Labels = raw24762step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24762step0 raw24762step0Labels permutation34 permutation3
    mixedMoment B raw24762step1 raw24762step1Labels = mixedMoment B raw24762step2 raw24762step2Labels := by
      have ha : raw24762step2 = raw24762step1 := by apply Matrix.ext; unfold raw24762step2 raw24762step1; decide +kernel
      have hl : raw24762step1Labels = labelEmbedding6 ∘ raw24762step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24762step1 raw24762step1Labels raw24762step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4172 node4172Labels := by rfl

def raw24763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24763Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24763step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24763step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24763step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24763step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24763 raw24763Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw24763 raw24763Labels = mixedMoment B raw24763step0 raw24763step0Labels := by
      have ha : raw24763step0 = (fun i j => raw24763 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24763step0 raw24763; decide +kernel
      have hl : raw24763step0Labels = raw24763Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24763 raw24763Labels permutation154 permutation3
    mixedMoment B raw24763step0 raw24763step0Labels = mixedMoment B raw24763step1 raw24763step1Labels := by
      have ha : raw24763step1 = raw24763step0 := by apply Matrix.ext; unfold raw24763step1 raw24763step0; decide +kernel
      have hl : raw24763step0Labels = labelEmbedding6 ∘ raw24763step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24763step0 raw24763step0Labels raw24763step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4541 node4541Labels := by rfl

def raw24764 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24764Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24764step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24764step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24764step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24764step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24764step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24764step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24764step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24764step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24764 raw24764Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw24764 raw24764Labels = mixedMoment B raw24764step0 raw24764step0Labels := by
      have hz : ∀ j, raw24764 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24764step0 = (fun i j => raw24764 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24764step0 raw24764; decide +kernel
      have hl : raw24764step0Labels = raw24764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24764 raw24764Labels permutation434 hz
    mixedMoment B raw24764step0 raw24764step0Labels = mixedMoment B raw24764step1 raw24764step1Labels := by
      have hz : ∀ j, raw24764step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24764step1 = (fun i j => raw24764step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24764step1 raw24764step0; decide +kernel
      have hl : raw24764step1Labels = raw24764step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24764step0 raw24764step0Labels permutation56 hz
    mixedMoment B raw24764step1 raw24764step1Labels = mixedMoment B raw24764step2 raw24764step2Labels := by
      have ha : raw24764step2 = (fun i j => raw24764step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24764step2 raw24764step1; decide +kernel
      have hl : raw24764step2Labels = raw24764step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24764step1 raw24764step1Labels permutation8 permutation3
    mixedMoment B raw24764step2 raw24764step2Labels = mixedMoment B raw24764step3 raw24764step3Labels := by
      have ha : raw24764step3 = raw24764step2 := by apply Matrix.ext; unfold raw24764step3 raw24764step2; decide +kernel
      have hl : raw24764step2Labels = labelEmbedding6 ∘ raw24764step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24764step2 raw24764step2Labels raw24764step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw24765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24765step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24765step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24765 raw24765Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24765 raw24765Labels = mixedMoment B raw24765step0 raw24765step0Labels := by
      have hz : ∀ j, raw24765 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24765step0 = (fun i j => raw24765 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24765step0 raw24765; decide +kernel
      have hl : raw24765step0Labels = raw24765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24765 raw24765Labels permutation265 hz
    mixedMoment B raw24765step0 raw24765step0Labels = mixedMoment B raw24765step1 raw24765step1Labels := by
      have ha : raw24765step1 = (fun i j => raw24765step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24765step1 raw24765step0; decide +kernel
      have hl : raw24765step1Labels = raw24765step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24765step0 raw24765step0Labels permutation44 permutation3
    mixedMoment B raw24765step1 raw24765step1Labels = mixedMoment B raw24765step2 raw24765step2Labels := by
      have ha : raw24765step2 = raw24765step1 := by apply Matrix.ext; unfold raw24765step2 raw24765step1; decide +kernel
      have hl : raw24765step1Labels = labelEmbedding6 ∘ raw24765step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24765step1 raw24765step1Labels raw24765step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24766step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24766step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24766 raw24766Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw24766 raw24766Labels = mixedMoment B raw24766step0 raw24766step0Labels := by
      have hz : ∀ j, raw24766 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24766step0 = (fun i j => raw24766 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24766step0 raw24766; decide +kernel
      have hl : raw24766step0Labels = raw24766Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24766 raw24766Labels permutation265 hz
    mixedMoment B raw24766step0 raw24766step0Labels = mixedMoment B raw24766step1 raw24766step1Labels := by
      have ha : raw24766step1 = (fun i j => raw24766step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24766step1 raw24766step0; decide +kernel
      have hl : raw24766step1Labels = raw24766step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24766step0 raw24766step0Labels permutation42 permutation2
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw24767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24767step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24767step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24767step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24767step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24767 raw24767Labels = mixedMoment B node4141 node4141Labels := by
  calc
    mixedMoment B raw24767 raw24767Labels = mixedMoment B raw24767step0 raw24767step0Labels := by
      have hz : ∀ j, raw24767 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24767step0 = (fun i j => raw24767 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24767step0 raw24767; decide +kernel
      have hl : raw24767step0Labels = raw24767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24767 raw24767Labels permutation265 hz
    mixedMoment B raw24767step0 raw24767step0Labels = mixedMoment B raw24767step1 raw24767step1Labels := by
      have ha : raw24767step1 = (fun i j => raw24767step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24767step1 raw24767step0; decide +kernel
      have hl : raw24767step1Labels = raw24767step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24767step0 raw24767step0Labels permutation34 permutation3
    mixedMoment B raw24767step1 raw24767step1Labels = mixedMoment B raw24767step2 raw24767step2Labels := by
      have ha : raw24767step2 = raw24767step1 := by apply Matrix.ext; unfold raw24767step2 raw24767step1; decide +kernel
      have hl : raw24767step1Labels = labelEmbedding6 ∘ raw24767step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24767step1 raw24767step1Labels raw24767step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4141 node4141Labels := by rfl

def raw24768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24768step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24768step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24768step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24768step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24768 raw24768Labels = mixedMoment B node4522 node4522Labels := by
  calc
    mixedMoment B raw24768 raw24768Labels = mixedMoment B raw24768step0 raw24768step0Labels := by
      have ha : raw24768step0 = (fun i j => raw24768 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24768step0 raw24768; decide +kernel
      have hl : raw24768step0Labels = raw24768Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24768 raw24768Labels permutation154 permutation3
    mixedMoment B raw24768step0 raw24768step0Labels = mixedMoment B raw24768step1 raw24768step1Labels := by
      have ha : raw24768step1 = raw24768step0 := by apply Matrix.ext; unfold raw24768step1 raw24768step0; decide +kernel
      have hl : raw24768step0Labels = labelEmbedding6 ∘ raw24768step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24768step0 raw24768step0Labels raw24768step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4522 node4522Labels := by rfl

def raw24769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24769step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24769 raw24769Labels = mixedMoment B node4515 node4515Labels := by
  calc
    mixedMoment B raw24769 raw24769Labels = mixedMoment B raw24769step0 raw24769step0Labels := by
      have hz : ∀ j, raw24769 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24769step0 = (fun i j => raw24769 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24769step0 raw24769; decide +kernel
      have hl : raw24769step0Labels = raw24769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24769 raw24769Labels permutation265 hz
    mixedMoment B raw24769step0 raw24769step0Labels = mixedMoment B raw24769step1 raw24769step1Labels := by
      have ha : raw24769step1 = (fun i j => raw24769step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24769step1 raw24769step0; decide +kernel
      have hl : raw24769step1Labels = raw24769step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24769step0 raw24769step0Labels permutation34 permutation3
    mixedMoment B raw24769step1 raw24769step1Labels = mixedMoment B raw24769step2 raw24769step2Labels := by
      have ha : raw24769step2 = raw24769step1 := by apply Matrix.ext; unfold raw24769step2 raw24769step1; decide +kernel
      have hl : raw24769step1Labels = labelEmbedding6 ∘ raw24769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24769step1 raw24769step1Labels raw24769step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4515 node4515Labels := by rfl

def raw24770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24770step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24770step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24770 raw24770Labels = mixedMoment B node4586 node4586Labels := by
  calc
    mixedMoment B raw24770 raw24770Labels = mixedMoment B raw24770step0 raw24770step0Labels := by
      have hz : ∀ j, raw24770 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24770step0 = (fun i j => raw24770 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24770step0 raw24770; decide +kernel
      have hl : raw24770step0Labels = raw24770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24770 raw24770Labels permutation265 hz
    mixedMoment B raw24770step0 raw24770step0Labels = mixedMoment B raw24770step1 raw24770step1Labels := by
      have ha : raw24770step1 = (fun i j => raw24770step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24770step1 raw24770step0; decide +kernel
      have hl : raw24770step1Labels = raw24770step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24770step0 raw24770step0Labels permutation34 permutation3
    mixedMoment B raw24770step1 raw24770step1Labels = mixedMoment B raw24770step2 raw24770step2Labels := by
      have ha : raw24770step2 = raw24770step1 := by apply Matrix.ext; unfold raw24770step2 raw24770step1; decide +kernel
      have hl : raw24770step1Labels = labelEmbedding6 ∘ raw24770step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24770step1 raw24770step1Labels raw24770step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4586 node4586Labels := by rfl

def raw24771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24771step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24771step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24771step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24771step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24771 raw24771Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw24771 raw24771Labels = mixedMoment B raw24771step0 raw24771step0Labels := by
      have hz : ∀ j, raw24771 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24771step0 = (fun i j => raw24771 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24771step0 raw24771; decide +kernel
      have hl : raw24771step0Labels = raw24771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24771 raw24771Labels permutation265 hz
    mixedMoment B raw24771step0 raw24771step0Labels = mixedMoment B raw24771step1 raw24771step1Labels := by
      have ha : raw24771step1 = (fun i j => raw24771step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24771step1 raw24771step0; decide +kernel
      have hl : raw24771step1Labels = raw24771step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24771step0 raw24771step0Labels permutation35 permutation3
    mixedMoment B raw24771step1 raw24771step1Labels = mixedMoment B raw24771step2 raw24771step2Labels := by
      have ha : raw24771step2 = raw24771step1 := by apply Matrix.ext; unfold raw24771step2 raw24771step1; decide +kernel
      have hl : raw24771step1Labels = labelEmbedding6 ∘ raw24771step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24771step1 raw24771step1Labels raw24771step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw24772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24772step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24772step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24772step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24772 raw24772Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw24772 raw24772Labels = mixedMoment B raw24772step0 raw24772step0Labels := by
      have hz : ∀ j, raw24772 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24772step0 = (fun i j => raw24772 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24772step0 raw24772; decide +kernel
      have hl : raw24772step0Labels = raw24772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24772 raw24772Labels permutation265 hz
    mixedMoment B raw24772step0 raw24772step0Labels = mixedMoment B raw24772step1 raw24772step1Labels := by
      have ha : raw24772step1 = (fun i j => raw24772step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24772step1 raw24772step0; decide +kernel
      have hl : raw24772step1Labels = raw24772step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24772step0 raw24772step0Labels permutation32 permutation3
    mixedMoment B raw24772step1 raw24772step1Labels = mixedMoment B raw24772step2 raw24772step2Labels := by
      have ha : raw24772step2 = raw24772step1 := by apply Matrix.ext; unfold raw24772step2 raw24772step1; decide +kernel
      have hl : raw24772step1Labels = labelEmbedding6 ∘ raw24772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24772step1 raw24772step1Labels raw24772step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4145 node4145Labels := by rfl

def raw24773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24773step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24773step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24773 raw24773Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw24773 raw24773Labels = mixedMoment B raw24773step0 raw24773step0Labels := by
      have ha : raw24773step0 = (fun i j => raw24773 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24773step0 raw24773; decide +kernel
      have hl : raw24773step0Labels = raw24773Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24773 raw24773Labels permutation152 permutation3
    mixedMoment B raw24773step0 raw24773step0Labels = mixedMoment B raw24773step1 raw24773step1Labels := by
      have ha : raw24773step1 = raw24773step0 := by apply Matrix.ext; unfold raw24773step1 raw24773step0; decide +kernel
      have hl : raw24773step0Labels = labelEmbedding6 ∘ raw24773step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24773step0 raw24773step0Labels raw24773step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4524 node4524Labels := by rfl

def raw24774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24774step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24774step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24774step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24774 raw24774Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw24774 raw24774Labels = mixedMoment B raw24774step0 raw24774step0Labels := by
      have hz : ∀ j, raw24774 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24774step0 = (fun i j => raw24774 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24774step0 raw24774; decide +kernel
      have hl : raw24774step0Labels = raw24774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24774 raw24774Labels permutation265 hz
    mixedMoment B raw24774step0 raw24774step0Labels = mixedMoment B raw24774step1 raw24774step1Labels := by
      have ha : raw24774step1 = (fun i j => raw24774step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24774step1 raw24774step0; decide +kernel
      have hl : raw24774step1Labels = raw24774step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24774step0 raw24774step0Labels permutation32 permutation3
    mixedMoment B raw24774step1 raw24774step1Labels = mixedMoment B raw24774step2 raw24774step2Labels := by
      have ha : raw24774step2 = raw24774step1 := by apply Matrix.ext; unfold raw24774step2 raw24774step1; decide +kernel
      have hl : raw24774step1Labels = labelEmbedding6 ∘ raw24774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24774step1 raw24774step1Labels raw24774step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

def raw24775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24775step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24775step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24775step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24775step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24775step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24775step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24775step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24775 raw24775Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw24775 raw24775Labels = mixedMoment B raw24775step0 raw24775step0Labels := by
      have hz : ∀ j, raw24775 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24775step0 = (fun i j => raw24775 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24775step0 raw24775; decide +kernel
      have hl : raw24775step0Labels = raw24775Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24775 raw24775Labels permutation434 hz
    mixedMoment B raw24775step0 raw24775step0Labels = mixedMoment B raw24775step1 raw24775step1Labels := by
      have hz : ∀ j, raw24775step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24775step1 = (fun i j => raw24775step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24775step1 raw24775step0; decide +kernel
      have hl : raw24775step1Labels = raw24775step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24775step0 raw24775step0Labels permutation56 hz
    mixedMoment B raw24775step1 raw24775step1Labels = mixedMoment B raw24775step2 raw24775step2Labels := by
      have ha : raw24775step2 = (fun i j => raw24775step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24775step2 raw24775step1; decide +kernel
      have hl : raw24775step2Labels = raw24775step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24775step1 raw24775step1Labels permutation8 permutation3
    mixedMoment B raw24775step2 raw24775step2Labels = mixedMoment B raw24775step3 raw24775step3Labels := by
      have ha : raw24775step3 = raw24775step2 := by apply Matrix.ext; unfold raw24775step3 raw24775step2; decide +kernel
      have hl : raw24775step2Labels = labelEmbedding6 ∘ raw24775step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24775step2 raw24775step2Labels raw24775step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw24776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24776step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24776step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24776 raw24776Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw24776 raw24776Labels = mixedMoment B raw24776step0 raw24776step0Labels := by
      have hz : ∀ j, raw24776 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24776step0 = (fun i j => raw24776 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24776step0 raw24776; decide +kernel
      have hl : raw24776step0Labels = raw24776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24776 raw24776Labels permutation265 hz
    mixedMoment B raw24776step0 raw24776step0Labels = mixedMoment B raw24776step1 raw24776step1Labels := by
      have ha : raw24776step1 = (fun i j => raw24776step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24776step1 raw24776step0; decide +kernel
      have hl : raw24776step1Labels = raw24776step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24776step0 raw24776step0Labels permutation33 permutation3
    mixedMoment B raw24776step1 raw24776step1Labels = mixedMoment B raw24776step2 raw24776step2Labels := by
      have ha : raw24776step2 = raw24776step1 := by apply Matrix.ext; unfold raw24776step2 raw24776step1; decide +kernel
      have hl : raw24776step1Labels = labelEmbedding6 ∘ raw24776step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24776step1 raw24776step1Labels raw24776step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw24777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24777step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24777step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24777step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24777step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24777step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24777 raw24777Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw24777 raw24777Labels = mixedMoment B raw24777step0 raw24777step0Labels := by
      have hz : ∀ j, raw24777 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24777step0 = (fun i j => raw24777 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24777step0 raw24777; decide +kernel
      have hl : raw24777step0Labels = raw24777Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24777 raw24777Labels permutation265 hz
    mixedMoment B raw24777step0 raw24777step0Labels = mixedMoment B raw24777step1 raw24777step1Labels := by
      have ha : raw24777step1 = (fun i j => raw24777step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24777step1 raw24777step0; decide +kernel
      have hl : raw24777step1Labels = raw24777step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24777step0 raw24777step0Labels permutation34 permutation3
    mixedMoment B raw24777step1 raw24777step1Labels = mixedMoment B raw24777step2 raw24777step2Labels := by
      have ha : raw24777step2 = raw24777step1 := by apply Matrix.ext; unfold raw24777step2 raw24777step1; decide +kernel
      have hl : raw24777step1Labels = labelEmbedding6 ∘ raw24777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24777step1 raw24777step1Labels raw24777step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4140 node4140Labels := by rfl

def raw24778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24778step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24778step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24778step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24778 raw24778Labels = mixedMoment B node4521 node4521Labels := by
  calc
    mixedMoment B raw24778 raw24778Labels = mixedMoment B raw24778step0 raw24778step0Labels := by
      have ha : raw24778step0 = (fun i j => raw24778 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24778step0 raw24778; decide +kernel
      have hl : raw24778step0Labels = raw24778Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24778 raw24778Labels permutation154 permutation3
    mixedMoment B raw24778step0 raw24778step0Labels = mixedMoment B raw24778step1 raw24778step1Labels := by
      have ha : raw24778step1 = raw24778step0 := by apply Matrix.ext; unfold raw24778step1 raw24778step0; decide +kernel
      have hl : raw24778step0Labels = labelEmbedding6 ∘ raw24778step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24778step0 raw24778step0Labels raw24778step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4521 node4521Labels := by rfl

def raw24779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24779step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24779step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24779 raw24779Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw24779 raw24779Labels = mixedMoment B raw24779step0 raw24779step0Labels := by
      have hz : ∀ j, raw24779 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24779step0 = (fun i j => raw24779 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24779step0 raw24779; decide +kernel
      have hl : raw24779step0Labels = raw24779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24779 raw24779Labels permutation265 hz
    mixedMoment B raw24779step0 raw24779step0Labels = mixedMoment B raw24779step1 raw24779step1Labels := by
      have ha : raw24779step1 = (fun i j => raw24779step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24779step1 raw24779step0; decide +kernel
      have hl : raw24779step1Labels = raw24779step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24779step0 raw24779step0Labels permutation34 permutation3
    mixedMoment B raw24779step1 raw24779step1Labels = mixedMoment B raw24779step2 raw24779step2Labels := by
      have ha : raw24779step2 = raw24779step1 := by apply Matrix.ext; unfold raw24779step2 raw24779step1; decide +kernel
      have hl : raw24779step1Labels = labelEmbedding6 ∘ raw24779step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24779step1 raw24779step1Labels raw24779step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

def raw24780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24780step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24780step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24780step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw24780step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24780step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw24780step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24780 raw24780Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw24780 raw24780Labels = mixedMoment B raw24780step0 raw24780step0Labels := by
      have hz : ∀ j, raw24780 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24780step0 = (fun i j => raw24780 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24780step0 raw24780; decide +kernel
      have hl : raw24780step0Labels = raw24780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24780 raw24780Labels permutation434 hz
    mixedMoment B raw24780step0 raw24780step0Labels = mixedMoment B raw24780step1 raw24780step1Labels := by
      have hz : ∀ j, raw24780step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24780step1 = (fun i j => raw24780step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24780step1 raw24780step0; decide +kernel
      have hl : raw24780step1Labels = raw24780step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24780step0 raw24780step0Labels permutation56 hz
    mixedMoment B raw24780step1 raw24780step1Labels = mixedMoment B raw24780step2 raw24780step2Labels := by
      have ha : raw24780step2 = (fun i j => raw24780step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24780step2 raw24780step1; decide +kernel
      have hl : raw24780step2Labels = raw24780step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24780step1 raw24780step1Labels permutation8 permutation3
    mixedMoment B raw24780step2 raw24780step2Labels = mixedMoment B raw24780step3 raw24780step3Labels := by
      have ha : raw24780step3 = raw24780step2 := by apply Matrix.ext; unfold raw24780step3 raw24780step2; decide +kernel
      have hl : raw24780step2Labels = labelEmbedding6 ∘ raw24780step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24780step2 raw24780step2Labels raw24780step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw24781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24781step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw24781step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24781step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw24781step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24781 raw24781Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw24781 raw24781Labels = mixedMoment B raw24781step0 raw24781step0Labels := by
      have hz : ∀ j, raw24781 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24781step0 = (fun i j => raw24781 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24781step0 raw24781; decide +kernel
      have hl : raw24781step0Labels = raw24781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24781 raw24781Labels permutation265 hz
    mixedMoment B raw24781step0 raw24781step0Labels = mixedMoment B raw24781step1 raw24781step1Labels := by
      have ha : raw24781step1 = (fun i j => raw24781step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24781step1 raw24781step0; decide +kernel
      have hl : raw24781step1Labels = raw24781step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24781step0 raw24781step0Labels permutation34 permutation3
    mixedMoment B raw24781step1 raw24781step1Labels = mixedMoment B raw24781step2 raw24781step2Labels := by
      have ha : raw24781step2 = raw24781step1 := by apply Matrix.ext; unfold raw24781step2 raw24781step1; decide +kernel
      have hl : raw24781step1Labels = labelEmbedding6 ∘ raw24781step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24781step1 raw24781step1Labels raw24781step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

def raw24782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24782Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24782step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24782step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24782 raw24782Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw24782 raw24782Labels = mixedMoment B raw24782step0 raw24782step0Labels := by
      have ha : raw24782step0 = (fun i j => raw24782 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24782step0 raw24782; decide +kernel
      have hl : raw24782step0Labels = raw24782Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24782 raw24782Labels permutation154 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw24783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24783Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24783step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24783step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24783 raw24783Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw24783 raw24783Labels = mixedMoment B raw24783step0 raw24783step0Labels := by
      have hz : ∀ j, raw24783 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24783step0 = (fun i j => raw24783 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24783step0 raw24783; decide +kernel
      have hl : raw24783step0Labels = raw24783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24783 raw24783Labels permutation265 hz
    mixedMoment B raw24783step0 raw24783step0Labels = mixedMoment B raw24783step1 raw24783step1Labels := by
      have ha : raw24783step1 = (fun i j => raw24783step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24783step1 raw24783step0; decide +kernel
      have hl : raw24783step1Labels = raw24783step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24783step0 raw24783step0Labels permutation34 permutation3
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw24784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24784Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24784step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24784step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24784step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24784step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24784 raw24784Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw24784 raw24784Labels = mixedMoment B raw24784step0 raw24784step0Labels := by
      have hz : ∀ j, raw24784 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24784step0 = (fun i j => raw24784 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24784step0 raw24784; decide +kernel
      have hl : raw24784step0Labels = raw24784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24784 raw24784Labels permutation434 hz
    mixedMoment B raw24784step0 raw24784step0Labels = mixedMoment B raw24784step1 raw24784step1Labels := by
      have hz : ∀ j, raw24784step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24784step1 = (fun i j => raw24784step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24784step1 raw24784step0; decide +kernel
      have hl : raw24784step1Labels = raw24784step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24784step0 raw24784step0Labels permutation56 hz
    mixedMoment B raw24784step1 raw24784step1Labels = mixedMoment B raw24784step2 raw24784step2Labels := by
      have ha : raw24784step2 = (fun i j => raw24784step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24784step2 raw24784step1; decide +kernel
      have hl : raw24784step2Labels = raw24784step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24784step1 raw24784step1Labels permutation8 permutation3
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw24785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24785Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24785step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24785 raw24785Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw24785 raw24785Labels = mixedMoment B raw24785step0 raw24785step0Labels := by
      have hz : ∀ j, raw24785 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24785step0 = (fun i j => raw24785 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24785step0 raw24785; decide +kernel
      have hl : raw24785step0Labels = raw24785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24785 raw24785Labels permutation265 hz
    mixedMoment B raw24785step0 raw24785step0Labels = mixedMoment B raw24785step1 raw24785step1Labels := by
      have ha : raw24785step1 = (fun i j => raw24785step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24785step1 raw24785step0; decide +kernel
      have hl : raw24785step1Labels = raw24785step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24785step0 raw24785step0Labels permutation34 permutation3
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw24786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24786Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24786step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24786 raw24786Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw24786 raw24786Labels = mixedMoment B raw24786step0 raw24786step0Labels := by
      have hz : ∀ j, raw24786 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24786step0 = (fun i j => raw24786 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24786step0 raw24786; decide +kernel
      have hl : raw24786step0Labels = raw24786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24786 raw24786Labels permutation265 hz
    mixedMoment B raw24786step0 raw24786step0Labels = mixedMoment B raw24786step1 raw24786step1Labels := by
      have ha : raw24786step1 = (fun i j => raw24786step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24786step1 raw24786step0; decide +kernel
      have hl : raw24786step1Labels = raw24786step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24786step0 raw24786step0Labels permutation34 permutation3
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw24787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24787Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24787 raw24787Labels = mixedMoment B node567 node567Labels := by
  calc
    mixedMoment B raw24787 raw24787Labels = mixedMoment B raw24787step0 raw24787step0Labels := by
      have ha : raw24787step0 = (fun i j => raw24787 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24787step0 raw24787; decide +kernel
      have hl : raw24787step0Labels = raw24787Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24787 raw24787Labels permutation188 permutation3
    _ = mixedMoment B node567 node567Labels := by rfl

def raw24788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24788Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24788step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24788 raw24788Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw24788 raw24788Labels = mixedMoment B raw24788step0 raw24788step0Labels := by
      have ha : raw24788step0 = (fun i j => raw24788 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24788step0 raw24788; decide +kernel
      have hl : raw24788step0Labels = raw24788Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24788 raw24788Labels permutation188 permutation3
    _ = mixedMoment B node1097 node1097Labels := by rfl

def raw24789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24789Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24789step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24789 raw24789Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24789 raw24789Labels = mixedMoment B raw24789step0 raw24789step0Labels := by
      have hz : ∀ j, raw24789 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24789step0 = (fun i j => raw24789 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24789step0 raw24789; decide +kernel
      have hl : raw24789step0Labels = raw24789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24789 raw24789Labels permutation434 hz
    mixedMoment B raw24789step0 raw24789step0Labels = mixedMoment B raw24789step1 raw24789step1Labels := by
      have ha : raw24789step1 = (fun i j => raw24789step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24789step1 raw24789step0; decide +kernel
      have hl : raw24789step1Labels = raw24789step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24789step0 raw24789step0Labels permutation40 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24790Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24790step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24790 raw24790Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw24790 raw24790Labels = mixedMoment B raw24790step0 raw24790step0Labels := by
      have ha : raw24790step0 = (fun i j => raw24790 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24790step0 raw24790; decide +kernel
      have hl : raw24790step0Labels = raw24790Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24790 raw24790Labels permutation188 permutation3
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw24791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24791Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24791 raw24791Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw24791 raw24791Labels = mixedMoment B raw24791step0 raw24791step0Labels := by
      have ha : raw24791step0 = (fun i j => raw24791 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24791step0 raw24791; decide +kernel
      have hl : raw24791step0Labels = raw24791Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24791 raw24791Labels permutation188 permutation3
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw24792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24792step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24792 raw24792Labels = mixedMoment B node600 node600Labels := by
  calc
    mixedMoment B raw24792 raw24792Labels = mixedMoment B raw24792step0 raw24792step0Labels := by
      have hz : ∀ j, raw24792 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24792step0 = (fun i j => raw24792 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24792step0 raw24792; decide +kernel
      have hl : raw24792step0Labels = raw24792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24792 raw24792Labels permutation265 hz
    mixedMoment B raw24792step0 raw24792step0Labels = mixedMoment B raw24792step1 raw24792step1Labels := by
      have ha : raw24792step1 = (fun i j => raw24792step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24792step1 raw24792step0; decide +kernel
      have hl : raw24792step1Labels = raw24792step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24792step0 raw24792step0Labels permutation34 permutation3
    _ = mixedMoment B node600 node600Labels := by rfl

def raw24793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24793 raw24793Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw24793 raw24793Labels = mixedMoment B raw24793step0 raw24793step0Labels := by
      have ha : raw24793step0 = (fun i j => raw24793 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24793step0 raw24793; decide +kernel
      have hl : raw24793step0Labels = raw24793Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24793 raw24793Labels permutation154 permutation3
    _ = mixedMoment B node1126 node1126Labels := by rfl

def raw24794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24794step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24794step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw24794step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24794step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24794 raw24794Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw24794 raw24794Labels = mixedMoment B raw24794step0 raw24794step0Labels := by
      have hz : ∀ j, raw24794 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24794step0 = (fun i j => raw24794 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24794step0 raw24794; decide +kernel
      have hl : raw24794step0Labels = raw24794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24794 raw24794Labels permutation434 hz
    mixedMoment B raw24794step0 raw24794step0Labels = mixedMoment B raw24794step1 raw24794step1Labels := by
      have hz : ∀ j, raw24794step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24794step1 = (fun i j => raw24794step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24794step1 raw24794step0; decide +kernel
      have hl : raw24794step1Labels = raw24794step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24794step0 raw24794step0Labels permutation56 hz
    mixedMoment B raw24794step1 raw24794step1Labels = mixedMoment B raw24794step2 raw24794step2Labels := by
      have ha : raw24794step2 = (fun i j => raw24794step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24794step2 raw24794step1; decide +kernel
      have hl : raw24794step2Labels = raw24794step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24794step1 raw24794step1Labels permutation8 permutation3
    _ = mixedMoment B node1300 node1300Labels := by rfl

def raw24795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24795 raw24795Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24795 raw24795Labels = mixedMoment B raw24795step0 raw24795step0Labels := by
      have hz : ∀ j, raw24795 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24795step0 = (fun i j => raw24795 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24795step0 raw24795; decide +kernel
      have hl : raw24795step0Labels = raw24795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24795 raw24795Labels permutation265 hz
    mixedMoment B raw24795step0 raw24795step0Labels = mixedMoment B raw24795step1 raw24795step1Labels := by
      have ha : raw24795step1 = (fun i j => raw24795step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24795step1 raw24795step0; decide +kernel
      have hl : raw24795step1Labels = raw24795step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24795step0 raw24795step0Labels permutation44 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24796step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24796step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw24796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24796 raw24796Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw24796 raw24796Labels = mixedMoment B raw24796step0 raw24796step0Labels := by
      have hz : ∀ j, raw24796 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24796step0 = (fun i j => raw24796 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24796step0 raw24796; decide +kernel
      have hl : raw24796step0Labels = raw24796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24796 raw24796Labels permutation265 hz
    mixedMoment B raw24796step0 raw24796step0Labels = mixedMoment B raw24796step1 raw24796step1Labels := by
      have ha : raw24796step1 = (fun i j => raw24796step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24796step1 raw24796step0; decide +kernel
      have hl : raw24796step1Labels = raw24796step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24796step0 raw24796step0Labels permutation34 permutation3
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw24797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24797 raw24797Labels = mixedMoment B node569 node569Labels := by
  calc
    mixedMoment B raw24797 raw24797Labels = mixedMoment B raw24797step0 raw24797step0Labels := by
      have hz : ∀ j, raw24797 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24797step0 = (fun i j => raw24797 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24797step0 raw24797; decide +kernel
      have hl : raw24797step0Labels = raw24797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24797 raw24797Labels permutation265 hz
    mixedMoment B raw24797step0 raw24797step0Labels = mixedMoment B raw24797step1 raw24797step1Labels := by
      have ha : raw24797step1 = (fun i j => raw24797step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24797step1 raw24797step0; decide +kernel
      have hl : raw24797step1Labels = raw24797step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24797step0 raw24797step0Labels permutation34 permutation3
    _ = mixedMoment B node569 node569Labels := by rfl

def raw24798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24798 raw24798Labels = mixedMoment B node1106 node1106Labels := by
  calc
    mixedMoment B raw24798 raw24798Labels = mixedMoment B raw24798step0 raw24798step0Labels := by
      have ha : raw24798step0 = (fun i j => raw24798 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24798step0 raw24798; decide +kernel
      have hl : raw24798step0Labels = raw24798Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24798 raw24798Labels permutation154 permutation3
    _ = mixedMoment B node1106 node1106Labels := by rfl

def raw24799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw24799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24799 raw24799Labels = mixedMoment B node1099 node1099Labels := by
  calc
    mixedMoment B raw24799 raw24799Labels = mixedMoment B raw24799step0 raw24799step0Labels := by
      have hz : ∀ j, raw24799 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24799step0 = (fun i j => raw24799 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24799step0 raw24799; decide +kernel
      have hl : raw24799step0Labels = raw24799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24799 raw24799Labels permutation265 hz
    mixedMoment B raw24799step0 raw24799step0Labels = mixedMoment B raw24799step1 raw24799step1Labels := by
      have ha : raw24799step1 = (fun i j => raw24799step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24799step1 raw24799step0; decide +kernel
      have hl : raw24799step1Labels = raw24799step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24799step0 raw24799step0Labels permutation34 permutation3
    _ = mixedMoment B node1099 node1099Labels := by rfl

def raw24800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw24800step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw24800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24800 raw24800Labels = mixedMoment B node1205 node1205Labels := by
  calc
    mixedMoment B raw24800 raw24800Labels = mixedMoment B raw24800step0 raw24800step0Labels := by
      have hz : ∀ j, raw24800 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24800step0 = (fun i j => raw24800 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24800step0 raw24800; decide +kernel
      have hl : raw24800step0Labels = raw24800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24800 raw24800Labels permutation265 hz
    mixedMoment B raw24800step0 raw24800step0Labels = mixedMoment B raw24800step1 raw24800step1Labels := by
      have ha : raw24800step1 = (fun i j => raw24800step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24800step1 raw24800step0; decide +kernel
      have hl : raw24800step1Labels = raw24800step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24800step0 raw24800step0Labels permutation34 permutation3
    _ = mixedMoment B node1205 node1205Labels := by rfl

def raw24801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw24801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24801 raw24801Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24801 raw24801Labels = mixedMoment B raw24801step0 raw24801step0Labels := by
      have hz : ∀ j, raw24801 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24801step0 = (fun i j => raw24801 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24801step0 raw24801; decide +kernel
      have hl : raw24801step0Labels = raw24801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24801 raw24801Labels permutation265 hz
    mixedMoment B raw24801step0 raw24801step0Labels = mixedMoment B raw24801step1 raw24801step1Labels := by
      have ha : raw24801step1 = (fun i j => raw24801step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24801step1 raw24801step0; decide +kernel
      have hl : raw24801step1Labels = raw24801step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24801step0 raw24801step0Labels permutation35 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24802 raw24802Labels = mixedMoment B node573 node573Labels := by
  calc
    mixedMoment B raw24802 raw24802Labels = mixedMoment B raw24802step0 raw24802step0Labels := by
      have hz : ∀ j, raw24802 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24802step0 = (fun i j => raw24802 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24802step0 raw24802; decide +kernel
      have hl : raw24802step0Labels = raw24802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24802 raw24802Labels permutation265 hz
    mixedMoment B raw24802step0 raw24802step0Labels = mixedMoment B raw24802step1 raw24802step1Labels := by
      have ha : raw24802step1 = (fun i j => raw24802step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24802step1 raw24802step0; decide +kernel
      have hl : raw24802step1Labels = raw24802step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24802step0 raw24802step0Labels permutation32 permutation3
    _ = mixedMoment B node573 node573Labels := by rfl

def raw24803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24803 raw24803Labels = mixedMoment B node1108 node1108Labels := by
  calc
    mixedMoment B raw24803 raw24803Labels = mixedMoment B raw24803step0 raw24803step0Labels := by
      have ha : raw24803step0 = (fun i j => raw24803 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24803step0 raw24803; decide +kernel
      have hl : raw24803step0Labels = raw24803Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24803 raw24803Labels permutation152 permutation3
    _ = mixedMoment B node1108 node1108Labels := by rfl

def raw24804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw24804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24804 raw24804Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw24804 raw24804Labels = mixedMoment B raw24804step0 raw24804step0Labels := by
      have hz : ∀ j, raw24804 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24804step0 = (fun i j => raw24804 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24804step0 raw24804; decide +kernel
      have hl : raw24804step0Labels = raw24804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24804 raw24804Labels permutation265 hz
    mixedMoment B raw24804step0 raw24804step0Labels = mixedMoment B raw24804step1 raw24804step1Labels := by
      have ha : raw24804step1 = (fun i j => raw24804step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24804step1 raw24804step0; decide +kernel
      have hl : raw24804step1Labels = raw24804step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24804step0 raw24804step0Labels permutation32 permutation3
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw24805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw24805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24805step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw24805step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24805step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24805 raw24805Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw24805 raw24805Labels = mixedMoment B raw24805step0 raw24805step0Labels := by
      have hz : ∀ j, raw24805 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24805step0 = (fun i j => raw24805 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24805step0 raw24805; decide +kernel
      have hl : raw24805step0Labels = raw24805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24805 raw24805Labels permutation434 hz
    mixedMoment B raw24805step0 raw24805step0Labels = mixedMoment B raw24805step1 raw24805step1Labels := by
      have hz : ∀ j, raw24805step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24805step1 = (fun i j => raw24805step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24805step1 raw24805step0; decide +kernel
      have hl : raw24805step1Labels = raw24805step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24805step0 raw24805step0Labels permutation56 hz
    mixedMoment B raw24805step1 raw24805step1Labels = mixedMoment B raw24805step2 raw24805step2Labels := by
      have ha : raw24805step2 = (fun i j => raw24805step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24805step2 raw24805step1; decide +kernel
      have hl : raw24805step2Labels = raw24805step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24805step1 raw24805step1Labels permutation8 permutation3
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw24806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw24806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24806 raw24806Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw24806 raw24806Labels = mixedMoment B raw24806step0 raw24806step0Labels := by
      have hz : ∀ j, raw24806 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24806step0 = (fun i j => raw24806 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24806step0 raw24806; decide +kernel
      have hl : raw24806step0Labels = raw24806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24806 raw24806Labels permutation265 hz
    mixedMoment B raw24806step0 raw24806step0Labels = mixedMoment B raw24806step1 raw24806step1Labels := by
      have ha : raw24806step1 = (fun i j => raw24806step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24806step1 raw24806step0; decide +kernel
      have hl : raw24806step1Labels = raw24806step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24806step0 raw24806step0Labels permutation33 permutation3
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw24807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24807 raw24807Labels = mixedMoment B node568 node568Labels := by
  calc
    mixedMoment B raw24807 raw24807Labels = mixedMoment B raw24807step0 raw24807step0Labels := by
      have hz : ∀ j, raw24807 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24807step0 = (fun i j => raw24807 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24807step0 raw24807; decide +kernel
      have hl : raw24807step0Labels = raw24807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24807 raw24807Labels permutation265 hz
    mixedMoment B raw24807step0 raw24807step0Labels = mixedMoment B raw24807step1 raw24807step1Labels := by
      have ha : raw24807step1 = (fun i j => raw24807step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24807step1 raw24807step0; decide +kernel
      have hl : raw24807step1Labels = raw24807step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24807step0 raw24807step0Labels permutation34 permutation3
    _ = mixedMoment B node568 node568Labels := by rfl

def raw24808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24808 raw24808Labels = mixedMoment B node1105 node1105Labels := by
  calc
    mixedMoment B raw24808 raw24808Labels = mixedMoment B raw24808step0 raw24808step0Labels := by
      have ha : raw24808step0 = (fun i j => raw24808 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24808step0 raw24808; decide +kernel
      have hl : raw24808step0Labels = raw24808Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24808 raw24808Labels permutation154 permutation3
    _ = mixedMoment B node1105 node1105Labels := by rfl

def raw24809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24809step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw24809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24809 raw24809Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw24809 raw24809Labels = mixedMoment B raw24809step0 raw24809step0Labels := by
      have hz : ∀ j, raw24809 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24809step0 = (fun i j => raw24809 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24809step0 raw24809; decide +kernel
      have hl : raw24809step0Labels = raw24809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24809 raw24809Labels permutation265 hz
    mixedMoment B raw24809step0 raw24809step0Labels = mixedMoment B raw24809step1 raw24809step1Labels := by
      have ha : raw24809step1 = (fun i j => raw24809step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24809step1 raw24809step0; decide +kernel
      have hl : raw24809step1Labels = raw24809step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24809step0 raw24809step0Labels permutation34 permutation3
    _ = mixedMoment B node1098 node1098Labels := by rfl

def raw24810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw24810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24810step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24810step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw24810step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24810step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw24810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24810 raw24810Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw24810 raw24810Labels = mixedMoment B raw24810step0 raw24810step0Labels := by
      have hz : ∀ j, raw24810 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw24810step0 = (fun i j => raw24810 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw24810step0 raw24810; decide +kernel
      have hl : raw24810step0Labels = raw24810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24810 raw24810Labels permutation434 hz
    mixedMoment B raw24810step0 raw24810step0Labels = mixedMoment B raw24810step1 raw24810step1Labels := by
      have hz : ∀ j, raw24810step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24810step1 = (fun i j => raw24810step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24810step1 raw24810step0; decide +kernel
      have hl : raw24810step1Labels = raw24810step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24810step0 raw24810step0Labels permutation56 hz
    mixedMoment B raw24810step1 raw24810step1Labels = mixedMoment B raw24810step2 raw24810step2Labels := by
      have ha : raw24810step2 = (fun i j => raw24810step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24810step2 raw24810step1; decide +kernel
      have hl : raw24810step2Labels = raw24810step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24810step1 raw24810step1Labels permutation8 permutation3
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw24811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw24811step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw24811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24811 raw24811Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw24811 raw24811Labels = mixedMoment B raw24811step0 raw24811step0Labels := by
      have hz : ∀ j, raw24811 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24811step0 = (fun i j => raw24811 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24811step0 raw24811; decide +kernel
      have hl : raw24811step0Labels = raw24811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24811 raw24811Labels permutation265 hz
    mixedMoment B raw24811step0 raw24811step0Labels = mixedMoment B raw24811step1 raw24811step1Labels := by
      have ha : raw24811step1 = (fun i j => raw24811step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24811step1 raw24811step0; decide +kernel
      have hl : raw24811step1Labels = raw24811step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24811step0 raw24811step0Labels permutation34 permutation3
    _ = mixedMoment B node1202 node1202Labels := by rfl

def raw24812 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24812step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24812step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24812 raw24812Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw24812 raw24812Labels = mixedMoment B raw24812step0 raw24812step0Labels := by
      have ha : raw24812step0 = (fun i j => raw24812 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24812step0 raw24812; decide +kernel
      have hl : raw24812step0Labels = raw24812Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24812 raw24812Labels permutation152 permutation7
    mixedMoment B raw24812step0 raw24812step0Labels = mixedMoment B raw24812step1 raw24812step1Labels := by
      have ha : raw24812step1 = raw24812step0 := by apply Matrix.ext; unfold raw24812step1 raw24812step0; decide +kernel
      have hl : raw24812step0Labels = labelEmbedding10 ∘ raw24812step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24812step0 raw24812step0Labels raw24812step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw24813 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24813step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24813step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24813 raw24813Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw24813 raw24813Labels = mixedMoment B raw24813step0 raw24813step0Labels := by
      have hz : ∀ j, raw24813 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24813step0 = (fun i j => raw24813 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24813step0 raw24813; decide +kernel
      have hl : raw24813step0Labels = raw24813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24813 raw24813Labels permutation265 hz
    mixedMoment B raw24813step0 raw24813step0Labels = mixedMoment B raw24813step1 raw24813step1Labels := by
      have ha : raw24813step1 = (fun i j => raw24813step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24813step1 raw24813step0; decide +kernel
      have hl : raw24813step1Labels = raw24813step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24813step0 raw24813step0Labels permutation32 permutation7
    mixedMoment B raw24813step1 raw24813step1Labels = mixedMoment B raw24813step2 raw24813step2Labels := by
      have ha : raw24813step2 = raw24813step1 := by apply Matrix.ext; unfold raw24813step2 raw24813step1; decide +kernel
      have hl : raw24813step1Labels = labelEmbedding10 ∘ raw24813step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24813step1 raw24813step1Labels raw24813step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw24814 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24814step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24814step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24814 raw24814Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw24814 raw24814Labels = mixedMoment B raw24814step0 raw24814step0Labels := by
      have hz : ∀ j, raw24814 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24814step0 = (fun i j => raw24814 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24814step0 raw24814; decide +kernel
      have hl : raw24814step0Labels = raw24814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24814 raw24814Labels permutation265 hz
    mixedMoment B raw24814step0 raw24814step0Labels = mixedMoment B raw24814step1 raw24814step1Labels := by
      have ha : raw24814step1 = (fun i j => raw24814step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24814step1 raw24814step0; decide +kernel
      have hl : raw24814step1Labels = raw24814step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24814step0 raw24814step0Labels permutation32 permutation7
    mixedMoment B raw24814step1 raw24814step1Labels = mixedMoment B raw24814step2 raw24814step2Labels := by
      have ha : raw24814step2 = raw24814step1 := by apply Matrix.ext; unfold raw24814step2 raw24814step1; decide +kernel
      have hl : raw24814step1Labels = labelEmbedding10 ∘ raw24814step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24814step1 raw24814step1Labels raw24814step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw24815 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24815step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24815step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24815step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24815step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24815 raw24815Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw24815 raw24815Labels = mixedMoment B raw24815step0 raw24815step0Labels := by
      have ha : raw24815step0 = (fun i j => raw24815 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24815step0 raw24815; decide +kernel
      have hl : raw24815step0Labels = raw24815Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24815 raw24815Labels permutation178 permutation6
    mixedMoment B raw24815step0 raw24815step0Labels = mixedMoment B raw24815step1 raw24815step1Labels := by
      have ha : raw24815step1 = raw24815step0 := by apply Matrix.ext; unfold raw24815step1 raw24815step0; decide +kernel
      have hl : raw24815step0Labels = labelEmbedding9 ∘ raw24815step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24815step0 raw24815step0Labels raw24815step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw24816 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24816step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24816step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24816step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24816step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24816 raw24816Labels = mixedMoment B node4561 node4561Labels := by
  calc
    mixedMoment B raw24816 raw24816Labels = mixedMoment B raw24816step0 raw24816step0Labels := by
      have ha : raw24816step0 = (fun i j => raw24816 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24816step0 raw24816; decide +kernel
      have hl : raw24816step0Labels = raw24816Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24816 raw24816Labels permutation178 permutation6
    mixedMoment B raw24816step0 raw24816step0Labels = mixedMoment B raw24816step1 raw24816step1Labels := by
      have ha : raw24816step1 = raw24816step0 := by apply Matrix.ext; unfold raw24816step1 raw24816step0; decide +kernel
      have hl : raw24816step0Labels = labelEmbedding9 ∘ raw24816step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24816step0 raw24816step0Labels raw24816step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4561 node4561Labels := by rfl

def raw24817 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24817step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24817 raw24817Labels = mixedMoment B node4587 node4587Labels := by
  calc
    mixedMoment B raw24817 raw24817Labels = mixedMoment B raw24817step0 raw24817step0Labels := by
      have ha : raw24817step0 = (fun i j => raw24817 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24817step0 raw24817; decide +kernel
      have hl : raw24817step0Labels = raw24817Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24817 raw24817Labels permutation178 permutation6
    mixedMoment B raw24817step0 raw24817step0Labels = mixedMoment B raw24817step1 raw24817step1Labels := by
      have ha : raw24817step1 = raw24817step0 := by apply Matrix.ext; unfold raw24817step1 raw24817step0; decide +kernel
      have hl : raw24817step0Labels = labelEmbedding9 ∘ raw24817step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24817step0 raw24817step0Labels raw24817step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4587 node4587Labels := by rfl

def raw24818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24818step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24818 raw24818Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw24818 raw24818Labels = mixedMoment B raw24818step0 raw24818step0Labels := by
      have hz : ∀ j, raw24818 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24818step0 = (fun i j => raw24818 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24818step0 raw24818; decide +kernel
      have hl : raw24818step0Labels = raw24818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24818 raw24818Labels permutation265 hz
    mixedMoment B raw24818step0 raw24818step0Labels = mixedMoment B raw24818step1 raw24818step1Labels := by
      have ha : raw24818step1 = (fun i j => raw24818step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24818step1 raw24818step0; decide +kernel
      have hl : raw24818step1Labels = raw24818step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24818step0 raw24818step0Labels permutation34 permutation6
    mixedMoment B raw24818step1 raw24818step1Labels = mixedMoment B raw24818step2 raw24818step2Labels := by
      have ha : raw24818step2 = raw24818step1 := by apply Matrix.ext; unfold raw24818step2 raw24818step1; decide +kernel
      have hl : raw24818step1Labels = labelEmbedding9 ∘ raw24818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24818step1 raw24818step1Labels raw24818step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw24819 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24819step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24819step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24819step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24819 raw24819Labels = mixedMoment B node4580 node4580Labels := by
  calc
    mixedMoment B raw24819 raw24819Labels = mixedMoment B raw24819step0 raw24819step0Labels := by
      have ha : raw24819step0 = (fun i j => raw24819 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24819step0 raw24819; decide +kernel
      have hl : raw24819step0Labels = raw24819Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24819 raw24819Labels permutation154 permutation6
    mixedMoment B raw24819step0 raw24819step0Labels = mixedMoment B raw24819step1 raw24819step1Labels := by
      have ha : raw24819step1 = raw24819step0 := by apply Matrix.ext; unfold raw24819step1 raw24819step0; decide +kernel
      have hl : raw24819step0Labels = labelEmbedding9 ∘ raw24819step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24819step0 raw24819step0Labels raw24819step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4580 node4580Labels := by rfl

def raw24820 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw24820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24820step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24820 raw24820Labels = mixedMoment B node4568 node4568Labels := by
  calc
    mixedMoment B raw24820 raw24820Labels = mixedMoment B raw24820step0 raw24820step0Labels := by
      have hz : ∀ j, raw24820 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24820step0 = (fun i j => raw24820 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24820step0 raw24820; decide +kernel
      have hl : raw24820step0Labels = raw24820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24820 raw24820Labels permutation265 hz
    mixedMoment B raw24820step0 raw24820step0Labels = mixedMoment B raw24820step1 raw24820step1Labels := by
      have ha : raw24820step1 = (fun i j => raw24820step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24820step1 raw24820step0; decide +kernel
      have hl : raw24820step1Labels = raw24820step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24820step0 raw24820step0Labels permutation34 permutation6
    mixedMoment B raw24820step1 raw24820step1Labels = mixedMoment B raw24820step2 raw24820step2Labels := by
      have ha : raw24820step2 = raw24820step1 := by apply Matrix.ext; unfold raw24820step2 raw24820step1; decide +kernel
      have hl : raw24820step1Labels = labelEmbedding9 ∘ raw24820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24820step1 raw24820step1Labels raw24820step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4568 node4568Labels := by rfl

def raw24821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw24821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24821step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24821 raw24821Labels = mixedMoment B node4597 node4597Labels := by
  calc
    mixedMoment B raw24821 raw24821Labels = mixedMoment B raw24821step0 raw24821step0Labels := by
      have hz : ∀ j, raw24821 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24821step0 = (fun i j => raw24821 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24821step0 raw24821; decide +kernel
      have hl : raw24821step0Labels = raw24821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24821 raw24821Labels permutation265 hz
    mixedMoment B raw24821step0 raw24821step0Labels = mixedMoment B raw24821step1 raw24821step1Labels := by
      have ha : raw24821step1 = (fun i j => raw24821step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24821step1 raw24821step0; decide +kernel
      have hl : raw24821step1Labels = raw24821step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24821step0 raw24821step0Labels permutation34 permutation6
    mixedMoment B raw24821step1 raw24821step1Labels = mixedMoment B raw24821step2 raw24821step2Labels := by
      have ha : raw24821step2 = raw24821step1 := by apply Matrix.ext; unfold raw24821step2 raw24821step1; decide +kernel
      have hl : raw24821step1Labels = labelEmbedding9 ∘ raw24821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24821step1 raw24821step1Labels raw24821step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4597 node4597Labels := by rfl

def raw24822 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24822step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24822step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24822 raw24822Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw24822 raw24822Labels = mixedMoment B raw24822step0 raw24822step0Labels := by
      have hz : ∀ j, raw24822 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24822step0 = (fun i j => raw24822 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24822step0 raw24822; decide +kernel
      have hl : raw24822step0Labels = raw24822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24822 raw24822Labels permutation265 hz
    mixedMoment B raw24822step0 raw24822step0Labels = mixedMoment B raw24822step1 raw24822step1Labels := by
      have ha : raw24822step1 = (fun i j => raw24822step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24822step1 raw24822step0; decide +kernel
      have hl : raw24822step1Labels = raw24822step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24822step0 raw24822step0Labels permutation34 permutation6
    mixedMoment B raw24822step1 raw24822step1Labels = mixedMoment B raw24822step2 raw24822step2Labels := by
      have ha : raw24822step2 = raw24822step1 := by apply Matrix.ext; unfold raw24822step2 raw24822step1; decide +kernel
      have hl : raw24822step1Labels = labelEmbedding9 ∘ raw24822step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24822step1 raw24822step1Labels raw24822step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw24823 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24823step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24823 raw24823Labels = mixedMoment B node4579 node4579Labels := by
  calc
    mixedMoment B raw24823 raw24823Labels = mixedMoment B raw24823step0 raw24823step0Labels := by
      have ha : raw24823step0 = (fun i j => raw24823 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24823step0 raw24823; decide +kernel
      have hl : raw24823step0Labels = raw24823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24823 raw24823Labels permutation154 permutation6
    mixedMoment B raw24823step0 raw24823step0Labels = mixedMoment B raw24823step1 raw24823step1Labels := by
      have ha : raw24823step1 = raw24823step0 := by apply Matrix.ext; unfold raw24823step1 raw24823step0; decide +kernel
      have hl : raw24823step0Labels = labelEmbedding9 ∘ raw24823step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24823step0 raw24823step0Labels raw24823step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4579 node4579Labels := by rfl

def raw24824 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw24824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24824step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24824 raw24824Labels = mixedMoment B node4567 node4567Labels := by
  calc
    mixedMoment B raw24824 raw24824Labels = mixedMoment B raw24824step0 raw24824step0Labels := by
      have hz : ∀ j, raw24824 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24824step0 = (fun i j => raw24824 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24824step0 raw24824; decide +kernel
      have hl : raw24824step0Labels = raw24824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24824 raw24824Labels permutation265 hz
    mixedMoment B raw24824step0 raw24824step0Labels = mixedMoment B raw24824step1 raw24824step1Labels := by
      have ha : raw24824step1 = (fun i j => raw24824step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24824step1 raw24824step0; decide +kernel
      have hl : raw24824step1Labels = raw24824step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24824step0 raw24824step0Labels permutation34 permutation6
    mixedMoment B raw24824step1 raw24824step1Labels = mixedMoment B raw24824step2 raw24824step2Labels := by
      have ha : raw24824step2 = raw24824step1 := by apply Matrix.ext; unfold raw24824step2 raw24824step1; decide +kernel
      have hl : raw24824step1Labels = labelEmbedding9 ∘ raw24824step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24824step1 raw24824step1Labels raw24824step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4567 node4567Labels := by rfl

def raw24825 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw24825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24825step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24825 raw24825Labels = mixedMoment B node4596 node4596Labels := by
  calc
    mixedMoment B raw24825 raw24825Labels = mixedMoment B raw24825step0 raw24825step0Labels := by
      have hz : ∀ j, raw24825 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24825step0 = (fun i j => raw24825 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24825step0 raw24825; decide +kernel
      have hl : raw24825step0Labels = raw24825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24825 raw24825Labels permutation265 hz
    mixedMoment B raw24825step0 raw24825step0Labels = mixedMoment B raw24825step1 raw24825step1Labels := by
      have ha : raw24825step1 = (fun i j => raw24825step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24825step1 raw24825step0; decide +kernel
      have hl : raw24825step1Labels = raw24825step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24825step0 raw24825step0Labels permutation34 permutation6
    mixedMoment B raw24825step1 raw24825step1Labels = mixedMoment B raw24825step2 raw24825step2Labels := by
      have ha : raw24825step2 = raw24825step1 := by apply Matrix.ext; unfold raw24825step2 raw24825step1; decide +kernel
      have hl : raw24825step1Labels = labelEmbedding9 ∘ raw24825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24825step1 raw24825step1Labels raw24825step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4596 node4596Labels := by rfl

def raw24826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24826 raw24826Labels = mixedMoment B node1229 node1229Labels := by
  calc
    mixedMoment B raw24826 raw24826Labels = mixedMoment B raw24826step0 raw24826step0Labels := by
      have hz : ∀ j, raw24826 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24826step0 = (fun i j => raw24826 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24826step0 raw24826; decide +kernel
      have hl : raw24826step0Labels = raw24826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24826 raw24826Labels permutation265 hz
    mixedMoment B raw24826step0 raw24826step0Labels = mixedMoment B raw24826step1 raw24826step1Labels := by
      have ha : raw24826step1 = (fun i j => raw24826step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24826step1 raw24826step0; decide +kernel
      have hl : raw24826step1Labels = raw24826step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24826step0 raw24826step0Labels permutation34 permutation2
    _ = mixedMoment B node1229 node1229Labels := by rfl

def raw24827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24827 raw24827Labels = mixedMoment B node2550 node2550Labels := by
  calc
    mixedMoment B raw24827 raw24827Labels = mixedMoment B raw24827step0 raw24827step0Labels := by
      have ha : raw24827step0 = (fun i j => raw24827 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24827step0 raw24827; decide +kernel
      have hl : raw24827step0Labels = raw24827Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24827 raw24827Labels permutation154 permutation2
    _ = mixedMoment B node2550 node2550Labels := by rfl

def raw24828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24828 raw24828Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw24828 raw24828Labels = mixedMoment B raw24828step0 raw24828step0Labels := by
      have hz : ∀ j, raw24828 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24828step0 = (fun i j => raw24828 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24828step0 raw24828; decide +kernel
      have hl : raw24828step0Labels = raw24828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24828 raw24828Labels permutation265 hz
    mixedMoment B raw24828step0 raw24828step0Labels = mixedMoment B raw24828step1 raw24828step1Labels := by
      have ha : raw24828step1 = (fun i j => raw24828step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24828step1 raw24828step0; decide +kernel
      have hl : raw24828step1Labels = raw24828step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24828step0 raw24828step0Labels permutation34 permutation2
    _ = mixedMoment B node2504 node2504Labels := by rfl

def raw24829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24829Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw24829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24829 raw24829Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw24829 raw24829Labels = mixedMoment B raw24829step0 raw24829step0Labels := by
      have hz : ∀ j, raw24829 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24829step0 = (fun i j => raw24829 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24829step0 raw24829; decide +kernel
      have hl : raw24829step0Labels = raw24829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24829 raw24829Labels permutation265 hz
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw24830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw24830Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 1, -3]]
def raw24830step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24830 raw24830Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw24830 raw24830Labels = mixedMoment B raw24830step0 raw24830step0Labels := by
      have hz : ∀ j, raw24830 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24830step0 = (fun i j => raw24830 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24830step0 raw24830; decide +kernel
      have hl : raw24830step0Labels = raw24830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24830 raw24830Labels permutation265 hz
    mixedMoment B raw24830step0 raw24830step0Labels = mixedMoment B raw24830step1 raw24830step1Labels := by
      have ha : raw24830step1 = (fun i j => raw24830step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24830step1 raw24830step0; decide +kernel
      have hl : raw24830step1Labels = raw24830step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24830step0 raw24830step0Labels permutation34 permutation2
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw24831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw24831Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 2, -3]]
def raw24831step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw24831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24831 raw24831Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw24831 raw24831Labels = mixedMoment B raw24831step0 raw24831step0Labels := by
      have hz : ∀ j, raw24831 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24831step0 = (fun i j => raw24831 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24831step0 raw24831; decide +kernel
      have hl : raw24831step0Labels = raw24831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24831 raw24831Labels permutation265 hz
    mixedMoment B raw24831step0 raw24831step0Labels = mixedMoment B raw24831step1 raw24831step1Labels := by
      have ha : raw24831step1 = (fun i j => raw24831step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24831step1 raw24831step0; decide +kernel
      have hl : raw24831step1Labels = raw24831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24831step0 raw24831step0Labels permutation34 permutation2
    _ = mixedMoment B node2735 node2735Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
