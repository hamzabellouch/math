import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw41984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41984Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw41984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41984step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41984step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw41984step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41984 raw41984Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw41984 raw41984Labels = mixedMoment B raw41984step0 raw41984step0Labels := by
      have hz : ∀ j, raw41984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41984step0 = (fun i j => raw41984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41984step0 raw41984; decide +kernel
      have hl : raw41984step0Labels = raw41984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41984 raw41984Labels permutation346 hz
    mixedMoment B raw41984step0 raw41984step0Labels = mixedMoment B raw41984step1 raw41984step1Labels := by
      have ha : raw41984step1 = (fun i j => raw41984step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41984step1 raw41984step0; decide +kernel
      have hl : raw41984step1Labels = raw41984step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41984step0 raw41984step0Labels permutation37 permutation4
    mixedMoment B raw41984step1 raw41984step1Labels = mixedMoment B raw41984step2 raw41984step2Labels := by
      have ha : raw41984step2 = -raw41984step1 := by apply Matrix.ext; change ∀ i j, raw41984step2 i j = -(raw41984step1 i j); unfold raw41984step2 raw41984step1; decide +kernel
      have hl : raw41984step2Labels = raw41984step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41984step2 raw41984step2Labels = mixedMoment B raw41984step3 raw41984step3Labels := by
      have ha : raw41984step3 = raw41984step2 := by apply Matrix.ext; unfold raw41984step3 raw41984step2; decide +kernel
      have hl : raw41984step2Labels = labelEmbedding1 ∘ raw41984step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41984step2 raw41984step2Labels raw41984step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw41985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41985Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw41985step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw41985step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41985step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw41985step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41985 raw41985Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw41985 raw41985Labels = mixedMoment B raw41985step0 raw41985step0Labels := by
      have hz : ∀ j, raw41985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41985step0 = (fun i j => raw41985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41985step0 raw41985; decide +kernel
      have hl : raw41985step0Labels = raw41985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41985 raw41985Labels permutation346 hz
    mixedMoment B raw41985step0 raw41985step0Labels = mixedMoment B raw41985step1 raw41985step1Labels := by
      have ha : raw41985step1 = (fun i j => raw41985step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41985step1 raw41985step0; decide +kernel
      have hl : raw41985step1Labels = raw41985step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41985step0 raw41985step0Labels permutation32 permutation5
    mixedMoment B raw41985step1 raw41985step1Labels = mixedMoment B raw41985step2 raw41985step2Labels := by
      have ha : raw41985step2 = -raw41985step1 := by apply Matrix.ext; change ∀ i j, raw41985step2 i j = -(raw41985step1 i j); unfold raw41985step2 raw41985step1; decide +kernel
      have hl : raw41985step2Labels = raw41985step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41985step2 raw41985step2Labels = mixedMoment B raw41985step3 raw41985step3Labels := by
      have ha : raw41985step3 = raw41985step2 := by apply Matrix.ext; unfold raw41985step3 raw41985step2; decide +kernel
      have hl : raw41985step2Labels = labelEmbedding9 ∘ raw41985step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41985step2 raw41985step2Labels raw41985step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw41986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41986Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41986step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41986 raw41986Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw41986 raw41986Labels = mixedMoment B raw41986step0 raw41986step0Labels := by
      have hz : ∀ j, raw41986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41986step0 = (fun i j => raw41986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41986step0 raw41986; decide +kernel
      have hl : raw41986step0Labels = raw41986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41986 raw41986Labels permutation346 hz
    mixedMoment B raw41986step0 raw41986step0Labels = mixedMoment B raw41986step1 raw41986step1Labels := by
      have ha : raw41986step1 = (fun i j => raw41986step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41986step1 raw41986step0; decide +kernel
      have hl : raw41986step1Labels = raw41986step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41986step0 raw41986step0Labels permutation50 permutation4
    mixedMoment B raw41986step1 raw41986step1Labels = mixedMoment B raw41986step2 raw41986step2Labels := by
      have ha : raw41986step2 = -raw41986step1 := by apply Matrix.ext; change ∀ i j, raw41986step2 i j = -(raw41986step1 i j); unfold raw41986step2 raw41986step1; decide +kernel
      have hl : raw41986step2Labels = raw41986step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41986step2 raw41986step2Labels = mixedMoment B raw41986step3 raw41986step3Labels := by
      have ha : raw41986step3 = raw41986step2 := by apply Matrix.ext; unfold raw41986step3 raw41986step2; decide +kernel
      have hl : raw41986step2Labels = labelEmbedding1 ∘ raw41986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41986step2 raw41986step2Labels raw41986step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw41987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41987Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw41987step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw41987step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41987step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41987step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw41987step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41987 raw41987Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw41987 raw41987Labels = mixedMoment B raw41987step0 raw41987step0Labels := by
      have hz : ∀ j, raw41987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41987step0 = (fun i j => raw41987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41987step0 raw41987; decide +kernel
      have hl : raw41987step0Labels = raw41987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41987 raw41987Labels permutation346 hz
    mixedMoment B raw41987step0 raw41987step0Labels = mixedMoment B raw41987step1 raw41987step1Labels := by
      have ha : raw41987step1 = (fun i j => raw41987step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41987step1 raw41987step0; decide +kernel
      have hl : raw41987step1Labels = raw41987step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41987step0 raw41987step0Labels permutation36 permutation5
    mixedMoment B raw41987step1 raw41987step1Labels = mixedMoment B raw41987step2 raw41987step2Labels := by
      have ha : raw41987step2 = -raw41987step1 := by apply Matrix.ext; change ∀ i j, raw41987step2 i j = -(raw41987step1 i j); unfold raw41987step2 raw41987step1; decide +kernel
      have hl : raw41987step2Labels = raw41987step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41987step2 raw41987step2Labels = mixedMoment B raw41987step3 raw41987step3Labels := by
      have ha : raw41987step3 = raw41987step2 := by apply Matrix.ext; unfold raw41987step3 raw41987step2; decide +kernel
      have hl : raw41987step2Labels = labelEmbedding9 ∘ raw41987step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41987step2 raw41987step2Labels raw41987step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw41988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41988Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw41988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41988step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41988step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw41988step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41988 raw41988Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw41988 raw41988Labels = mixedMoment B raw41988step0 raw41988step0Labels := by
      have hz : ∀ j, raw41988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41988step0 = (fun i j => raw41988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41988step0 raw41988; decide +kernel
      have hl : raw41988step0Labels = raw41988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41988 raw41988Labels permutation346 hz
    mixedMoment B raw41988step0 raw41988step0Labels = mixedMoment B raw41988step1 raw41988step1Labels := by
      have ha : raw41988step1 = (fun i j => raw41988step0 (permutation51 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41988step1 raw41988step0; decide +kernel
      have hl : raw41988step1Labels = raw41988step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41988step0 raw41988step0Labels permutation51 permutation4
    mixedMoment B raw41988step1 raw41988step1Labels = mixedMoment B raw41988step2 raw41988step2Labels := by
      have ha : raw41988step2 = -raw41988step1 := by apply Matrix.ext; change ∀ i j, raw41988step2 i j = -(raw41988step1 i j); unfold raw41988step2 raw41988step1; decide +kernel
      have hl : raw41988step2Labels = raw41988step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41988step2 raw41988step2Labels = mixedMoment B raw41988step3 raw41988step3Labels := by
      have ha : raw41988step3 = raw41988step2 := by apply Matrix.ext; unfold raw41988step3 raw41988step2; decide +kernel
      have hl : raw41988step2Labels = labelEmbedding1 ∘ raw41988step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41988step2 raw41988step2Labels raw41988step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw41989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41989Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw41989step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw41989step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41989step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw41989step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41989 raw41989Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw41989 raw41989Labels = mixedMoment B raw41989step0 raw41989step0Labels := by
      have hz : ∀ j, raw41989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41989step0 = (fun i j => raw41989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41989step0 raw41989; decide +kernel
      have hl : raw41989step0Labels = raw41989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41989 raw41989Labels permutation346 hz
    mixedMoment B raw41989step0 raw41989step0Labels = mixedMoment B raw41989step1 raw41989step1Labels := by
      have ha : raw41989step1 = (fun i j => raw41989step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41989step1 raw41989step0; decide +kernel
      have hl : raw41989step1Labels = raw41989step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41989step0 raw41989step0Labels permutation37 permutation5
    mixedMoment B raw41989step1 raw41989step1Labels = mixedMoment B raw41989step2 raw41989step2Labels := by
      have ha : raw41989step2 = -raw41989step1 := by apply Matrix.ext; change ∀ i j, raw41989step2 i j = -(raw41989step1 i j); unfold raw41989step2 raw41989step1; decide +kernel
      have hl : raw41989step2Labels = raw41989step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41989step2 raw41989step2Labels = mixedMoment B raw41989step3 raw41989step3Labels := by
      have ha : raw41989step3 = raw41989step2 := by apply Matrix.ext; unfold raw41989step3 raw41989step2; decide +kernel
      have hl : raw41989step2Labels = labelEmbedding9 ∘ raw41989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41989step2 raw41989step2Labels raw41989step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw41990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41990Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41990step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw41990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41990 raw41990Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw41990 raw41990Labels = mixedMoment B raw41990step0 raw41990step0Labels := by
      have hz : ∀ j, raw41990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41990step0 = (fun i j => raw41990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41990step0 raw41990; decide +kernel
      have hl : raw41990step0Labels = raw41990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41990 raw41990Labels permutation346 hz
    mixedMoment B raw41990step0 raw41990step0Labels = mixedMoment B raw41990step1 raw41990step1Labels := by
      have ha : raw41990step1 = (fun i j => raw41990step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41990step1 raw41990step0; decide +kernel
      have hl : raw41990step1Labels = raw41990step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41990step0 raw41990step0Labels permutation38 permutation4
    mixedMoment B raw41990step1 raw41990step1Labels = mixedMoment B raw41990step2 raw41990step2Labels := by
      have ha : raw41990step2 = -raw41990step1 := by apply Matrix.ext; change ∀ i j, raw41990step2 i j = -(raw41990step1 i j); unfold raw41990step2 raw41990step1; decide +kernel
      have hl : raw41990step2Labels = raw41990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41990step2 raw41990step2Labels = mixedMoment B raw41990step3 raw41990step3Labels := by
      have ha : raw41990step3 = raw41990step2 := by apply Matrix.ext; unfold raw41990step3 raw41990step2; decide +kernel
      have hl : raw41990step2Labels = labelEmbedding1 ∘ raw41990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41990step2 raw41990step2Labels raw41990step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw41991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41991Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw41991step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41991step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41991step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41991step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41991 raw41991Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw41991 raw41991Labels = mixedMoment B raw41991step0 raw41991step0Labels := by
      have hz : ∀ j, raw41991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41991step0 = (fun i j => raw41991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41991step0 raw41991; decide +kernel
      have hl : raw41991step0Labels = raw41991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41991 raw41991Labels permutation346 hz
    mixedMoment B raw41991step0 raw41991step0Labels = mixedMoment B raw41991step1 raw41991step1Labels := by
      have ha : raw41991step1 = (fun i j => raw41991step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41991step1 raw41991step0; decide +kernel
      have hl : raw41991step1Labels = raw41991step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41991step0 raw41991step0Labels permutation32 permutation5
    mixedMoment B raw41991step1 raw41991step1Labels = mixedMoment B raw41991step2 raw41991step2Labels := by
      have ha : raw41991step2 = -raw41991step1 := by apply Matrix.ext; change ∀ i j, raw41991step2 i j = -(raw41991step1 i j); unfold raw41991step2 raw41991step1; decide +kernel
      have hl : raw41991step2Labels = raw41991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41991step2 raw41991step2Labels = mixedMoment B raw41991step3 raw41991step3Labels := by
      have ha : raw41991step3 = raw41991step2 := by apply Matrix.ext; unfold raw41991step3 raw41991step2; decide +kernel
      have hl : raw41991step2Labels = labelEmbedding9 ∘ raw41991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41991step2 raw41991step2Labels raw41991step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw41992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41992Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw41992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41992step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41992 raw41992Labels = mixedMoment B node3111 node3111Labels := by
  calc
    mixedMoment B raw41992 raw41992Labels = mixedMoment B raw41992step0 raw41992step0Labels := by
      have hz : ∀ j, raw41992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41992step0 = (fun i j => raw41992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41992step0 raw41992; decide +kernel
      have hl : raw41992step0Labels = raw41992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41992 raw41992Labels permutation346 hz
    mixedMoment B raw41992step0 raw41992step0Labels = mixedMoment B raw41992step1 raw41992step1Labels := by
      have ha : raw41992step1 = (fun i j => raw41992step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41992step1 raw41992step0; decide +kernel
      have hl : raw41992step1Labels = raw41992step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41992step0 raw41992step0Labels permutation32 permutation4
    mixedMoment B raw41992step1 raw41992step1Labels = mixedMoment B raw41992step2 raw41992step2Labels := by
      have ha : raw41992step2 = -raw41992step1 := by apply Matrix.ext; change ∀ i j, raw41992step2 i j = -(raw41992step1 i j); unfold raw41992step2 raw41992step1; decide +kernel
      have hl : raw41992step2Labels = raw41992step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41992step2 raw41992step2Labels = mixedMoment B raw41992step3 raw41992step3Labels := by
      have ha : raw41992step3 = raw41992step2 := by apply Matrix.ext; unfold raw41992step3 raw41992step2; decide +kernel
      have hl : raw41992step2Labels = labelEmbedding1 ∘ raw41992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41992step2 raw41992step2Labels raw41992step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3111 node3111Labels := by rfl

def raw41993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41993Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw41993step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw41993step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41993step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw41993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41993 raw41993Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw41993 raw41993Labels = mixedMoment B raw41993step0 raw41993step0Labels := by
      have hz : ∀ j, raw41993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw41993step0 = (fun i j => raw41993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw41993step0 raw41993; decide +kernel
      have hl : raw41993step0Labels = raw41993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw41993 raw41993Labels permutation346 hz
    mixedMoment B raw41993step0 raw41993step0Labels = mixedMoment B raw41993step1 raw41993step1Labels := by
      have ha : raw41993step1 = (fun i j => raw41993step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41993step1 raw41993step0; decide +kernel
      have hl : raw41993step1Labels = raw41993step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41993step0 raw41993step0Labels permutation32 permutation5
    mixedMoment B raw41993step1 raw41993step1Labels = mixedMoment B raw41993step2 raw41993step2Labels := by
      have ha : raw41993step2 = -raw41993step1 := by apply Matrix.ext; change ∀ i j, raw41993step2 i j = -(raw41993step1 i j); unfold raw41993step2 raw41993step1; decide +kernel
      have hl : raw41993step2Labels = raw41993step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41993step2 raw41993step2Labels = mixedMoment B raw41993step3 raw41993step3Labels := by
      have ha : raw41993step3 = raw41993step2 := by apply Matrix.ext; unfold raw41993step3 raw41993step2; decide +kernel
      have hl : raw41993step2Labels = labelEmbedding9 ∘ raw41993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41993step2 raw41993step2Labels raw41993step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw41994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41994Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41994step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41994step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41994step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41994 raw41994Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw41994 raw41994Labels = mixedMoment B raw41994step0 raw41994step0Labels := by
      have ha : raw41994step0 = (fun i j => raw41994 (permutation250 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41994step0 raw41994; decide +kernel
      have hl : raw41994step0Labels = raw41994Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41994 raw41994Labels permutation250 permutation4
    mixedMoment B raw41994step0 raw41994step0Labels = mixedMoment B raw41994step1 raw41994step1Labels := by
      have ha : raw41994step1 = -raw41994step0 := by apply Matrix.ext; change ∀ i j, raw41994step1 i j = -(raw41994step0 i j); unfold raw41994step1 raw41994step0; decide +kernel
      have hl : raw41994step1Labels = raw41994step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41994step1 raw41994step1Labels = mixedMoment B raw41994step2 raw41994step2Labels := by
      have ha : raw41994step2 = raw41994step1 := by apply Matrix.ext; unfold raw41994step2 raw41994step1; decide +kernel
      have hl : raw41994step1Labels = labelEmbedding1 ∘ raw41994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41994step1 raw41994step1Labels raw41994step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw41995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw41995Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41995step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41995step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41995step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41995 raw41995Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw41995 raw41995Labels = mixedMoment B raw41995step0 raw41995step0Labels := by
      have ha : raw41995step0 = (fun i j => raw41995 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41995step0 raw41995; decide +kernel
      have hl : raw41995step0Labels = raw41995Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41995 raw41995Labels permutation170 permutation5
    mixedMoment B raw41995step0 raw41995step0Labels = mixedMoment B raw41995step1 raw41995step1Labels := by
      have ha : raw41995step1 = -raw41995step0 := by apply Matrix.ext; change ∀ i j, raw41995step1 i j = -(raw41995step0 i j); unfold raw41995step1 raw41995step0; decide +kernel
      have hl : raw41995step1Labels = raw41995step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41995step1 raw41995step1Labels = mixedMoment B raw41995step2 raw41995step2Labels := by
      have ha : raw41995step2 = raw41995step1 := by apply Matrix.ext; unfold raw41995step2 raw41995step1; decide +kernel
      have hl : raw41995step1Labels = labelEmbedding9 ∘ raw41995step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41995step1 raw41995step1Labels raw41995step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw41996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41996Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw41996step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41996step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw41996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41996 raw41996Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw41996 raw41996Labels = mixedMoment B raw41996step0 raw41996step0Labels := by
      have ha : raw41996step0 = (fun i j => raw41996 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41996step0 raw41996; decide +kernel
      have hl : raw41996step0Labels = raw41996Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41996 raw41996Labels permutation212 permutation4
    mixedMoment B raw41996step0 raw41996step0Labels = mixedMoment B raw41996step1 raw41996step1Labels := by
      have ha : raw41996step1 = -raw41996step0 := by apply Matrix.ext; change ∀ i j, raw41996step1 i j = -(raw41996step0 i j); unfold raw41996step1 raw41996step0; decide +kernel
      have hl : raw41996step1Labels = raw41996step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41996step1 raw41996step1Labels = mixedMoment B raw41996step2 raw41996step2Labels := by
      have ha : raw41996step2 = raw41996step1 := by apply Matrix.ext; unfold raw41996step2 raw41996step1; decide +kernel
      have hl : raw41996step1Labels = labelEmbedding1 ∘ raw41996step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41996step1 raw41996step1Labels raw41996step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw41997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw41997Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw41997step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41997step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41997step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw41997step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41997 raw41997Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw41997 raw41997Labels = mixedMoment B raw41997step0 raw41997step0Labels := by
      have ha : raw41997step0 = (fun i j => raw41997 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41997step0 raw41997; decide +kernel
      have hl : raw41997step0Labels = raw41997Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41997 raw41997Labels permutation160 permutation5
    mixedMoment B raw41997step0 raw41997step0Labels = mixedMoment B raw41997step1 raw41997step1Labels := by
      have ha : raw41997step1 = -raw41997step0 := by apply Matrix.ext; change ∀ i j, raw41997step1 i j = -(raw41997step0 i j); unfold raw41997step1 raw41997step0; decide +kernel
      have hl : raw41997step1Labels = raw41997step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41997step1 raw41997step1Labels = mixedMoment B raw41997step2 raw41997step2Labels := by
      have ha : raw41997step2 = raw41997step1 := by apply Matrix.ext; unfold raw41997step2 raw41997step1; decide +kernel
      have hl : raw41997step1Labels = labelEmbedding9 ∘ raw41997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41997step1 raw41997step1Labels raw41997step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw41998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41998Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw41998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw41998step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw41998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical41998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41998 raw41998Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw41998 raw41998Labels = mixedMoment B raw41998step0 raw41998step0Labels := by
      have ha : raw41998step0 = (fun i j => raw41998 (permutation203 i) (permutation4 j)) := by apply Matrix.ext; unfold raw41998step0 raw41998; decide +kernel
      have hl : raw41998step0Labels = raw41998Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41998 raw41998Labels permutation203 permutation4
    mixedMoment B raw41998step0 raw41998step0Labels = mixedMoment B raw41998step1 raw41998step1Labels := by
      have ha : raw41998step1 = -raw41998step0 := by apply Matrix.ext; change ∀ i j, raw41998step1 i j = -(raw41998step0 i j); unfold raw41998step1 raw41998step0; decide +kernel
      have hl : raw41998step1Labels = raw41998step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41998step1 raw41998step1Labels = mixedMoment B raw41998step2 raw41998step2Labels := by
      have ha : raw41998step2 = raw41998step1 := by apply Matrix.ext; unfold raw41998step2 raw41998step1; decide +kernel
      have hl : raw41998step1Labels = labelEmbedding1 ∘ raw41998step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41998step1 raw41998step1Labels raw41998step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw41999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw41999Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw41999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw41999step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41999step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw41999step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw41999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical41999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw41999 raw41999Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw41999 raw41999Labels = mixedMoment B raw41999step0 raw41999step0Labels := by
      have ha : raw41999step0 = (fun i j => raw41999 (permutation158 i) (permutation5 j)) := by apply Matrix.ext; unfold raw41999step0 raw41999; decide +kernel
      have hl : raw41999step0Labels = raw41999Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw41999 raw41999Labels permutation158 permutation5
    mixedMoment B raw41999step0 raw41999step0Labels = mixedMoment B raw41999step1 raw41999step1Labels := by
      have ha : raw41999step1 = -raw41999step0 := by apply Matrix.ext; change ∀ i j, raw41999step1 i j = -(raw41999step0 i j); unfold raw41999step1 raw41999step0; decide +kernel
      have hl : raw41999step1Labels = raw41999step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw41999step1 raw41999step1Labels = mixedMoment B raw41999step2 raw41999step2Labels := by
      have ha : raw41999step2 = raw41999step1 := by apply Matrix.ext; unfold raw41999step2 raw41999step1; decide +kernel
      have hl : raw41999step1Labels = labelEmbedding9 ∘ raw41999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw41999step1 raw41999step1Labels raw41999step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw42000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42000Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42000step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42000step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42000 raw42000Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw42000 raw42000Labels = mixedMoment B raw42000step0 raw42000step0Labels := by
      have ha : raw42000step0 = (fun i j => raw42000 (permutation213 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42000step0 raw42000; decide +kernel
      have hl : raw42000step0Labels = raw42000Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42000 raw42000Labels permutation213 permutation4
    mixedMoment B raw42000step0 raw42000step0Labels = mixedMoment B raw42000step1 raw42000step1Labels := by
      have ha : raw42000step1 = -raw42000step0 := by apply Matrix.ext; change ∀ i j, raw42000step1 i j = -(raw42000step0 i j); unfold raw42000step1 raw42000step0; decide +kernel
      have hl : raw42000step1Labels = raw42000step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42000step1 raw42000step1Labels = mixedMoment B raw42000step2 raw42000step2Labels := by
      have ha : raw42000step2 = raw42000step1 := by apply Matrix.ext; unfold raw42000step2 raw42000step1; decide +kernel
      have hl : raw42000step1Labels = labelEmbedding1 ∘ raw42000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42000step1 raw42000step1Labels raw42000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw42001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42001Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42001step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42001step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42001step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42001step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42001 raw42001Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42001 raw42001Labels = mixedMoment B raw42001step0 raw42001step0Labels := by
      have ha : raw42001step0 = (fun i j => raw42001 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42001step0 raw42001; decide +kernel
      have hl : raw42001step0Labels = raw42001Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42001 raw42001Labels permutation161 permutation5
    mixedMoment B raw42001step0 raw42001step0Labels = mixedMoment B raw42001step1 raw42001step1Labels := by
      have ha : raw42001step1 = -raw42001step0 := by apply Matrix.ext; change ∀ i j, raw42001step1 i j = -(raw42001step0 i j); unfold raw42001step1 raw42001step0; decide +kernel
      have hl : raw42001step1Labels = raw42001step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42001step1 raw42001step1Labels = mixedMoment B raw42001step2 raw42001step2Labels := by
      have ha : raw42001step2 = raw42001step1 := by apply Matrix.ext; unfold raw42001step2 raw42001step1; decide +kernel
      have hl : raw42001step1Labels = labelEmbedding9 ∘ raw42001step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42001step1 raw42001step1Labels raw42001step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw42002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42002Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42002step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42002step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42002step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42002step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42002step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42002 raw42002Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw42002 raw42002Labels = mixedMoment B raw42002step0 raw42002step0Labels := by
      have hz : ∀ j, raw42002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42002step0 = (fun i j => raw42002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42002step0 raw42002; decide +kernel
      have hl : raw42002step0Labels = raw42002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42002 raw42002Labels permutation434 hz
    mixedMoment B raw42002step0 raw42002step0Labels = mixedMoment B raw42002step1 raw42002step1Labels := by
      have hz : ∀ j, raw42002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42002step1 = (fun i j => raw42002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42002step1 raw42002step0; decide +kernel
      have hl : raw42002step1Labels = raw42002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42002step0 raw42002step0Labels permutation80 hz
    mixedMoment B raw42002step1 raw42002step1Labels = mixedMoment B raw42002step2 raw42002step2Labels := by
      have ha : raw42002step2 = (fun i j => raw42002step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42002step2 raw42002step1; decide +kernel
      have hl : raw42002step2Labels = raw42002step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42002step1 raw42002step1Labels permutation10 permutation4
    mixedMoment B raw42002step2 raw42002step2Labels = mixedMoment B raw42002step3 raw42002step3Labels := by
      have ha : raw42002step3 = -raw42002step2 := by apply Matrix.ext; change ∀ i j, raw42002step3 i j = -(raw42002step2 i j); unfold raw42002step3 raw42002step2; decide +kernel
      have hl : raw42002step3Labels = raw42002step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42002step3 raw42002step3Labels = mixedMoment B raw42002step4 raw42002step4Labels := by
      have ha : raw42002step4 = raw42002step3 := by apply Matrix.ext; unfold raw42002step4 raw42002step3; decide +kernel
      have hl : raw42002step3Labels = labelEmbedding1 ∘ raw42002step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42002step3 raw42002step3Labels raw42002step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw42003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42003Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42003step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -2, 0]]
def raw42003step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw42003step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42003step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42003step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42003step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42003step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42003 raw42003Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw42003 raw42003Labels = mixedMoment B raw42003step0 raw42003step0Labels := by
      have hz : ∀ j, raw42003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42003step0 = (fun i j => raw42003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42003step0 raw42003; decide +kernel
      have hl : raw42003step0Labels = raw42003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42003 raw42003Labels permutation434 hz
    mixedMoment B raw42003step0 raw42003step0Labels = mixedMoment B raw42003step1 raw42003step1Labels := by
      have hz : ∀ j, raw42003step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42003step1 = (fun i j => raw42003step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42003step1 raw42003step0; decide +kernel
      have hl : raw42003step1Labels = raw42003step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42003step0 raw42003step0Labels permutation80 hz
    mixedMoment B raw42003step1 raw42003step1Labels = mixedMoment B raw42003step2 raw42003step2Labels := by
      have ha : raw42003step2 = (fun i j => raw42003step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42003step2 raw42003step1; decide +kernel
      have hl : raw42003step2Labels = raw42003step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42003step1 raw42003step1Labels permutation10 permutation5
    mixedMoment B raw42003step2 raw42003step2Labels = mixedMoment B raw42003step3 raw42003step3Labels := by
      have ha : raw42003step3 = -raw42003step2 := by apply Matrix.ext; change ∀ i j, raw42003step3 i j = -(raw42003step2 i j); unfold raw42003step3 raw42003step2; decide +kernel
      have hl : raw42003step3Labels = raw42003step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42003step3 raw42003step3Labels = mixedMoment B raw42003step4 raw42003step4Labels := by
      have ha : raw42003step4 = raw42003step3 := by apply Matrix.ext; unfold raw42003step4 raw42003step3; decide +kernel
      have hl : raw42003step3Labels = labelEmbedding9 ∘ raw42003step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42003step3 raw42003step3Labels raw42003step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw42004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42004Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42004step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42004step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42004step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42004step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42004step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42004step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42004step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42004step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42004 raw42004Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw42004 raw42004Labels = mixedMoment B raw42004step0 raw42004step0Labels := by
      have hz : ∀ j, raw42004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42004step0 = (fun i j => raw42004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42004step0 raw42004; decide +kernel
      have hl : raw42004step0Labels = raw42004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42004 raw42004Labels permutation434 hz
    mixedMoment B raw42004step0 raw42004step0Labels = mixedMoment B raw42004step1 raw42004step1Labels := by
      have hz : ∀ j, raw42004step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42004step1 = (fun i j => raw42004step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42004step1 raw42004step0; decide +kernel
      have hl : raw42004step1Labels = raw42004step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42004step0 raw42004step0Labels permutation80 hz
    mixedMoment B raw42004step1 raw42004step1Labels = mixedMoment B raw42004step2 raw42004step2Labels := by
      have ha : raw42004step2 = (fun i j => raw42004step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42004step2 raw42004step1; decide +kernel
      have hl : raw42004step2Labels = raw42004step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42004step1 raw42004step1Labels permutation13 permutation4
    mixedMoment B raw42004step2 raw42004step2Labels = mixedMoment B raw42004step3 raw42004step3Labels := by
      have ha : raw42004step3 = -raw42004step2 := by apply Matrix.ext; change ∀ i j, raw42004step3 i j = -(raw42004step2 i j); unfold raw42004step3 raw42004step2; decide +kernel
      have hl : raw42004step3Labels = raw42004step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42004step3 raw42004step3Labels = mixedMoment B raw42004step4 raw42004step4Labels := by
      have ha : raw42004step4 = raw42004step3 := by apply Matrix.ext; unfold raw42004step4 raw42004step3; decide +kernel
      have hl : raw42004step3Labels = labelEmbedding1 ∘ raw42004step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42004step3 raw42004step3Labels raw42004step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw42005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42005Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42005step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1]]
def raw42005step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42005step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42005step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42005step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42005step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42005step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42005step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42005 raw42005Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw42005 raw42005Labels = mixedMoment B raw42005step0 raw42005step0Labels := by
      have hz : ∀ j, raw42005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42005step0 = (fun i j => raw42005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42005step0 raw42005; decide +kernel
      have hl : raw42005step0Labels = raw42005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42005 raw42005Labels permutation434 hz
    mixedMoment B raw42005step0 raw42005step0Labels = mixedMoment B raw42005step1 raw42005step1Labels := by
      have hz : ∀ j, raw42005step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42005step1 = (fun i j => raw42005step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42005step1 raw42005step0; decide +kernel
      have hl : raw42005step1Labels = raw42005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42005step0 raw42005step0Labels permutation80 hz
    mixedMoment B raw42005step1 raw42005step1Labels = mixedMoment B raw42005step2 raw42005step2Labels := by
      have ha : raw42005step2 = (fun i j => raw42005step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42005step2 raw42005step1; decide +kernel
      have hl : raw42005step2Labels = raw42005step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42005step1 raw42005step1Labels permutation8 permutation5
    mixedMoment B raw42005step2 raw42005step2Labels = mixedMoment B raw42005step3 raw42005step3Labels := by
      have ha : raw42005step3 = -raw42005step2 := by apply Matrix.ext; change ∀ i j, raw42005step3 i j = -(raw42005step2 i j); unfold raw42005step3 raw42005step2; decide +kernel
      have hl : raw42005step3Labels = raw42005step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42005step3 raw42005step3Labels = mixedMoment B raw42005step4 raw42005step4Labels := by
      have ha : raw42005step4 = raw42005step3 := by apply Matrix.ext; unfold raw42005step4 raw42005step3; decide +kernel
      have hl : raw42005step3Labels = labelEmbedding9 ∘ raw42005step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42005step3 raw42005step3Labels raw42005step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw42006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42006Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42006step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw42006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42006step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42006step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42006step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42006step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42006step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42006 raw42006Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw42006 raw42006Labels = mixedMoment B raw42006step0 raw42006step0Labels := by
      have hz : ∀ j, raw42006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42006step0 = (fun i j => raw42006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42006step0 raw42006; decide +kernel
      have hl : raw42006step0Labels = raw42006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42006 raw42006Labels permutation434 hz
    mixedMoment B raw42006step0 raw42006step0Labels = mixedMoment B raw42006step1 raw42006step1Labels := by
      have hz : ∀ j, raw42006step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42006step1 = (fun i j => raw42006step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42006step1 raw42006step0; decide +kernel
      have hl : raw42006step1Labels = raw42006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42006step0 raw42006step0Labels permutation80 hz
    mixedMoment B raw42006step1 raw42006step1Labels = mixedMoment B raw42006step2 raw42006step2Labels := by
      have ha : raw42006step2 = (fun i j => raw42006step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42006step2 raw42006step1; decide +kernel
      have hl : raw42006step2Labels = raw42006step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42006step1 raw42006step1Labels permutation12 permutation4
    mixedMoment B raw42006step2 raw42006step2Labels = mixedMoment B raw42006step3 raw42006step3Labels := by
      have ha : raw42006step3 = -raw42006step2 := by apply Matrix.ext; change ∀ i j, raw42006step3 i j = -(raw42006step2 i j); unfold raw42006step3 raw42006step2; decide +kernel
      have hl : raw42006step3Labels = raw42006step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42006step3 raw42006step3Labels = mixedMoment B raw42006step4 raw42006step4Labels := by
      have ha : raw42006step4 = raw42006step3 := by apply Matrix.ext; unfold raw42006step4 raw42006step3; decide +kernel
      have hl : raw42006step3Labels = labelEmbedding1 ∘ raw42006step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42006step3 raw42006step3Labels raw42006step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw42007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42007Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42007step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, -2, 1], ![2, 0, -2]]
def raw42007step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42007step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42007step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42007step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42007step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42007step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42007 raw42007Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42007 raw42007Labels = mixedMoment B raw42007step0 raw42007step0Labels := by
      have hz : ∀ j, raw42007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42007step0 = (fun i j => raw42007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42007step0 raw42007; decide +kernel
      have hl : raw42007step0Labels = raw42007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42007 raw42007Labels permutation434 hz
    mixedMoment B raw42007step0 raw42007step0Labels = mixedMoment B raw42007step1 raw42007step1Labels := by
      have hz : ∀ j, raw42007step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42007step1 = (fun i j => raw42007step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42007step1 raw42007step0; decide +kernel
      have hl : raw42007step1Labels = raw42007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42007step0 raw42007step0Labels permutation80 hz
    mixedMoment B raw42007step1 raw42007step1Labels = mixedMoment B raw42007step2 raw42007step2Labels := by
      have ha : raw42007step2 = (fun i j => raw42007step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42007step2 raw42007step1; decide +kernel
      have hl : raw42007step2Labels = raw42007step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42007step1 raw42007step1Labels permutation12 permutation5
    mixedMoment B raw42007step2 raw42007step2Labels = mixedMoment B raw42007step3 raw42007step3Labels := by
      have ha : raw42007step3 = -raw42007step2 := by apply Matrix.ext; change ∀ i j, raw42007step3 i j = -(raw42007step2 i j); unfold raw42007step3 raw42007step2; decide +kernel
      have hl : raw42007step3Labels = raw42007step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42007step3 raw42007step3Labels = mixedMoment B raw42007step4 raw42007step4Labels := by
      have ha : raw42007step4 = raw42007step3 := by apply Matrix.ext; unfold raw42007step4 raw42007step3; decide +kernel
      have hl : raw42007step3Labels = labelEmbedding9 ∘ raw42007step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42007step3 raw42007step3Labels raw42007step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw42008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42008Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42008step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42008step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42008step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42008step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42008 raw42008Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw42008 raw42008Labels = mixedMoment B raw42008step0 raw42008step0Labels := by
      have hz : ∀ j, raw42008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42008step0 = (fun i j => raw42008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42008step0 raw42008; decide +kernel
      have hl : raw42008step0Labels = raw42008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42008 raw42008Labels permutation346 hz
    mixedMoment B raw42008step0 raw42008step0Labels = mixedMoment B raw42008step1 raw42008step1Labels := by
      have ha : raw42008step1 = (fun i j => raw42008step0 (permutation55 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42008step1 raw42008step0; decide +kernel
      have hl : raw42008step1Labels = raw42008step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42008step0 raw42008step0Labels permutation55 permutation4
    mixedMoment B raw42008step1 raw42008step1Labels = mixedMoment B raw42008step2 raw42008step2Labels := by
      have ha : raw42008step2 = -raw42008step1 := by apply Matrix.ext; change ∀ i j, raw42008step2 i j = -(raw42008step1 i j); unfold raw42008step2 raw42008step1; decide +kernel
      have hl : raw42008step2Labels = raw42008step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42008step2 raw42008step2Labels = mixedMoment B raw42008step3 raw42008step3Labels := by
      have ha : raw42008step3 = raw42008step2 := by apply Matrix.ext; unfold raw42008step3 raw42008step2; decide +kernel
      have hl : raw42008step2Labels = labelEmbedding1 ∘ raw42008step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42008step2 raw42008step2Labels raw42008step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw42009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42009Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42009step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42009step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42009step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42009step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42009step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42009step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42009 raw42009Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42009 raw42009Labels = mixedMoment B raw42009step0 raw42009step0Labels := by
      have hz : ∀ j, raw42009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42009step0 = (fun i j => raw42009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42009step0 raw42009; decide +kernel
      have hl : raw42009step0Labels = raw42009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42009 raw42009Labels permutation346 hz
    mixedMoment B raw42009step0 raw42009step0Labels = mixedMoment B raw42009step1 raw42009step1Labels := by
      have ha : raw42009step1 = (fun i j => raw42009step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42009step1 raw42009step0; decide +kernel
      have hl : raw42009step1Labels = raw42009step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42009step0 raw42009step0Labels permutation50 permutation5
    mixedMoment B raw42009step1 raw42009step1Labels = mixedMoment B raw42009step2 raw42009step2Labels := by
      have ha : raw42009step2 = -raw42009step1 := by apply Matrix.ext; change ∀ i j, raw42009step2 i j = -(raw42009step1 i j); unfold raw42009step2 raw42009step1; decide +kernel
      have hl : raw42009step2Labels = raw42009step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42009step2 raw42009step2Labels = mixedMoment B raw42009step3 raw42009step3Labels := by
      have ha : raw42009step3 = raw42009step2 := by apply Matrix.ext; unfold raw42009step3 raw42009step2; decide +kernel
      have hl : raw42009step2Labels = labelEmbedding9 ∘ raw42009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42009step2 raw42009step2Labels raw42009step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw42010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42010Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42010step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42010step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42010step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42010 raw42010Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw42010 raw42010Labels = mixedMoment B raw42010step0 raw42010step0Labels := by
      have hz : ∀ j, raw42010 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42010step0 = (fun i j => raw42010 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42010step0 raw42010; decide +kernel
      have hl : raw42010step0Labels = raw42010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42010 raw42010Labels permutation346 hz
    mixedMoment B raw42010step0 raw42010step0Labels = mixedMoment B raw42010step1 raw42010step1Labels := by
      have ha : raw42010step1 = (fun i j => raw42010step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42010step1 raw42010step0; decide +kernel
      have hl : raw42010step1Labels = raw42010step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42010step0 raw42010step0Labels permutation40 permutation4
    mixedMoment B raw42010step1 raw42010step1Labels = mixedMoment B raw42010step2 raw42010step2Labels := by
      have ha : raw42010step2 = -raw42010step1 := by apply Matrix.ext; change ∀ i j, raw42010step2 i j = -(raw42010step1 i j); unfold raw42010step2 raw42010step1; decide +kernel
      have hl : raw42010step2Labels = raw42010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42010step2 raw42010step2Labels = mixedMoment B raw42010step3 raw42010step3Labels := by
      have ha : raw42010step3 = raw42010step2 := by apply Matrix.ext; unfold raw42010step3 raw42010step2; decide +kernel
      have hl : raw42010step2Labels = labelEmbedding1 ∘ raw42010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42010step2 raw42010step2Labels raw42010step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw42011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42011Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42011step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42011step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42011step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42011step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42011step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42011 raw42011Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42011 raw42011Labels = mixedMoment B raw42011step0 raw42011step0Labels := by
      have hz : ∀ j, raw42011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42011step0 = (fun i j => raw42011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42011step0 raw42011; decide +kernel
      have hl : raw42011step0Labels = raw42011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42011 raw42011Labels permutation346 hz
    mixedMoment B raw42011step0 raw42011step0Labels = mixedMoment B raw42011step1 raw42011step1Labels := by
      have ha : raw42011step1 = (fun i j => raw42011step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42011step1 raw42011step0; decide +kernel
      have hl : raw42011step1Labels = raw42011step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42011step0 raw42011step0Labels permutation40 permutation5
    mixedMoment B raw42011step1 raw42011step1Labels = mixedMoment B raw42011step2 raw42011step2Labels := by
      have ha : raw42011step2 = -raw42011step1 := by apply Matrix.ext; change ∀ i j, raw42011step2 i j = -(raw42011step1 i j); unfold raw42011step2 raw42011step1; decide +kernel
      have hl : raw42011step2Labels = raw42011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42011step2 raw42011step2Labels = mixedMoment B raw42011step3 raw42011step3Labels := by
      have ha : raw42011step3 = raw42011step2 := by apply Matrix.ext; unfold raw42011step3 raw42011step2; decide +kernel
      have hl : raw42011step2Labels = labelEmbedding9 ∘ raw42011step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42011step2 raw42011step2Labels raw42011step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw42012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42012Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42012step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42012step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42012step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42012 raw42012Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw42012 raw42012Labels = mixedMoment B raw42012step0 raw42012step0Labels := by
      have hz : ∀ j, raw42012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42012step0 = (fun i j => raw42012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42012step0 raw42012; decide +kernel
      have hl : raw42012step0Labels = raw42012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42012 raw42012Labels permutation346 hz
    mixedMoment B raw42012step0 raw42012step0Labels = mixedMoment B raw42012step1 raw42012step1Labels := by
      have ha : raw42012step1 = (fun i j => raw42012step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42012step1 raw42012step0; decide +kernel
      have hl : raw42012step1Labels = raw42012step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42012step0 raw42012step0Labels permutation41 permutation4
    mixedMoment B raw42012step1 raw42012step1Labels = mixedMoment B raw42012step2 raw42012step2Labels := by
      have ha : raw42012step2 = -raw42012step1 := by apply Matrix.ext; change ∀ i j, raw42012step2 i j = -(raw42012step1 i j); unfold raw42012step2 raw42012step1; decide +kernel
      have hl : raw42012step2Labels = raw42012step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42012step2 raw42012step2Labels = mixedMoment B raw42012step3 raw42012step3Labels := by
      have ha : raw42012step3 = raw42012step2 := by apply Matrix.ext; unfold raw42012step3 raw42012step2; decide +kernel
      have hl : raw42012step2Labels = labelEmbedding1 ∘ raw42012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42012step2 raw42012step2Labels raw42012step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw42013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42013Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42013step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42013step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42013step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42013step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42013step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42013 raw42013Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw42013 raw42013Labels = mixedMoment B raw42013step0 raw42013step0Labels := by
      have hz : ∀ j, raw42013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42013step0 = (fun i j => raw42013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42013step0 raw42013; decide +kernel
      have hl : raw42013step0Labels = raw42013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42013 raw42013Labels permutation346 hz
    mixedMoment B raw42013step0 raw42013step0Labels = mixedMoment B raw42013step1 raw42013step1Labels := by
      have ha : raw42013step1 = (fun i j => raw42013step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42013step1 raw42013step0; decide +kernel
      have hl : raw42013step1Labels = raw42013step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42013step0 raw42013step0Labels permutation38 permutation5
    mixedMoment B raw42013step1 raw42013step1Labels = mixedMoment B raw42013step2 raw42013step2Labels := by
      have ha : raw42013step2 = -raw42013step1 := by apply Matrix.ext; change ∀ i j, raw42013step2 i j = -(raw42013step1 i j); unfold raw42013step2 raw42013step1; decide +kernel
      have hl : raw42013step2Labels = raw42013step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42013step2 raw42013step2Labels = mixedMoment B raw42013step3 raw42013step3Labels := by
      have ha : raw42013step3 = raw42013step2 := by apply Matrix.ext; unfold raw42013step3 raw42013step2; decide +kernel
      have hl : raw42013step2Labels = labelEmbedding9 ∘ raw42013step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42013step2 raw42013step2Labels raw42013step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw42014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42014Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42014step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42014step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42014 raw42014Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw42014 raw42014Labels = mixedMoment B raw42014step0 raw42014step0Labels := by
      have ha : raw42014step0 = (fun i j => raw42014 (permutation217 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42014step0 raw42014; decide +kernel
      have hl : raw42014step0Labels = raw42014Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42014 raw42014Labels permutation217 permutation4
    mixedMoment B raw42014step0 raw42014step0Labels = mixedMoment B raw42014step1 raw42014step1Labels := by
      have ha : raw42014step1 = -raw42014step0 := by apply Matrix.ext; change ∀ i j, raw42014step1 i j = -(raw42014step0 i j); unfold raw42014step1 raw42014step0; decide +kernel
      have hl : raw42014step1Labels = raw42014step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42014step1 raw42014step1Labels = mixedMoment B raw42014step2 raw42014step2Labels := by
      have ha : raw42014step2 = raw42014step1 := by apply Matrix.ext; unfold raw42014step2 raw42014step1; decide +kernel
      have hl : raw42014step1Labels = labelEmbedding1 ∘ raw42014step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42014step1 raw42014step1Labels raw42014step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw42015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42015Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42015step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42015step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42015step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42015step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42015 raw42015Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw42015 raw42015Labels = mixedMoment B raw42015step0 raw42015step0Labels := by
      have ha : raw42015step0 = (fun i j => raw42015 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42015step0 raw42015; decide +kernel
      have hl : raw42015step0Labels = raw42015Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42015 raw42015Labels permutation212 permutation5
    mixedMoment B raw42015step0 raw42015step0Labels = mixedMoment B raw42015step1 raw42015step1Labels := by
      have ha : raw42015step1 = -raw42015step0 := by apply Matrix.ext; change ∀ i j, raw42015step1 i j = -(raw42015step0 i j); unfold raw42015step1 raw42015step0; decide +kernel
      have hl : raw42015step1Labels = raw42015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42015step1 raw42015step1Labels = mixedMoment B raw42015step2 raw42015step2Labels := by
      have ha : raw42015step2 = raw42015step1 := by apply Matrix.ext; unfold raw42015step2 raw42015step1; decide +kernel
      have hl : raw42015step1Labels = labelEmbedding9 ∘ raw42015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42015step1 raw42015step1Labels raw42015step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw42016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42016Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42016step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-2, -1, 3]]
def raw42016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42016step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42016step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42016step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42016 raw42016Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw42016 raw42016Labels = mixedMoment B raw42016step0 raw42016step0Labels := by
      have hz : ∀ j, raw42016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42016step0 = (fun i j => raw42016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42016step0 raw42016; decide +kernel
      have hl : raw42016step0Labels = raw42016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42016 raw42016Labels permutation434 hz
    mixedMoment B raw42016step0 raw42016step0Labels = mixedMoment B raw42016step1 raw42016step1Labels := by
      have hz : ∀ j, raw42016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42016step1 = (fun i j => raw42016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42016step1 raw42016step0; decide +kernel
      have hl : raw42016step1Labels = raw42016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42016step0 raw42016step0Labels permutation80 hz
    mixedMoment B raw42016step1 raw42016step1Labels = mixedMoment B raw42016step2 raw42016step2Labels := by
      have ha : raw42016step2 = (fun i j => raw42016step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42016step2 raw42016step1; decide +kernel
      have hl : raw42016step2Labels = raw42016step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42016step1 raw42016step1Labels permutation13 permutation4
    mixedMoment B raw42016step2 raw42016step2Labels = mixedMoment B raw42016step3 raw42016step3Labels := by
      have ha : raw42016step3 = -raw42016step2 := by apply Matrix.ext; change ∀ i j, raw42016step3 i j = -(raw42016step2 i j); unfold raw42016step3 raw42016step2; decide +kernel
      have hl : raw42016step3Labels = raw42016step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42016step3 raw42016step3Labels = mixedMoment B raw42016step4 raw42016step4Labels := by
      have ha : raw42016step4 = raw42016step3 := by apply Matrix.ext; unfold raw42016step4 raw42016step3; decide +kernel
      have hl : raw42016step3Labels = labelEmbedding1 ∘ raw42016step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42016step3 raw42016step3Labels raw42016step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw42017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42017Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42017step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, -1, 0], ![2, 0, -2]]
def raw42017step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw42017step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42017step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42017 raw42017Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw42017 raw42017Labels = mixedMoment B raw42017step0 raw42017step0Labels := by
      have hz : ∀ j, raw42017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42017step0 = (fun i j => raw42017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42017step0 raw42017; decide +kernel
      have hl : raw42017step0Labels = raw42017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42017 raw42017Labels permutation434 hz
    mixedMoment B raw42017step0 raw42017step0Labels = mixedMoment B raw42017step1 raw42017step1Labels := by
      have hz : ∀ j, raw42017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42017step1 = (fun i j => raw42017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42017step1 raw42017step0; decide +kernel
      have hl : raw42017step1Labels = raw42017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42017step0 raw42017step0Labels permutation80 hz
    mixedMoment B raw42017step1 raw42017step1Labels = mixedMoment B raw42017step2 raw42017step2Labels := by
      have ha : raw42017step2 = (fun i j => raw42017step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42017step2 raw42017step1; decide +kernel
      have hl : raw42017step2Labels = raw42017step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42017step1 raw42017step1Labels permutation16 permutation6
    mixedMoment B raw42017step2 raw42017step2Labels = mixedMoment B raw42017step3 raw42017step3Labels := by
      have ha : raw42017step3 = -raw42017step2 := by apply Matrix.ext; change ∀ i j, raw42017step3 i j = -(raw42017step2 i j); unfold raw42017step3 raw42017step2; decide +kernel
      have hl : raw42017step3Labels = raw42017step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw42018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42018Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42018step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw42018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42018step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42018step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42018 raw42018Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw42018 raw42018Labels = mixedMoment B raw42018step0 raw42018step0Labels := by
      have hz : ∀ j, raw42018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42018step0 = (fun i j => raw42018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42018step0 raw42018; decide +kernel
      have hl : raw42018step0Labels = raw42018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42018 raw42018Labels permutation346 hz
    mixedMoment B raw42018step0 raw42018step0Labels = mixedMoment B raw42018step1 raw42018step1Labels := by
      have ha : raw42018step1 = (fun i j => raw42018step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42018step1 raw42018step0; decide +kernel
      have hl : raw42018step1Labels = raw42018step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42018step0 raw42018step0Labels permutation41 permutation4
    mixedMoment B raw42018step1 raw42018step1Labels = mixedMoment B raw42018step2 raw42018step2Labels := by
      have ha : raw42018step2 = -raw42018step1 := by apply Matrix.ext; change ∀ i j, raw42018step2 i j = -(raw42018step1 i j); unfold raw42018step2 raw42018step1; decide +kernel
      have hl : raw42018step2Labels = raw42018step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42018step2 raw42018step2Labels = mixedMoment B raw42018step3 raw42018step3Labels := by
      have ha : raw42018step3 = raw42018step2 := by apply Matrix.ext; unfold raw42018step3 raw42018step2; decide +kernel
      have hl : raw42018step2Labels = labelEmbedding1 ∘ raw42018step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42018step2 raw42018step2Labels raw42018step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw42019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42019Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 3, -1], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42019step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw42019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw42019step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42019 raw42019Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw42019 raw42019Labels = mixedMoment B raw42019step0 raw42019step0Labels := by
      have hz : ∀ j, raw42019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42019step0 = (fun i j => raw42019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42019step0 raw42019; decide +kernel
      have hl : raw42019step0Labels = raw42019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42019 raw42019Labels permutation346 hz
    mixedMoment B raw42019step0 raw42019step0Labels = mixedMoment B raw42019step1 raw42019step1Labels := by
      have ha : raw42019step1 = (fun i j => raw42019step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42019step1 raw42019step0; decide +kernel
      have hl : raw42019step1Labels = raw42019step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42019step0 raw42019step0Labels permutation77 permutation6
    mixedMoment B raw42019step1 raw42019step1Labels = mixedMoment B raw42019step2 raw42019step2Labels := by
      have ha : raw42019step2 = -raw42019step1 := by apply Matrix.ext; change ∀ i j, raw42019step2 i j = -(raw42019step1 i j); unfold raw42019step2 raw42019step1; decide +kernel
      have hl : raw42019step2Labels = raw42019step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw42020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42020Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42020step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42020step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42020step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw42020step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42020step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw42020step3Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42020step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw42020step4Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42020step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw42020step5Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42020step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw42020step6Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical42020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42020 raw42020Labels = mixedMoment B node1 node1Labels := by
  calc
    mixedMoment B raw42020 raw42020Labels = mixedMoment B raw42020step0 raw42020step0Labels := by
      have hz : ∀ j, raw42020 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42020step0 = (fun i j => raw42020 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42020step0 raw42020; decide +kernel
      have hl : raw42020step0Labels = raw42020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42020 raw42020Labels permutation520 hz
    mixedMoment B raw42020step0 raw42020step0Labels = mixedMoment B raw42020step1 raw42020step1Labels := by
      have hz : ∀ j, raw42020step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42020step1 = (fun i j => raw42020step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42020step1 raw42020step0; decide +kernel
      have hl : raw42020step1Labels = raw42020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42020step0 raw42020step0Labels permutation104 hz
    mixedMoment B raw42020step1 raw42020step1Labels = mixedMoment B raw42020step2 raw42020step2Labels := by
      have hz : ∀ j, raw42020step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42020step2 = (fun i j => raw42020step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42020step2 raw42020step1; decide +kernel
      have hl : raw42020step2Labels = raw42020step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42020step1 raw42020step1Labels permutation20 hz
    mixedMoment B raw42020step2 raw42020step2Labels = mixedMoment B raw42020step3 raw42020step3Labels := by
      have hz : ∀ i, raw42020step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42020step3 = (fun i j => raw42020step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42020step3 raw42020step2; decide +kernel
      have hl : raw42020step3Labels = (fun j => raw42020step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42020step2 raw42020step2Labels permutation6 hz
    mixedMoment B raw42020step3 raw42020step3Labels = mixedMoment B raw42020step4 raw42020step4Labels := by
      have ha : raw42020step4 = (fun i j => raw42020step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42020step4 raw42020step3; decide +kernel
      have hl : raw42020step4Labels = raw42020step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42020step3 raw42020step3Labels permutation7 permutation0
    mixedMoment B raw42020step4 raw42020step4Labels = mixedMoment B raw42020step5 raw42020step5Labels := by
      have ha : raw42020step5 = -raw42020step4 := by apply Matrix.ext; change ∀ i j, raw42020step5 i j = -(raw42020step4 i j); unfold raw42020step5 raw42020step4; decide +kernel
      have hl : raw42020step5Labels = raw42020step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42020step5 raw42020step5Labels = mixedMoment B raw42020step6 raw42020step6Labels := by
      have ha : raw42020step6 = raw42020step5 := by apply Matrix.ext; unfold raw42020step6 raw42020step5; decide +kernel
      have hl : raw42020step5Labels = labelEmbedding0 ∘ raw42020step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42020step5 raw42020step5Labels raw42020step6Labels labelEmbedding0 hl
    _ = mixedMoment B node1 node1Labels := by rfl

def raw42021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42021Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42021step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42021step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42021step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![3, -3, 0]]
def raw42021step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42021step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw42021step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42021step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw42021step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42021step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw42021step5Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42021step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw42021step6Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical42021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42021 raw42021Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw42021 raw42021Labels = mixedMoment B raw42021step0 raw42021step0Labels := by
      have hz : ∀ j, raw42021 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42021step0 = (fun i j => raw42021 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42021step0 raw42021; decide +kernel
      have hl : raw42021step0Labels = raw42021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42021 raw42021Labels permutation520 hz
    mixedMoment B raw42021step0 raw42021step0Labels = mixedMoment B raw42021step1 raw42021step1Labels := by
      have hz : ∀ j, raw42021step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42021step1 = (fun i j => raw42021step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42021step1 raw42021step0; decide +kernel
      have hl : raw42021step1Labels = raw42021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42021step0 raw42021step0Labels permutation104 hz
    mixedMoment B raw42021step1 raw42021step1Labels = mixedMoment B raw42021step2 raw42021step2Labels := by
      have hz : ∀ j, raw42021step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42021step2 = (fun i j => raw42021step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42021step2 raw42021step1; decide +kernel
      have hl : raw42021step2Labels = raw42021step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42021step1 raw42021step1Labels permutation20 hz
    mixedMoment B raw42021step2 raw42021step2Labels = mixedMoment B raw42021step3 raw42021step3Labels := by
      have hz : ∀ i, raw42021step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42021step3 = (fun i j => raw42021step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42021step3 raw42021step2; decide +kernel
      have hl : raw42021step3Labels = (fun j => raw42021step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42021step2 raw42021step2Labels permutation6 hz
    mixedMoment B raw42021step3 raw42021step3Labels = mixedMoment B raw42021step4 raw42021step4Labels := by
      have ha : raw42021step4 = (fun i j => raw42021step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw42021step4 raw42021step3; decide +kernel
      have hl : raw42021step4Labels = raw42021step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42021step3 raw42021step3Labels permutation7 permutation0
    mixedMoment B raw42021step4 raw42021step4Labels = mixedMoment B raw42021step5 raw42021step5Labels := by
      have ha : raw42021step5 = -raw42021step4 := by apply Matrix.ext; change ∀ i j, raw42021step5 i j = -(raw42021step4 i j); unfold raw42021step5 raw42021step4; decide +kernel
      have hl : raw42021step5Labels = raw42021step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42021step5 raw42021step5Labels = mixedMoment B raw42021step6 raw42021step6Labels := by
      have ha : raw42021step6 = raw42021step5 := by apply Matrix.ext; unfold raw42021step6 raw42021step5; decide +kernel
      have hl : raw42021step5Labels = labelEmbedding3 ∘ raw42021step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42021step5 raw42021step5Labels raw42021step6Labels labelEmbedding3 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw42022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42022Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42022step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42022step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42022step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42022step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42022step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42022 raw42022Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw42022 raw42022Labels = mixedMoment B raw42022step0 raw42022step0Labels := by
      have hz : ∀ j, raw42022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42022step0 = (fun i j => raw42022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42022step0 raw42022; decide +kernel
      have hl : raw42022step0Labels = raw42022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42022 raw42022Labels permutation434 hz
    mixedMoment B raw42022step0 raw42022step0Labels = mixedMoment B raw42022step1 raw42022step1Labels := by
      have hz : ∀ j, raw42022step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42022step1 = (fun i j => raw42022step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42022step1 raw42022step0; decide +kernel
      have hl : raw42022step1Labels = raw42022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42022step0 raw42022step0Labels permutation80 hz
    mixedMoment B raw42022step1 raw42022step1Labels = mixedMoment B raw42022step2 raw42022step2Labels := by
      have ha : raw42022step2 = (fun i j => raw42022step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42022step2 raw42022step1; decide +kernel
      have hl : raw42022step2Labels = raw42022step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42022step1 raw42022step1Labels permutation31 permutation4
    mixedMoment B raw42022step2 raw42022step2Labels = mixedMoment B raw42022step3 raw42022step3Labels := by
      have ha : raw42022step3 = raw42022step2 := by apply Matrix.ext; unfold raw42022step3 raw42022step2; decide +kernel
      have hl : raw42022step2Labels = labelEmbedding1 ∘ raw42022step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42022step2 raw42022step2Labels raw42022step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw42023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42023Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42023step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42023step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42023step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw42023step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42023step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw42023step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42023 raw42023Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw42023 raw42023Labels = mixedMoment B raw42023step0 raw42023step0Labels := by
      have hz : ∀ j, raw42023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42023step0 = (fun i j => raw42023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42023step0 raw42023; decide +kernel
      have hl : raw42023step0Labels = raw42023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42023 raw42023Labels permutation434 hz
    mixedMoment B raw42023step0 raw42023step0Labels = mixedMoment B raw42023step1 raw42023step1Labels := by
      have hz : ∀ j, raw42023step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42023step1 = (fun i j => raw42023step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42023step1 raw42023step0; decide +kernel
      have hl : raw42023step1Labels = raw42023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42023step0 raw42023step0Labels permutation80 hz
    mixedMoment B raw42023step1 raw42023step1Labels = mixedMoment B raw42023step2 raw42023step2Labels := by
      have ha : raw42023step2 = (fun i j => raw42023step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42023step2 raw42023step1; decide +kernel
      have hl : raw42023step2Labels = raw42023step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42023step1 raw42023step1Labels permutation31 permutation5
    mixedMoment B raw42023step2 raw42023step2Labels = mixedMoment B raw42023step3 raw42023step3Labels := by
      have ha : raw42023step3 = raw42023step2 := by apply Matrix.ext; unfold raw42023step3 raw42023step2; decide +kernel
      have hl : raw42023step2Labels = labelEmbedding9 ∘ raw42023step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42023step2 raw42023step2Labels raw42023step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw42024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42024Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42024step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42024step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42024step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw42024step2Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42024step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw42024step3Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical42024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42024 raw42024Labels = mixedMoment B node4 node4Labels := by
  calc
    mixedMoment B raw42024 raw42024Labels = mixedMoment B raw42024step0 raw42024step0Labels := by
      have hz : ∀ j, raw42024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42024step0 = (fun i j => raw42024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42024step0 raw42024; decide +kernel
      have hl : raw42024step0Labels = raw42024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42024 raw42024Labels permutation434 hz
    mixedMoment B raw42024step0 raw42024step0Labels = mixedMoment B raw42024step1 raw42024step1Labels := by
      have hz : ∀ j, raw42024step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42024step1 = (fun i j => raw42024step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42024step1 raw42024step0; decide +kernel
      have hl : raw42024step1Labels = raw42024step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42024step0 raw42024step0Labels permutation80 hz
    mixedMoment B raw42024step1 raw42024step1Labels = mixedMoment B raw42024step2 raw42024step2Labels := by
      have hz : ∀ i, raw42024step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42024step2 = (fun i j => raw42024step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42024step2 raw42024step1; decide +kernel
      have hl : raw42024step2Labels = (fun j => raw42024step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42024step1 raw42024step1Labels permutation6 hz
    mixedMoment B raw42024step2 raw42024step2Labels = mixedMoment B raw42024step3 raw42024step3Labels := by
      have ha : raw42024step3 = raw42024step2 := by apply Matrix.ext; unfold raw42024step3 raw42024step2; decide +kernel
      have hl : raw42024step2Labels = labelEmbedding0 ∘ raw42024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42024step2 raw42024step2Labels raw42024step3Labels labelEmbedding0 hl
    _ = mixedMoment B node4 node4Labels := by rfl

def raw42025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42025Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42025step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42025step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42025step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw42025step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42025step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw42025step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical42025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42025 raw42025Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw42025 raw42025Labels = mixedMoment B raw42025step0 raw42025step0Labels := by
      have hz : ∀ j, raw42025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42025step0 = (fun i j => raw42025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42025step0 raw42025; decide +kernel
      have hl : raw42025step0Labels = raw42025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42025 raw42025Labels permutation434 hz
    mixedMoment B raw42025step0 raw42025step0Labels = mixedMoment B raw42025step1 raw42025step1Labels := by
      have hz : ∀ j, raw42025step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42025step1 = (fun i j => raw42025step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42025step1 raw42025step0; decide +kernel
      have hl : raw42025step1Labels = raw42025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42025step0 raw42025step0Labels permutation80 hz
    mixedMoment B raw42025step1 raw42025step1Labels = mixedMoment B raw42025step2 raw42025step2Labels := by
      have hz : ∀ i, raw42025step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42025step2 = (fun i j => raw42025step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42025step2 raw42025step1; decide +kernel
      have hl : raw42025step2Labels = (fun j => raw42025step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42025step1 raw42025step1Labels permutation6 hz
    mixedMoment B raw42025step2 raw42025step2Labels = mixedMoment B raw42025step3 raw42025step3Labels := by
      have ha : raw42025step3 = raw42025step2 := by apply Matrix.ext; unfold raw42025step3 raw42025step2; decide +kernel
      have hl : raw42025step2Labels = labelEmbedding3 ∘ raw42025step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42025step2 raw42025step2Labels raw42025step3Labels labelEmbedding3 hl
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw42026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42026Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42026step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42026step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42026step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42026step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42026step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42026step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42026step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42026 raw42026Labels = mixedMoment B node4006 node4006Labels := by
  calc
    mixedMoment B raw42026 raw42026Labels = mixedMoment B raw42026step0 raw42026step0Labels := by
      have hz : ∀ j, raw42026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42026step0 = (fun i j => raw42026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42026step0 raw42026; decide +kernel
      have hl : raw42026step0Labels = raw42026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42026 raw42026Labels permutation434 hz
    mixedMoment B raw42026step0 raw42026step0Labels = mixedMoment B raw42026step1 raw42026step1Labels := by
      have hz : ∀ j, raw42026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42026step1 = (fun i j => raw42026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42026step1 raw42026step0; decide +kernel
      have hl : raw42026step1Labels = raw42026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42026step0 raw42026step0Labels permutation80 hz
    mixedMoment B raw42026step1 raw42026step1Labels = mixedMoment B raw42026step2 raw42026step2Labels := by
      have ha : raw42026step2 = (fun i j => raw42026step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42026step2 raw42026step1; decide +kernel
      have hl : raw42026step2Labels = raw42026step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42026step1 raw42026step1Labels permutation31 permutation2
    mixedMoment B raw42026step2 raw42026step2Labels = mixedMoment B raw42026step3 raw42026step3Labels := by
      have ha : raw42026step3 = -raw42026step2 := by apply Matrix.ext; change ∀ i j, raw42026step3 i j = -(raw42026step2 i j); unfold raw42026step3 raw42026step2; decide +kernel
      have hl : raw42026step3Labels = raw42026step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42026step3 raw42026step3Labels = mixedMoment B raw42026step4 raw42026step4Labels := by
      have ha : raw42026step4 = raw42026step3 := by apply Matrix.ext; unfold raw42026step4 raw42026step3; decide +kernel
      have hl : raw42026step3Labels = labelEmbedding1 ∘ raw42026step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42026step3 raw42026step3Labels raw42026step4Labels labelEmbedding1 hl
    _ = mixedMoment B node4006 node4006Labels := by rfl

def raw42027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42027Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42027step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42027step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42027step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42027step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42027 raw42027Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw42027 raw42027Labels = mixedMoment B raw42027step0 raw42027step0Labels := by
      have hz : ∀ j, raw42027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42027step0 = (fun i j => raw42027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42027step0 raw42027; decide +kernel
      have hl : raw42027step0Labels = raw42027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42027 raw42027Labels permutation434 hz
    mixedMoment B raw42027step0 raw42027step0Labels = mixedMoment B raw42027step1 raw42027step1Labels := by
      have hz : ∀ j, raw42027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42027step1 = (fun i j => raw42027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42027step1 raw42027step0; decide +kernel
      have hl : raw42027step1Labels = raw42027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42027step0 raw42027step0Labels permutation80 hz
    mixedMoment B raw42027step1 raw42027step1Labels = mixedMoment B raw42027step2 raw42027step2Labels := by
      have ha : raw42027step2 = (fun i j => raw42027step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42027step2 raw42027step1; decide +kernel
      have hl : raw42027step2Labels = raw42027step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42027step1 raw42027step1Labels permutation8 permutation3
    mixedMoment B raw42027step2 raw42027step2Labels = mixedMoment B raw42027step3 raw42027step3Labels := by
      have ha : raw42027step3 = raw42027step2 := by apply Matrix.ext; unfold raw42027step3 raw42027step2; decide +kernel
      have hl : raw42027step2Labels = labelEmbedding7 ∘ raw42027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42027step2 raw42027step2Labels raw42027step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw42028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42028Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42028step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42028step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42028step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42028step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42028 raw42028Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw42028 raw42028Labels = mixedMoment B raw42028step0 raw42028step0Labels := by
      have hz : ∀ j, raw42028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42028step0 = (fun i j => raw42028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42028step0 raw42028; decide +kernel
      have hl : raw42028step0Labels = raw42028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42028 raw42028Labels permutation434 hz
    mixedMoment B raw42028step0 raw42028step0Labels = mixedMoment B raw42028step1 raw42028step1Labels := by
      have hz : ∀ j, raw42028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42028step1 = (fun i j => raw42028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42028step1 raw42028step0; decide +kernel
      have hl : raw42028step1Labels = raw42028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42028step0 raw42028step0Labels permutation80 hz
    mixedMoment B raw42028step1 raw42028step1Labels = mixedMoment B raw42028step2 raw42028step2Labels := by
      have ha : raw42028step2 = (fun i j => raw42028step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42028step2 raw42028step1; decide +kernel
      have hl : raw42028step2Labels = raw42028step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42028step1 raw42028step1Labels permutation25 permutation4
    mixedMoment B raw42028step2 raw42028step2Labels = mixedMoment B raw42028step3 raw42028step3Labels := by
      have ha : raw42028step3 = raw42028step2 := by apply Matrix.ext; unfold raw42028step3 raw42028step2; decide +kernel
      have hl : raw42028step2Labels = labelEmbedding1 ∘ raw42028step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42028step2 raw42028step2Labels raw42028step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw42029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42029Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42029step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42029step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42029step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42029step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42029step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42029 raw42029Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw42029 raw42029Labels = mixedMoment B raw42029step0 raw42029step0Labels := by
      have hz : ∀ j, raw42029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42029step0 = (fun i j => raw42029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42029step0 raw42029; decide +kernel
      have hl : raw42029step0Labels = raw42029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42029 raw42029Labels permutation434 hz
    mixedMoment B raw42029step0 raw42029step0Labels = mixedMoment B raw42029step1 raw42029step1Labels := by
      have hz : ∀ j, raw42029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42029step1 = (fun i j => raw42029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42029step1 raw42029step0; decide +kernel
      have hl : raw42029step1Labels = raw42029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42029step0 raw42029step0Labels permutation80 hz
    mixedMoment B raw42029step1 raw42029step1Labels = mixedMoment B raw42029step2 raw42029step2Labels := by
      have ha : raw42029step2 = (fun i j => raw42029step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42029step2 raw42029step1; decide +kernel
      have hl : raw42029step2Labels = raw42029step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42029step1 raw42029step1Labels permutation25 permutation4
    mixedMoment B raw42029step2 raw42029step2Labels = mixedMoment B raw42029step3 raw42029step3Labels := by
      have ha : raw42029step3 = raw42029step2 := by apply Matrix.ext; unfold raw42029step3 raw42029step2; decide +kernel
      have hl : raw42029step2Labels = labelEmbedding10 ∘ raw42029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42029step2 raw42029step2Labels raw42029step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw42030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42030Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42030step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42030step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42030step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42030step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42030 raw42030Labels = mixedMoment B node4035 node4035Labels := by
  calc
    mixedMoment B raw42030 raw42030Labels = mixedMoment B raw42030step0 raw42030step0Labels := by
      have hz : ∀ j, raw42030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42030step0 = (fun i j => raw42030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42030step0 raw42030; decide +kernel
      have hl : raw42030step0Labels = raw42030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42030 raw42030Labels permutation346 hz
    mixedMoment B raw42030step0 raw42030step0Labels = mixedMoment B raw42030step1 raw42030step1Labels := by
      have ha : raw42030step1 = (fun i j => raw42030step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42030step1 raw42030step0; decide +kernel
      have hl : raw42030step1Labels = raw42030step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42030step0 raw42030step0Labels permutation151 permutation2
    mixedMoment B raw42030step1 raw42030step1Labels = mixedMoment B raw42030step2 raw42030step2Labels := by
      have ha : raw42030step2 = -raw42030step1 := by apply Matrix.ext; change ∀ i j, raw42030step2 i j = -(raw42030step1 i j); unfold raw42030step2 raw42030step1; decide +kernel
      have hl : raw42030step2Labels = raw42030step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42030step2 raw42030step2Labels = mixedMoment B raw42030step3 raw42030step3Labels := by
      have ha : raw42030step3 = raw42030step2 := by apply Matrix.ext; unfold raw42030step3 raw42030step2; decide +kernel
      have hl : raw42030step2Labels = labelEmbedding1 ∘ raw42030step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42030step2 raw42030step2Labels raw42030step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4035 node4035Labels := by rfl

def raw42031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42031Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42031step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42031step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42031 raw42031Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw42031 raw42031Labels = mixedMoment B raw42031step0 raw42031step0Labels := by
      have hz : ∀ j, raw42031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42031step0 = (fun i j => raw42031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42031step0 raw42031; decide +kernel
      have hl : raw42031step0Labels = raw42031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42031 raw42031Labels permutation346 hz
    mixedMoment B raw42031step0 raw42031step0Labels = mixedMoment B raw42031step1 raw42031step1Labels := by
      have ha : raw42031step1 = (fun i j => raw42031step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42031step1 raw42031step0; decide +kernel
      have hl : raw42031step1Labels = raw42031step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42031step0 raw42031step0Labels permutation32 permutation3
    mixedMoment B raw42031step1 raw42031step1Labels = mixedMoment B raw42031step2 raw42031step2Labels := by
      have ha : raw42031step2 = raw42031step1 := by apply Matrix.ext; unfold raw42031step2 raw42031step1; decide +kernel
      have hl : raw42031step1Labels = labelEmbedding7 ∘ raw42031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42031step1 raw42031step1Labels raw42031step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw42032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42032Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42032step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42032step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42032 raw42032Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw42032 raw42032Labels = mixedMoment B raw42032step0 raw42032step0Labels := by
      have hz : ∀ j, raw42032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42032step0 = (fun i j => raw42032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42032step0 raw42032; decide +kernel
      have hl : raw42032step0Labels = raw42032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42032 raw42032Labels permutation346 hz
    mixedMoment B raw42032step0 raw42032step0Labels = mixedMoment B raw42032step1 raw42032step1Labels := by
      have ha : raw42032step1 = (fun i j => raw42032step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42032step1 raw42032step0; decide +kernel
      have hl : raw42032step1Labels = raw42032step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42032step0 raw42032step0Labels permutation151 permutation2
    mixedMoment B raw42032step1 raw42032step1Labels = mixedMoment B raw42032step2 raw42032step2Labels := by
      have ha : raw42032step2 = -raw42032step1 := by apply Matrix.ext; change ∀ i j, raw42032step2 i j = -(raw42032step1 i j); unfold raw42032step2 raw42032step1; decide +kernel
      have hl : raw42032step2Labels = raw42032step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42032step2 raw42032step2Labels = mixedMoment B raw42032step3 raw42032step3Labels := by
      have ha : raw42032step3 = raw42032step2 := by apply Matrix.ext; unfold raw42032step3 raw42032step2; decide +kernel
      have hl : raw42032step2Labels = labelEmbedding1 ∘ raw42032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42032step2 raw42032step2Labels raw42032step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw42033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42033Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42033step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42033step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42033step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42033 raw42033Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw42033 raw42033Labels = mixedMoment B raw42033step0 raw42033step0Labels := by
      have hz : ∀ j, raw42033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42033step0 = (fun i j => raw42033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42033step0 raw42033; decide +kernel
      have hl : raw42033step0Labels = raw42033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42033 raw42033Labels permutation346 hz
    mixedMoment B raw42033step0 raw42033step0Labels = mixedMoment B raw42033step1 raw42033step1Labels := by
      have ha : raw42033step1 = (fun i j => raw42033step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42033step1 raw42033step0; decide +kernel
      have hl : raw42033step1Labels = raw42033step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42033step0 raw42033step0Labels permutation32 permutation3
    mixedMoment B raw42033step1 raw42033step1Labels = mixedMoment B raw42033step2 raw42033step2Labels := by
      have ha : raw42033step2 = raw42033step1 := by apply Matrix.ext; unfold raw42033step2 raw42033step1; decide +kernel
      have hl : raw42033step1Labels = labelEmbedding7 ∘ raw42033step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42033step1 raw42033step1Labels raw42033step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw42034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42034Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42034step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42034step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42034step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42034step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42034 raw42034Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw42034 raw42034Labels = mixedMoment B raw42034step0 raw42034step0Labels := by
      have hz : ∀ j, raw42034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42034step0 = (fun i j => raw42034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42034step0 raw42034; decide +kernel
      have hl : raw42034step0Labels = raw42034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42034 raw42034Labels permutation346 hz
    mixedMoment B raw42034step0 raw42034step0Labels = mixedMoment B raw42034step1 raw42034step1Labels := by
      have ha : raw42034step1 = (fun i j => raw42034step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42034step1 raw42034step0; decide +kernel
      have hl : raw42034step1Labels = raw42034step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42034step0 raw42034step0Labels permutation151 permutation2
    mixedMoment B raw42034step1 raw42034step1Labels = mixedMoment B raw42034step2 raw42034step2Labels := by
      have ha : raw42034step2 = -raw42034step1 := by apply Matrix.ext; change ∀ i j, raw42034step2 i j = -(raw42034step1 i j); unfold raw42034step2 raw42034step1; decide +kernel
      have hl : raw42034step2Labels = raw42034step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42034step2 raw42034step2Labels = mixedMoment B raw42034step3 raw42034step3Labels := by
      have ha : raw42034step3 = raw42034step2 := by apply Matrix.ext; unfold raw42034step3 raw42034step2; decide +kernel
      have hl : raw42034step2Labels = labelEmbedding1 ∘ raw42034step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42034step2 raw42034step2Labels raw42034step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw42035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42035Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42035step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42035step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42035 raw42035Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw42035 raw42035Labels = mixedMoment B raw42035step0 raw42035step0Labels := by
      have hz : ∀ j, raw42035 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42035step0 = (fun i j => raw42035 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42035step0 raw42035; decide +kernel
      have hl : raw42035step0Labels = raw42035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42035 raw42035Labels permutation346 hz
    mixedMoment B raw42035step0 raw42035step0Labels = mixedMoment B raw42035step1 raw42035step1Labels := by
      have ha : raw42035step1 = (fun i j => raw42035step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42035step1 raw42035step0; decide +kernel
      have hl : raw42035step1Labels = raw42035step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42035step0 raw42035step0Labels permutation32 permutation3
    mixedMoment B raw42035step1 raw42035step1Labels = mixedMoment B raw42035step2 raw42035step2Labels := by
      have ha : raw42035step2 = raw42035step1 := by apply Matrix.ext; unfold raw42035step2 raw42035step1; decide +kernel
      have hl : raw42035step1Labels = labelEmbedding7 ∘ raw42035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42035step1 raw42035step1Labels raw42035step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw42036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42036Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42036step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42036step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42036step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42036step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42036 raw42036Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw42036 raw42036Labels = mixedMoment B raw42036step0 raw42036step0Labels := by
      have hz : ∀ j, raw42036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42036step0 = (fun i j => raw42036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42036step0 raw42036; decide +kernel
      have hl : raw42036step0Labels = raw42036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42036 raw42036Labels permutation346 hz
    mixedMoment B raw42036step0 raw42036step0Labels = mixedMoment B raw42036step1 raw42036step1Labels := by
      have ha : raw42036step1 = (fun i j => raw42036step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42036step1 raw42036step0; decide +kernel
      have hl : raw42036step1Labels = raw42036step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42036step0 raw42036step0Labels permutation151 permutation2
    mixedMoment B raw42036step1 raw42036step1Labels = mixedMoment B raw42036step2 raw42036step2Labels := by
      have ha : raw42036step2 = -raw42036step1 := by apply Matrix.ext; change ∀ i j, raw42036step2 i j = -(raw42036step1 i j); unfold raw42036step2 raw42036step1; decide +kernel
      have hl : raw42036step2Labels = raw42036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42036step2 raw42036step2Labels = mixedMoment B raw42036step3 raw42036step3Labels := by
      have ha : raw42036step3 = raw42036step2 := by apply Matrix.ext; unfold raw42036step3 raw42036step2; decide +kernel
      have hl : raw42036step2Labels = labelEmbedding1 ∘ raw42036step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42036step2 raw42036step2Labels raw42036step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw42037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42037Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42037step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42037step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42037step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42037 raw42037Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw42037 raw42037Labels = mixedMoment B raw42037step0 raw42037step0Labels := by
      have hz : ∀ j, raw42037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42037step0 = (fun i j => raw42037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42037step0 raw42037; decide +kernel
      have hl : raw42037step0Labels = raw42037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42037 raw42037Labels permutation346 hz
    mixedMoment B raw42037step0 raw42037step0Labels = mixedMoment B raw42037step1 raw42037step1Labels := by
      have ha : raw42037step1 = (fun i j => raw42037step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42037step1 raw42037step0; decide +kernel
      have hl : raw42037step1Labels = raw42037step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42037step0 raw42037step0Labels permutation32 permutation3
    mixedMoment B raw42037step1 raw42037step1Labels = mixedMoment B raw42037step2 raw42037step2Labels := by
      have ha : raw42037step2 = raw42037step1 := by apply Matrix.ext; unfold raw42037step2 raw42037step1; decide +kernel
      have hl : raw42037step1Labels = labelEmbedding7 ∘ raw42037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42037step1 raw42037step1Labels raw42037step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw42038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42038Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42038step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42038step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42038 raw42038Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw42038 raw42038Labels = mixedMoment B raw42038step0 raw42038step0Labels := by
      have hz : ∀ j, raw42038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42038step0 = (fun i j => raw42038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42038step0 raw42038; decide +kernel
      have hl : raw42038step0Labels = raw42038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42038 raw42038Labels permutation346 hz
    mixedMoment B raw42038step0 raw42038step0Labels = mixedMoment B raw42038step1 raw42038step1Labels := by
      have ha : raw42038step1 = (fun i j => raw42038step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42038step1 raw42038step0; decide +kernel
      have hl : raw42038step1Labels = raw42038step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42038step0 raw42038step0Labels permutation145 permutation4
    mixedMoment B raw42038step1 raw42038step1Labels = mixedMoment B raw42038step2 raw42038step2Labels := by
      have ha : raw42038step2 = raw42038step1 := by apply Matrix.ext; unfold raw42038step2 raw42038step1; decide +kernel
      have hl : raw42038step1Labels = labelEmbedding1 ∘ raw42038step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42038step1 raw42038step1Labels raw42038step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw42039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42039Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42039step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42039step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42039step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42039step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42039 raw42039Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw42039 raw42039Labels = mixedMoment B raw42039step0 raw42039step0Labels := by
      have hz : ∀ j, raw42039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42039step0 = (fun i j => raw42039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42039step0 raw42039; decide +kernel
      have hl : raw42039step0Labels = raw42039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42039 raw42039Labels permutation346 hz
    mixedMoment B raw42039step0 raw42039step0Labels = mixedMoment B raw42039step1 raw42039step1Labels := by
      have ha : raw42039step1 = (fun i j => raw42039step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42039step1 raw42039step0; decide +kernel
      have hl : raw42039step1Labels = raw42039step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42039step0 raw42039step0Labels permutation145 permutation4
    mixedMoment B raw42039step1 raw42039step1Labels = mixedMoment B raw42039step2 raw42039step2Labels := by
      have ha : raw42039step2 = raw42039step1 := by apply Matrix.ext; unfold raw42039step2 raw42039step1; decide +kernel
      have hl : raw42039step1Labels = labelEmbedding10 ∘ raw42039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42039step1 raw42039step1Labels raw42039step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw42040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42040Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42040step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42040 raw42040Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw42040 raw42040Labels = mixedMoment B raw42040step0 raw42040step0Labels := by
      have hz : ∀ j, raw42040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42040step0 = (fun i j => raw42040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42040step0 raw42040; decide +kernel
      have hl : raw42040step0Labels = raw42040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42040 raw42040Labels permutation346 hz
    mixedMoment B raw42040step0 raw42040step0Labels = mixedMoment B raw42040step1 raw42040step1Labels := by
      have ha : raw42040step1 = (fun i j => raw42040step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42040step1 raw42040step0; decide +kernel
      have hl : raw42040step1Labels = raw42040step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42040step0 raw42040step0Labels permutation151 permutation4
    mixedMoment B raw42040step1 raw42040step1Labels = mixedMoment B raw42040step2 raw42040step2Labels := by
      have ha : raw42040step2 = raw42040step1 := by apply Matrix.ext; unfold raw42040step2 raw42040step1; decide +kernel
      have hl : raw42040step1Labels = labelEmbedding1 ∘ raw42040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42040step1 raw42040step1Labels raw42040step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw42041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42041Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42041step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42041step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42041step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42041step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42041step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42041 raw42041Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw42041 raw42041Labels = mixedMoment B raw42041step0 raw42041step0Labels := by
      have hz : ∀ j, raw42041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42041step0 = (fun i j => raw42041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42041step0 raw42041; decide +kernel
      have hl : raw42041step0Labels = raw42041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42041 raw42041Labels permutation346 hz
    mixedMoment B raw42041step0 raw42041step0Labels = mixedMoment B raw42041step1 raw42041step1Labels := by
      have ha : raw42041step1 = (fun i j => raw42041step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42041step1 raw42041step0; decide +kernel
      have hl : raw42041step1Labels = raw42041step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42041step0 raw42041step0Labels permutation32 permutation5
    mixedMoment B raw42041step1 raw42041step1Labels = mixedMoment B raw42041step2 raw42041step2Labels := by
      have ha : raw42041step2 = -raw42041step1 := by apply Matrix.ext; change ∀ i j, raw42041step2 i j = -(raw42041step1 i j); unfold raw42041step2 raw42041step1; decide +kernel
      have hl : raw42041step2Labels = raw42041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42041step2 raw42041step2Labels = mixedMoment B raw42041step3 raw42041step3Labels := by
      have ha : raw42041step3 = raw42041step2 := by apply Matrix.ext; unfold raw42041step3 raw42041step2; decide +kernel
      have hl : raw42041step2Labels = labelEmbedding9 ∘ raw42041step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42041step2 raw42041step2Labels raw42041step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw42042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42042Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42042step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42042step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42042step1Labels : Fin 2 → Fin 2 := ![1, 1]

def raw42042step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42042step2Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical42042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42042 raw42042Labels = mixedMoment B node3 node3Labels := by
  calc
    mixedMoment B raw42042 raw42042Labels = mixedMoment B raw42042step0 raw42042step0Labels := by
      have hz : ∀ j, raw42042 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42042step0 = (fun i j => raw42042 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42042step0 raw42042; decide +kernel
      have hl : raw42042step0Labels = raw42042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42042 raw42042Labels permutation346 hz
    mixedMoment B raw42042step0 raw42042step0Labels = mixedMoment B raw42042step1 raw42042step1Labels := by
      have hz : ∀ i, raw42042step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42042step1 = (fun i j => raw42042step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42042step1 raw42042step0; decide +kernel
      have hl : raw42042step1Labels = (fun j => raw42042step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42042step0 raw42042step0Labels permutation6 hz
    mixedMoment B raw42042step1 raw42042step1Labels = mixedMoment B raw42042step2 raw42042step2Labels := by
      have ha : raw42042step2 = raw42042step1 := by apply Matrix.ext; unfold raw42042step2 raw42042step1; decide +kernel
      have hl : raw42042step1Labels = labelEmbedding0 ∘ raw42042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42042step1 raw42042step1Labels raw42042step2Labels labelEmbedding0 hl
    _ = mixedMoment B node3 node3Labels := by rfl

def raw42043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42043Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42043step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42043step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42043step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw42043step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw42043step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical42043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42043 raw42043Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw42043 raw42043Labels = mixedMoment B raw42043step0 raw42043step0Labels := by
      have hz : ∀ j, raw42043 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42043step0 = (fun i j => raw42043 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42043step0 raw42043; decide +kernel
      have hl : raw42043step0Labels = raw42043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42043 raw42043Labels permutation346 hz
    mixedMoment B raw42043step0 raw42043step0Labels = mixedMoment B raw42043step1 raw42043step1Labels := by
      have hz : ∀ i, raw42043step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw42043step1 = (fun i j => raw42043step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw42043step1 raw42043step0; decide +kernel
      have hl : raw42043step1Labels = (fun j => raw42043step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw42043step0 raw42043step0Labels permutation6 hz
    mixedMoment B raw42043step1 raw42043step1Labels = mixedMoment B raw42043step2 raw42043step2Labels := by
      have ha : raw42043step2 = raw42043step1 := by apply Matrix.ext; unfold raw42043step2 raw42043step1; decide +kernel
      have hl : raw42043step1Labels = labelEmbedding3 ∘ raw42043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42043step1 raw42043step1Labels raw42043step2Labels labelEmbedding3 hl
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw42044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42044Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42044step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42044 raw42044Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw42044 raw42044Labels = mixedMoment B raw42044step0 raw42044step0Labels := by
      have ha : raw42044step0 = (fun i j => raw42044 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42044step0 raw42044; decide +kernel
      have hl : raw42044step0Labels = raw42044Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42044 raw42044Labels permutation682 permutation2
    mixedMoment B raw42044step0 raw42044step0Labels = mixedMoment B raw42044step1 raw42044step1Labels := by
      have ha : raw42044step1 = -raw42044step0 := by apply Matrix.ext; change ∀ i j, raw42044step1 i j = -(raw42044step0 i j); unfold raw42044step1 raw42044step0; decide +kernel
      have hl : raw42044step1Labels = raw42044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42044step1 raw42044step1Labels = mixedMoment B raw42044step2 raw42044step2Labels := by
      have ha : raw42044step2 = raw42044step1 := by apply Matrix.ext; unfold raw42044step2 raw42044step1; decide +kernel
      have hl : raw42044step1Labels = labelEmbedding1 ∘ raw42044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42044step1 raw42044step1Labels raw42044step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw42045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42045Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42045step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42045 raw42045Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw42045 raw42045Labels = mixedMoment B raw42045step0 raw42045step0Labels := by
      have ha : raw42045step0 = (fun i j => raw42045 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42045step0 raw42045; decide +kernel
      have hl : raw42045step0Labels = raw42045Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42045 raw42045Labels permutation152 permutation3
    mixedMoment B raw42045step0 raw42045step0Labels = mixedMoment B raw42045step1 raw42045step1Labels := by
      have ha : raw42045step1 = raw42045step0 := by apply Matrix.ext; unfold raw42045step1 raw42045step0; decide +kernel
      have hl : raw42045step0Labels = labelEmbedding7 ∘ raw42045step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42045step0 raw42045step0Labels raw42045step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw42046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42046Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42046step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42046 raw42046Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw42046 raw42046Labels = mixedMoment B raw42046step0 raw42046step0Labels := by
      have ha : raw42046step0 = (fun i j => raw42046 (permutation640 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42046step0 raw42046; decide +kernel
      have hl : raw42046step0Labels = raw42046Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42046 raw42046Labels permutation640 permutation4
    mixedMoment B raw42046step0 raw42046step0Labels = mixedMoment B raw42046step1 raw42046step1Labels := by
      have ha : raw42046step1 = raw42046step0 := by apply Matrix.ext; unfold raw42046step1 raw42046step0; decide +kernel
      have hl : raw42046step0Labels = labelEmbedding1 ∘ raw42046step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42046step0 raw42046step0Labels raw42046step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw42047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42047Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42047step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42047step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42047step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42047step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42047 raw42047Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw42047 raw42047Labels = mixedMoment B raw42047step0 raw42047step0Labels := by
      have ha : raw42047step0 = (fun i j => raw42047 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42047step0 raw42047; decide +kernel
      have hl : raw42047step0Labels = raw42047Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42047 raw42047Labels permutation160 permutation5
    mixedMoment B raw42047step0 raw42047step0Labels = mixedMoment B raw42047step1 raw42047step1Labels := by
      have ha : raw42047step1 = -raw42047step0 := by apply Matrix.ext; change ∀ i j, raw42047step1 i j = -(raw42047step0 i j); unfold raw42047step1 raw42047step0; decide +kernel
      have hl : raw42047step1Labels = raw42047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42047step1 raw42047step1Labels = mixedMoment B raw42047step2 raw42047step2Labels := by
      have ha : raw42047step2 = raw42047step1 := by apply Matrix.ext; unfold raw42047step2 raw42047step1; decide +kernel
      have hl : raw42047step1Labels = labelEmbedding9 ∘ raw42047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42047step1 raw42047step1Labels raw42047step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw42048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42048Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42048step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42048 raw42048Labels = mixedMoment B node4038 node4038Labels := by
  calc
    mixedMoment B raw42048 raw42048Labels = mixedMoment B raw42048step0 raw42048step0Labels := by
      have ha : raw42048step0 = (fun i j => raw42048 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42048step0 raw42048; decide +kernel
      have hl : raw42048step0Labels = raw42048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42048 raw42048Labels permutation155 permutation2
    mixedMoment B raw42048step0 raw42048step0Labels = mixedMoment B raw42048step1 raw42048step1Labels := by
      have ha : raw42048step1 = raw42048step0 := by apply Matrix.ext; unfold raw42048step1 raw42048step0; decide +kernel
      have hl : raw42048step0Labels = labelEmbedding1 ∘ raw42048step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42048step0 raw42048step0Labels raw42048step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4038 node4038Labels := by rfl

def raw42049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42049Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42049step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42049 raw42049Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw42049 raw42049Labels = mixedMoment B raw42049step0 raw42049step0Labels := by
      have ha : raw42049step0 = (fun i j => raw42049 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42049step0 raw42049; decide +kernel
      have hl : raw42049step0Labels = raw42049Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42049 raw42049Labels permutation152 permutation3
    mixedMoment B raw42049step0 raw42049step0Labels = mixedMoment B raw42049step1 raw42049step1Labels := by
      have ha : raw42049step1 = raw42049step0 := by apply Matrix.ext; unfold raw42049step1 raw42049step0; decide +kernel
      have hl : raw42049step0Labels = labelEmbedding7 ∘ raw42049step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42049step0 raw42049step0Labels raw42049step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw42050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42050Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42050step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42050 raw42050Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw42050 raw42050Labels = mixedMoment B raw42050step0 raw42050step0Labels := by
      have ha : raw42050step0 = (fun i j => raw42050 (permutation427 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42050step0 raw42050; decide +kernel
      have hl : raw42050step0Labels = raw42050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42050 raw42050Labels permutation427 permutation4
    mixedMoment B raw42050step0 raw42050step0Labels = mixedMoment B raw42050step1 raw42050step1Labels := by
      have ha : raw42050step1 = raw42050step0 := by apply Matrix.ext; unfold raw42050step1 raw42050step0; decide +kernel
      have hl : raw42050step0Labels = labelEmbedding1 ∘ raw42050step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42050step0 raw42050step0Labels raw42050step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw42051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42051Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42051step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42051step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42051step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42051 raw42051Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw42051 raw42051Labels = mixedMoment B raw42051step0 raw42051step0Labels := by
      have ha : raw42051step0 = (fun i j => raw42051 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42051step0 raw42051; decide +kernel
      have hl : raw42051step0Labels = raw42051Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42051 raw42051Labels permutation161 permutation5
    mixedMoment B raw42051step0 raw42051step0Labels = mixedMoment B raw42051step1 raw42051step1Labels := by
      have ha : raw42051step1 = -raw42051step0 := by apply Matrix.ext; change ∀ i j, raw42051step1 i j = -(raw42051step0 i j); unfold raw42051step1 raw42051step0; decide +kernel
      have hl : raw42051step1Labels = raw42051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42051step1 raw42051step1Labels = mixedMoment B raw42051step2 raw42051step2Labels := by
      have ha : raw42051step2 = raw42051step1 := by apply Matrix.ext; unfold raw42051step2 raw42051step1; decide +kernel
      have hl : raw42051step1Labels = labelEmbedding9 ∘ raw42051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42051step1 raw42051step1Labels raw42051step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw42052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42052Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42052step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42052step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42052step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42052step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42052step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42052 raw42052Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw42052 raw42052Labels = mixedMoment B raw42052step0 raw42052step0Labels := by
      have hz : ∀ j, raw42052 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42052step0 = (fun i j => raw42052 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42052step0 raw42052; decide +kernel
      have hl : raw42052step0Labels = raw42052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42052 raw42052Labels permutation520 hz
    mixedMoment B raw42052step0 raw42052step0Labels = mixedMoment B raw42052step1 raw42052step1Labels := by
      have hz : ∀ j, raw42052step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42052step1 = (fun i j => raw42052step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42052step1 raw42052step0; decide +kernel
      have hl : raw42052step1Labels = raw42052step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42052step0 raw42052step0Labels permutation104 hz
    mixedMoment B raw42052step1 raw42052step1Labels = mixedMoment B raw42052step2 raw42052step2Labels := by
      have ha : raw42052step2 = (fun i j => raw42052step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42052step2 raw42052step1; decide +kernel
      have hl : raw42052step2Labels = raw42052step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42052step1 raw42052step1Labels permutation31 permutation2
    mixedMoment B raw42052step2 raw42052step2Labels = mixedMoment B raw42052step3 raw42052step3Labels := by
      have ha : raw42052step3 = -raw42052step2 := by apply Matrix.ext; change ∀ i j, raw42052step3 i j = -(raw42052step2 i j); unfold raw42052step3 raw42052step2; decide +kernel
      have hl : raw42052step3Labels = raw42052step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42052step3 raw42052step3Labels = mixedMoment B raw42052step4 raw42052step4Labels := by
      have ha : raw42052step4 = raw42052step3 := by apply Matrix.ext; unfold raw42052step4 raw42052step3; decide +kernel
      have hl : raw42052step3Labels = labelEmbedding1 ∘ raw42052step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42052step3 raw42052step3Labels raw42052step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw42053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42053Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42053step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![3, -3, 0]]
def raw42053step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42053step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42053step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42053step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42053step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42053 raw42053Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw42053 raw42053Labels = mixedMoment B raw42053step0 raw42053step0Labels := by
      have hz : ∀ j, raw42053 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42053step0 = (fun i j => raw42053 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42053step0 raw42053; decide +kernel
      have hl : raw42053step0Labels = raw42053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42053 raw42053Labels permutation520 hz
    mixedMoment B raw42053step0 raw42053step0Labels = mixedMoment B raw42053step1 raw42053step1Labels := by
      have hz : ∀ j, raw42053step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42053step1 = (fun i j => raw42053step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42053step1 raw42053step0; decide +kernel
      have hl : raw42053step1Labels = raw42053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42053step0 raw42053step0Labels permutation104 hz
    mixedMoment B raw42053step1 raw42053step1Labels = mixedMoment B raw42053step2 raw42053step2Labels := by
      have ha : raw42053step2 = (fun i j => raw42053step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42053step2 raw42053step1; decide +kernel
      have hl : raw42053step2Labels = raw42053step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42053step1 raw42053step1Labels permutation31 permutation3
    mixedMoment B raw42053step2 raw42053step2Labels = mixedMoment B raw42053step3 raw42053step3Labels := by
      have ha : raw42053step3 = -raw42053step2 := by apply Matrix.ext; change ∀ i j, raw42053step3 i j = -(raw42053step2 i j); unfold raw42053step3 raw42053step2; decide +kernel
      have hl : raw42053step3Labels = raw42053step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42053step3 raw42053step3Labels = mixedMoment B raw42053step4 raw42053step4Labels := by
      have ha : raw42053step4 = raw42053step3 := by apply Matrix.ext; unfold raw42053step4 raw42053step3; decide +kernel
      have hl : raw42053step3Labels = labelEmbedding7 ∘ raw42053step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42053step3 raw42053step3Labels raw42053step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw42054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42054Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42054step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42054 raw42054Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw42054 raw42054Labels = mixedMoment B raw42054step0 raw42054step0Labels := by
      have hz : ∀ j, raw42054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42054step0 = (fun i j => raw42054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42054step0 raw42054; decide +kernel
      have hl : raw42054step0Labels = raw42054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42054 raw42054Labels permutation434 hz
    mixedMoment B raw42054step0 raw42054step0Labels = mixedMoment B raw42054step1 raw42054step1Labels := by
      have ha : raw42054step1 = (fun i j => raw42054step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42054step1 raw42054step0; decide +kernel
      have hl : raw42054step1Labels = raw42054step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42054step0 raw42054step0Labels permutation139 permutation4
    mixedMoment B raw42054step1 raw42054step1Labels = mixedMoment B raw42054step2 raw42054step2Labels := by
      have ha : raw42054step2 = raw42054step1 := by apply Matrix.ext; unfold raw42054step2 raw42054step1; decide +kernel
      have hl : raw42054step1Labels = labelEmbedding1 ∘ raw42054step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42054step1 raw42054step1Labels raw42054step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw42055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42055Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42055step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42055step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42055step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42055 raw42055Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw42055 raw42055Labels = mixedMoment B raw42055step0 raw42055step0Labels := by
      have hz : ∀ j, raw42055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42055step0 = (fun i j => raw42055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42055step0 raw42055; decide +kernel
      have hl : raw42055step0Labels = raw42055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42055 raw42055Labels permutation434 hz
    mixedMoment B raw42055step0 raw42055step0Labels = mixedMoment B raw42055step1 raw42055step1Labels := by
      have ha : raw42055step1 = (fun i j => raw42055step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42055step1 raw42055step0; decide +kernel
      have hl : raw42055step1Labels = raw42055step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42055step0 raw42055step0Labels permutation149 permutation5
    mixedMoment B raw42055step1 raw42055step1Labels = mixedMoment B raw42055step2 raw42055step2Labels := by
      have ha : raw42055step2 = raw42055step1 := by apply Matrix.ext; unfold raw42055step2 raw42055step1; decide +kernel
      have hl : raw42055step1Labels = labelEmbedding9 ∘ raw42055step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42055step1 raw42055step1Labels raw42055step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw42056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42056Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42056step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42056 raw42056Labels = mixedMoment B node4035 node4035Labels := by
  calc
    mixedMoment B raw42056 raw42056Labels = mixedMoment B raw42056step0 raw42056step0Labels := by
      have hz : ∀ j, raw42056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42056step0 = (fun i j => raw42056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42056step0 raw42056; decide +kernel
      have hl : raw42056step0Labels = raw42056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42056 raw42056Labels permutation434 hz
    mixedMoment B raw42056step0 raw42056step0Labels = mixedMoment B raw42056step1 raw42056step1Labels := by
      have ha : raw42056step1 = raw42056step0 := by apply Matrix.ext; unfold raw42056step1 raw42056step0; decide +kernel
      have hl : raw42056step0Labels = labelEmbedding1 ∘ raw42056step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42056step0 raw42056step0Labels raw42056step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4035 node4035Labels := by rfl

def raw42057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42057Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42057step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42057step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42057step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42057step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42057 raw42057Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw42057 raw42057Labels = mixedMoment B raw42057step0 raw42057step0Labels := by
      have hz : ∀ j, raw42057 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42057step0 = (fun i j => raw42057 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42057step0 raw42057; decide +kernel
      have hl : raw42057step0Labels = raw42057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42057 raw42057Labels permutation434 hz
    mixedMoment B raw42057step0 raw42057step0Labels = mixedMoment B raw42057step1 raw42057step1Labels := by
      have ha : raw42057step1 = (fun i j => raw42057step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42057step1 raw42057step0; decide +kernel
      have hl : raw42057step1Labels = raw42057step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42057step0 raw42057step0Labels permutation151 permutation3
    mixedMoment B raw42057step1 raw42057step1Labels = mixedMoment B raw42057step2 raw42057step2Labels := by
      have ha : raw42057step2 = -raw42057step1 := by apply Matrix.ext; change ∀ i j, raw42057step2 i j = -(raw42057step1 i j); unfold raw42057step2 raw42057step1; decide +kernel
      have hl : raw42057step2Labels = raw42057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42057step2 raw42057step2Labels = mixedMoment B raw42057step3 raw42057step3Labels := by
      have ha : raw42057step3 = raw42057step2 := by apply Matrix.ext; unfold raw42057step3 raw42057step2; decide +kernel
      have hl : raw42057step2Labels = labelEmbedding7 ∘ raw42057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42057step2 raw42057step2Labels raw42057step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw42058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42058Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42058step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42058step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42058step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42058step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42058step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42058 raw42058Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw42058 raw42058Labels = mixedMoment B raw42058step0 raw42058step0Labels := by
      have hz : ∀ j, raw42058 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42058step0 = (fun i j => raw42058 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42058step0 raw42058; decide +kernel
      have hl : raw42058step0Labels = raw42058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42058 raw42058Labels permutation434 hz
    mixedMoment B raw42058step0 raw42058step0Labels = mixedMoment B raw42058step1 raw42058step1Labels := by
      have ha : raw42058step1 = (fun i j => raw42058step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42058step1 raw42058step0; decide +kernel
      have hl : raw42058step1Labels = raw42058step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42058step0 raw42058step0Labels permutation151 permutation2
    mixedMoment B raw42058step1 raw42058step1Labels = mixedMoment B raw42058step2 raw42058step2Labels := by
      have ha : raw42058step2 = -raw42058step1 := by apply Matrix.ext; change ∀ i j, raw42058step2 i j = -(raw42058step1 i j); unfold raw42058step2 raw42058step1; decide +kernel
      have hl : raw42058step2Labels = raw42058step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42058step2 raw42058step2Labels = mixedMoment B raw42058step3 raw42058step3Labels := by
      have ha : raw42058step3 = raw42058step2 := by apply Matrix.ext; unfold raw42058step3 raw42058step2; decide +kernel
      have hl : raw42058step2Labels = labelEmbedding1 ∘ raw42058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42058step2 raw42058step2Labels raw42058step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw42059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42059Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42059step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42059step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42059step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42059 raw42059Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw42059 raw42059Labels = mixedMoment B raw42059step0 raw42059step0Labels := by
      have hz : ∀ j, raw42059 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42059step0 = (fun i j => raw42059 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42059step0 raw42059; decide +kernel
      have hl : raw42059step0Labels = raw42059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42059 raw42059Labels permutation434 hz
    mixedMoment B raw42059step0 raw42059step0Labels = mixedMoment B raw42059step1 raw42059step1Labels := by
      have ha : raw42059step1 = (fun i j => raw42059step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42059step1 raw42059step0; decide +kernel
      have hl : raw42059step1Labels = raw42059step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42059step0 raw42059step0Labels permutation32 permutation3
    mixedMoment B raw42059step1 raw42059step1Labels = mixedMoment B raw42059step2 raw42059step2Labels := by
      have ha : raw42059step2 = raw42059step1 := by apply Matrix.ext; unfold raw42059step2 raw42059step1; decide +kernel
      have hl : raw42059step1Labels = labelEmbedding7 ∘ raw42059step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42059step1 raw42059step1Labels raw42059step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw42060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42060Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42060 raw42060Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw42060 raw42060Labels = mixedMoment B raw42060step0 raw42060step0Labels := by
      have hz : ∀ j, raw42060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42060step0 = (fun i j => raw42060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42060step0 raw42060; decide +kernel
      have hl : raw42060step0Labels = raw42060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42060 raw42060Labels permutation434 hz
    mixedMoment B raw42060step0 raw42060step0Labels = mixedMoment B raw42060step1 raw42060step1Labels := by
      have ha : raw42060step1 = (fun i j => raw42060step0 (permutation115 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42060step1 raw42060step0; decide +kernel
      have hl : raw42060step1Labels = raw42060step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42060step0 raw42060step0Labels permutation115 permutation4
    mixedMoment B raw42060step1 raw42060step1Labels = mixedMoment B raw42060step2 raw42060step2Labels := by
      have ha : raw42060step2 = raw42060step1 := by apply Matrix.ext; unfold raw42060step2 raw42060step1; decide +kernel
      have hl : raw42060step1Labels = labelEmbedding1 ∘ raw42060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42060step1 raw42060step1Labels raw42060step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw42061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42061Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42061step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42061step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42061step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42061 raw42061Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42061 raw42061Labels = mixedMoment B raw42061step0 raw42061step0Labels := by
      have hz : ∀ j, raw42061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42061step0 = (fun i j => raw42061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42061step0 raw42061; decide +kernel
      have hl : raw42061step0Labels = raw42061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42061 raw42061Labels permutation434 hz
    mixedMoment B raw42061step0 raw42061step0Labels = mixedMoment B raw42061step1 raw42061step1Labels := by
      have ha : raw42061step1 = (fun i j => raw42061step0 (permutation115 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42061step1 raw42061step0; decide +kernel
      have hl : raw42061step1Labels = raw42061step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42061step0 raw42061step0Labels permutation115 permutation4
    mixedMoment B raw42061step1 raw42061step1Labels = mixedMoment B raw42061step2 raw42061step2Labels := by
      have ha : raw42061step2 = raw42061step1 := by apply Matrix.ext; unfold raw42061step2 raw42061step1; decide +kernel
      have hl : raw42061step1Labels = labelEmbedding10 ∘ raw42061step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42061step1 raw42061step1Labels raw42061step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw42062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42062Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42062step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42062 raw42062Labels = mixedMoment B node4032 node4032Labels := by
  calc
    mixedMoment B raw42062 raw42062Labels = mixedMoment B raw42062step0 raw42062step0Labels := by
      have ha : raw42062step0 = (fun i j => raw42062 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42062step0 raw42062; decide +kernel
      have hl : raw42062step0Labels = raw42062Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42062 raw42062Labels permutation158 permutation2
    mixedMoment B raw42062step0 raw42062step0Labels = mixedMoment B raw42062step1 raw42062step1Labels := by
      have ha : raw42062step1 = raw42062step0 := by apply Matrix.ext; unfold raw42062step1 raw42062step0; decide +kernel
      have hl : raw42062step0Labels = labelEmbedding1 ∘ raw42062step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42062step0 raw42062step0Labels raw42062step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4032 node4032Labels := by rfl

def raw42063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42063Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42063step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42063 raw42063Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw42063 raw42063Labels = mixedMoment B raw42063step0 raw42063step0Labels := by
      have ha : raw42063step0 = (fun i j => raw42063 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42063step0 raw42063; decide +kernel
      have hl : raw42063step0Labels = raw42063Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42063 raw42063Labels permutation152 permutation3
    mixedMoment B raw42063step0 raw42063step0Labels = mixedMoment B raw42063step1 raw42063step1Labels := by
      have ha : raw42063step1 = raw42063step0 := by apply Matrix.ext; unfold raw42063step1 raw42063step0; decide +kernel
      have hl : raw42063step0Labels = labelEmbedding7 ∘ raw42063step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42063step0 raw42063step0Labels raw42063step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw42064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42064Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42064step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42064step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42064step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42064step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42064 raw42064Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw42064 raw42064Labels = mixedMoment B raw42064step0 raw42064step0Labels := by
      have ha : raw42064step0 = (fun i j => raw42064 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42064step0 raw42064; decide +kernel
      have hl : raw42064step0Labels = raw42064Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42064 raw42064Labels permutation682 permutation2
    mixedMoment B raw42064step0 raw42064step0Labels = mixedMoment B raw42064step1 raw42064step1Labels := by
      have ha : raw42064step1 = -raw42064step0 := by apply Matrix.ext; change ∀ i j, raw42064step1 i j = -(raw42064step0 i j); unfold raw42064step1 raw42064step0; decide +kernel
      have hl : raw42064step1Labels = raw42064step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42064step1 raw42064step1Labels = mixedMoment B raw42064step2 raw42064step2Labels := by
      have ha : raw42064step2 = raw42064step1 := by apply Matrix.ext; unfold raw42064step2 raw42064step1; decide +kernel
      have hl : raw42064step1Labels = labelEmbedding1 ∘ raw42064step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42064step1 raw42064step1Labels raw42064step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw42065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42065Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42065step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42065 raw42065Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw42065 raw42065Labels = mixedMoment B raw42065step0 raw42065step0Labels := by
      have ha : raw42065step0 = (fun i j => raw42065 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42065step0 raw42065; decide +kernel
      have hl : raw42065step0Labels = raw42065Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42065 raw42065Labels permutation152 permutation3
    mixedMoment B raw42065step0 raw42065step0Labels = mixedMoment B raw42065step1 raw42065step1Labels := by
      have ha : raw42065step1 = raw42065step0 := by apply Matrix.ext; unfold raw42065step1 raw42065step0; decide +kernel
      have hl : raw42065step0Labels = labelEmbedding7 ∘ raw42065step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42065step0 raw42065step0Labels raw42065step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw42066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42066Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42066 raw42066Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw42066 raw42066Labels = mixedMoment B raw42066step0 raw42066step0Labels := by
      have ha : raw42066step0 = (fun i j => raw42066 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42066step0 raw42066; decide +kernel
      have hl : raw42066step0Labels = raw42066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42066 raw42066Labels permutation682 permutation2
    mixedMoment B raw42066step0 raw42066step0Labels = mixedMoment B raw42066step1 raw42066step1Labels := by
      have ha : raw42066step1 = -raw42066step0 := by apply Matrix.ext; change ∀ i j, raw42066step1 i j = -(raw42066step0 i j); unfold raw42066step1 raw42066step0; decide +kernel
      have hl : raw42066step1Labels = raw42066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42066step1 raw42066step1Labels = mixedMoment B raw42066step2 raw42066step2Labels := by
      have ha : raw42066step2 = raw42066step1 := by apply Matrix.ext; unfold raw42066step2 raw42066step1; decide +kernel
      have hl : raw42066step1Labels = labelEmbedding1 ∘ raw42066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42066step1 raw42066step1Labels raw42066step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw42067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42067Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42067step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42067 raw42067Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42067 raw42067Labels = mixedMoment B raw42067step0 raw42067step0Labels := by
      have ha : raw42067step0 = (fun i j => raw42067 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42067step0 raw42067; decide +kernel
      have hl : raw42067step0Labels = raw42067Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42067 raw42067Labels permutation152 permutation3
    mixedMoment B raw42067step0 raw42067step0Labels = mixedMoment B raw42067step1 raw42067step1Labels := by
      have ha : raw42067step1 = raw42067step0 := by apply Matrix.ext; unfold raw42067step1 raw42067step0; decide +kernel
      have hl : raw42067step0Labels = labelEmbedding7 ∘ raw42067step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42067step0 raw42067step0Labels raw42067step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw42068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42068Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42068step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42068step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42068step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42068 raw42068Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw42068 raw42068Labels = mixedMoment B raw42068step0 raw42068step0Labels := by
      have ha : raw42068step0 = (fun i j => raw42068 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42068step0 raw42068; decide +kernel
      have hl : raw42068step0Labels = raw42068Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42068 raw42068Labels permutation682 permutation2
    mixedMoment B raw42068step0 raw42068step0Labels = mixedMoment B raw42068step1 raw42068step1Labels := by
      have ha : raw42068step1 = -raw42068step0 := by apply Matrix.ext; change ∀ i j, raw42068step1 i j = -(raw42068step0 i j); unfold raw42068step1 raw42068step0; decide +kernel
      have hl : raw42068step1Labels = raw42068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42068step1 raw42068step1Labels = mixedMoment B raw42068step2 raw42068step2Labels := by
      have ha : raw42068step2 = raw42068step1 := by apply Matrix.ext; unfold raw42068step2 raw42068step1; decide +kernel
      have hl : raw42068step1Labels = labelEmbedding1 ∘ raw42068step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42068step1 raw42068step1Labels raw42068step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw42069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42069Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42069step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42069step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42069step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42069 raw42069Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw42069 raw42069Labels = mixedMoment B raw42069step0 raw42069step0Labels := by
      have ha : raw42069step0 = (fun i j => raw42069 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42069step0 raw42069; decide +kernel
      have hl : raw42069step0Labels = raw42069Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42069 raw42069Labels permutation682 permutation2
    mixedMoment B raw42069step0 raw42069step0Labels = mixedMoment B raw42069step1 raw42069step1Labels := by
      have ha : raw42069step1 = -raw42069step0 := by apply Matrix.ext; change ∀ i j, raw42069step1 i j = -(raw42069step0 i j); unfold raw42069step1 raw42069step0; decide +kernel
      have hl : raw42069step1Labels = raw42069step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42069step1 raw42069step1Labels = mixedMoment B raw42069step2 raw42069step2Labels := by
      have ha : raw42069step2 = raw42069step1 := by apply Matrix.ext; unfold raw42069step2 raw42069step1; decide +kernel
      have hl : raw42069step1Labels = labelEmbedding8 ∘ raw42069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42069step1 raw42069step1Labels raw42069step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5426 node5426Labels := by rfl

def raw42070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42070Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42070 raw42070Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw42070 raw42070Labels = mixedMoment B raw42070step0 raw42070step0Labels := by
      have ha : raw42070step0 = (fun i j => raw42070 (permutation616 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42070step0 raw42070; decide +kernel
      have hl : raw42070step0Labels = raw42070Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42070 raw42070Labels permutation616 permutation4
    mixedMoment B raw42070step0 raw42070step0Labels = mixedMoment B raw42070step1 raw42070step1Labels := by
      have ha : raw42070step1 = raw42070step0 := by apply Matrix.ext; unfold raw42070step1 raw42070step0; decide +kernel
      have hl : raw42070step0Labels = labelEmbedding1 ∘ raw42070step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42070step0 raw42070step0Labels raw42070step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw42071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42071Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42071step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42071 raw42071Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw42071 raw42071Labels = mixedMoment B raw42071step0 raw42071step0Labels := by
      have ha : raw42071step0 = (fun i j => raw42071 (permutation616 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42071step0 raw42071; decide +kernel
      have hl : raw42071step0Labels = raw42071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42071 raw42071Labels permutation616 permutation4
    mixedMoment B raw42071step0 raw42071step0Labels = mixedMoment B raw42071step1 raw42071step1Labels := by
      have ha : raw42071step1 = raw42071step0 := by apply Matrix.ext; unfold raw42071step1 raw42071step0; decide +kernel
      have hl : raw42071step0Labels = labelEmbedding10 ∘ raw42071step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42071step0 raw42071step0Labels raw42071step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw42072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42072Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42072step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42072 raw42072Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw42072 raw42072Labels = mixedMoment B raw42072step0 raw42072step0Labels := by
      have ha : raw42072step0 = (fun i j => raw42072 (permutation676 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42072step0 raw42072; decide +kernel
      have hl : raw42072step0Labels = raw42072Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42072 raw42072Labels permutation676 permutation4
    mixedMoment B raw42072step0 raw42072step0Labels = mixedMoment B raw42072step1 raw42072step1Labels := by
      have ha : raw42072step1 = raw42072step0 := by apply Matrix.ext; unfold raw42072step1 raw42072step0; decide +kernel
      have hl : raw42072step0Labels = labelEmbedding1 ∘ raw42072step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42072step0 raw42072step0Labels raw42072step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw42073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42073Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42073step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42073step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42073 raw42073Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw42073 raw42073Labels = mixedMoment B raw42073step0 raw42073step0Labels := by
      have ha : raw42073step0 = (fun i j => raw42073 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42073step0 raw42073; decide +kernel
      have hl : raw42073step0Labels = raw42073Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42073 raw42073Labels permutation176 permutation5
    mixedMoment B raw42073step0 raw42073step0Labels = mixedMoment B raw42073step1 raw42073step1Labels := by
      have ha : raw42073step1 = -raw42073step0 := by apply Matrix.ext; change ∀ i j, raw42073step1 i j = -(raw42073step0 i j); unfold raw42073step1 raw42073step0; decide +kernel
      have hl : raw42073step1Labels = raw42073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42073step1 raw42073step1Labels = mixedMoment B raw42073step2 raw42073step2Labels := by
      have ha : raw42073step2 = raw42073step1 := by apply Matrix.ext; unfold raw42073step2 raw42073step1; decide +kernel
      have hl : raw42073step1Labels = labelEmbedding9 ∘ raw42073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42073step1 raw42073step1Labels raw42073step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw42074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42074Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42074 raw42074Labels = mixedMoment B node4034 node4034Labels := by
  calc
    mixedMoment B raw42074 raw42074Labels = mixedMoment B raw42074step0 raw42074step0Labels := by
      have ha : raw42074step0 = raw42074 := by apply Matrix.ext; unfold raw42074step0 raw42074; decide +kernel
      have hl : raw42074Labels = labelEmbedding1 ∘ raw42074step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42074 raw42074Labels raw42074step0Labels labelEmbedding1 hl
    _ = mixedMoment B node4034 node4034Labels := by rfl

def raw42075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42075Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42075step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42075 raw42075Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw42075 raw42075Labels = mixedMoment B raw42075step0 raw42075step0Labels := by
      have ha : raw42075step0 = (fun i j => raw42075 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42075step0 raw42075; decide +kernel
      have hl : raw42075step0Labels = raw42075Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42075 raw42075Labels permutation152 permutation3
    mixedMoment B raw42075step0 raw42075step0Labels = mixedMoment B raw42075step1 raw42075step1Labels := by
      have ha : raw42075step1 = raw42075step0 := by apply Matrix.ext; unfold raw42075step1 raw42075step0; decide +kernel
      have hl : raw42075step0Labels = labelEmbedding7 ∘ raw42075step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42075step0 raw42075step0Labels raw42075step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5427 node5427Labels := by rfl

def raw42076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42076Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42076step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42076step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42076 raw42076Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw42076 raw42076Labels = mixedMoment B raw42076step0 raw42076step0Labels := by
      have hz : ∀ j, raw42076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42076step0 = (fun i j => raw42076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42076step0 raw42076; decide +kernel
      have hl : raw42076step0Labels = raw42076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42076 raw42076Labels permutation434 hz
    mixedMoment B raw42076step0 raw42076step0Labels = mixedMoment B raw42076step1 raw42076step1Labels := by
      have hz : ∀ j, raw42076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42076step1 = (fun i j => raw42076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42076step1 raw42076step0; decide +kernel
      have hl : raw42076step1Labels = raw42076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42076step0 raw42076step0Labels permutation80 hz
    mixedMoment B raw42076step1 raw42076step1Labels = mixedMoment B raw42076step2 raw42076step2Labels := by
      have ha : raw42076step2 = (fun i j => raw42076step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42076step2 raw42076step1; decide +kernel
      have hl : raw42076step2Labels = raw42076step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42076step1 raw42076step1Labels permutation29 permutation4
    mixedMoment B raw42076step2 raw42076step2Labels = mixedMoment B raw42076step3 raw42076step3Labels := by
      have ha : raw42076step3 = raw42076step2 := by apply Matrix.ext; unfold raw42076step3 raw42076step2; decide +kernel
      have hl : raw42076step2Labels = labelEmbedding1 ∘ raw42076step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42076step2 raw42076step2Labels raw42076step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw42077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42077Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42077step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -3, 1]]
def raw42077step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42077step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42077step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42077step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42077step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42077 raw42077Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw42077 raw42077Labels = mixedMoment B raw42077step0 raw42077step0Labels := by
      have hz : ∀ j, raw42077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42077step0 = (fun i j => raw42077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42077step0 raw42077; decide +kernel
      have hl : raw42077step0Labels = raw42077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42077 raw42077Labels permutation434 hz
    mixedMoment B raw42077step0 raw42077step0Labels = mixedMoment B raw42077step1 raw42077step1Labels := by
      have hz : ∀ j, raw42077step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42077step1 = (fun i j => raw42077step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42077step1 raw42077step0; decide +kernel
      have hl : raw42077step1Labels = raw42077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42077step0 raw42077step0Labels permutation80 hz
    mixedMoment B raw42077step1 raw42077step1Labels = mixedMoment B raw42077step2 raw42077step2Labels := by
      have ha : raw42077step2 = (fun i j => raw42077step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42077step2 raw42077step1; decide +kernel
      have hl : raw42077step2Labels = raw42077step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42077step1 raw42077step1Labels permutation29 permutation5
    mixedMoment B raw42077step2 raw42077step2Labels = mixedMoment B raw42077step3 raw42077step3Labels := by
      have ha : raw42077step3 = raw42077step2 := by apply Matrix.ext; unfold raw42077step3 raw42077step2; decide +kernel
      have hl : raw42077step2Labels = labelEmbedding9 ∘ raw42077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42077step2 raw42077step2Labels raw42077step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw42078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42078Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42078step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw42078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42078step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42078step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42078step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42078step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42078 raw42078Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw42078 raw42078Labels = mixedMoment B raw42078step0 raw42078step0Labels := by
      have hz : ∀ j, raw42078 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42078step0 = (fun i j => raw42078 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42078step0 raw42078; decide +kernel
      have hl : raw42078step0Labels = raw42078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42078 raw42078Labels permutation434 hz
    mixedMoment B raw42078step0 raw42078step0Labels = mixedMoment B raw42078step1 raw42078step1Labels := by
      have hz : ∀ j, raw42078step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42078step1 = (fun i j => raw42078step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42078step1 raw42078step0; decide +kernel
      have hl : raw42078step1Labels = raw42078step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42078step0 raw42078step0Labels permutation80 hz
    mixedMoment B raw42078step1 raw42078step1Labels = mixedMoment B raw42078step2 raw42078step2Labels := by
      have ha : raw42078step2 = (fun i j => raw42078step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42078step2 raw42078step1; decide +kernel
      have hl : raw42078step2Labels = raw42078step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42078step1 raw42078step1Labels permutation23 permutation4
    mixedMoment B raw42078step2 raw42078step2Labels = mixedMoment B raw42078step3 raw42078step3Labels := by
      have ha : raw42078step3 = raw42078step2 := by apply Matrix.ext; unfold raw42078step3 raw42078step2; decide +kernel
      have hl : raw42078step2Labels = labelEmbedding1 ∘ raw42078step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42078step2 raw42078step2Labels raw42078step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw42079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42079Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42079step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![2, 1, -3]]
def raw42079step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42079step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42079step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42079 raw42079Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw42079 raw42079Labels = mixedMoment B raw42079step0 raw42079step0Labels := by
      have hz : ∀ j, raw42079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42079step0 = (fun i j => raw42079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42079step0 raw42079; decide +kernel
      have hl : raw42079step0Labels = raw42079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42079 raw42079Labels permutation434 hz
    mixedMoment B raw42079step0 raw42079step0Labels = mixedMoment B raw42079step1 raw42079step1Labels := by
      have hz : ∀ j, raw42079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42079step1 = (fun i j => raw42079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42079step1 raw42079step0; decide +kernel
      have hl : raw42079step1Labels = raw42079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42079step0 raw42079step0Labels permutation80 hz
    mixedMoment B raw42079step1 raw42079step1Labels = mixedMoment B raw42079step2 raw42079step2Labels := by
      have ha : raw42079step2 = (fun i j => raw42079step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42079step2 raw42079step1; decide +kernel
      have hl : raw42079step2Labels = raw42079step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42079step1 raw42079step1Labels permutation23 permutation4
    mixedMoment B raw42079step2 raw42079step2Labels = mixedMoment B raw42079step3 raw42079step3Labels := by
      have ha : raw42079step3 = raw42079step2 := by apply Matrix.ext; unfold raw42079step3 raw42079step2; decide +kernel
      have hl : raw42079step2Labels = labelEmbedding10 ∘ raw42079step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42079step2 raw42079step2Labels raw42079step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw42080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42080Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42080step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42080step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42080step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42080step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42080 raw42080Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw42080 raw42080Labels = mixedMoment B raw42080step0 raw42080step0Labels := by
      have hz : ∀ j, raw42080 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42080step0 = (fun i j => raw42080 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42080step0 raw42080; decide +kernel
      have hl : raw42080step0Labels = raw42080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42080 raw42080Labels permutation346 hz
    mixedMoment B raw42080step0 raw42080step0Labels = mixedMoment B raw42080step1 raw42080step1Labels := by
      have ha : raw42080step1 = (fun i j => raw42080step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42080step1 raw42080step0; decide +kernel
      have hl : raw42080step1Labels = raw42080step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42080step0 raw42080step0Labels permutation151 permutation2
    mixedMoment B raw42080step1 raw42080step1Labels = mixedMoment B raw42080step2 raw42080step2Labels := by
      have ha : raw42080step2 = -raw42080step1 := by apply Matrix.ext; change ∀ i j, raw42080step2 i j = -(raw42080step1 i j); unfold raw42080step2 raw42080step1; decide +kernel
      have hl : raw42080step2Labels = raw42080step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42080step2 raw42080step2Labels = mixedMoment B raw42080step3 raw42080step3Labels := by
      have ha : raw42080step3 = raw42080step2 := by apply Matrix.ext; unfold raw42080step3 raw42080step2; decide +kernel
      have hl : raw42080step2Labels = labelEmbedding1 ∘ raw42080step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42080step2 raw42080step2Labels raw42080step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw42081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42081Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42081step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42081step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42081 raw42081Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw42081 raw42081Labels = mixedMoment B raw42081step0 raw42081step0Labels := by
      have hz : ∀ j, raw42081 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42081step0 = (fun i j => raw42081 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42081step0 raw42081; decide +kernel
      have hl : raw42081step0Labels = raw42081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42081 raw42081Labels permutation346 hz
    mixedMoment B raw42081step0 raw42081step0Labels = mixedMoment B raw42081step1 raw42081step1Labels := by
      have ha : raw42081step1 = (fun i j => raw42081step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42081step1 raw42081step0; decide +kernel
      have hl : raw42081step1Labels = raw42081step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42081step0 raw42081step0Labels permutation32 permutation3
    mixedMoment B raw42081step1 raw42081step1Labels = mixedMoment B raw42081step2 raw42081step2Labels := by
      have ha : raw42081step2 = raw42081step1 := by apply Matrix.ext; unfold raw42081step2 raw42081step1; decide +kernel
      have hl : raw42081step1Labels = labelEmbedding7 ∘ raw42081step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42081step1 raw42081step1Labels raw42081step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw42082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42082Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42082step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42082step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42082step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42082 raw42082Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw42082 raw42082Labels = mixedMoment B raw42082step0 raw42082step0Labels := by
      have hz : ∀ j, raw42082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42082step0 = (fun i j => raw42082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42082step0 raw42082; decide +kernel
      have hl : raw42082step0Labels = raw42082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42082 raw42082Labels permutation346 hz
    mixedMoment B raw42082step0 raw42082step0Labels = mixedMoment B raw42082step1 raw42082step1Labels := by
      have ha : raw42082step1 = (fun i j => raw42082step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42082step1 raw42082step0; decide +kernel
      have hl : raw42082step1Labels = raw42082step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42082step0 raw42082step0Labels permutation151 permutation2
    mixedMoment B raw42082step1 raw42082step1Labels = mixedMoment B raw42082step2 raw42082step2Labels := by
      have ha : raw42082step2 = -raw42082step1 := by apply Matrix.ext; change ∀ i j, raw42082step2 i j = -(raw42082step1 i j); unfold raw42082step2 raw42082step1; decide +kernel
      have hl : raw42082step2Labels = raw42082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42082step2 raw42082step2Labels = mixedMoment B raw42082step3 raw42082step3Labels := by
      have ha : raw42082step3 = raw42082step2 := by apply Matrix.ext; unfold raw42082step3 raw42082step2; decide +kernel
      have hl : raw42082step2Labels = labelEmbedding1 ∘ raw42082step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42082step2 raw42082step2Labels raw42082step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw42083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42083Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42083step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42083step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42083step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42083 raw42083Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42083 raw42083Labels = mixedMoment B raw42083step0 raw42083step0Labels := by
      have hz : ∀ j, raw42083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42083step0 = (fun i j => raw42083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42083step0 raw42083; decide +kernel
      have hl : raw42083step0Labels = raw42083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42083 raw42083Labels permutation346 hz
    mixedMoment B raw42083step0 raw42083step0Labels = mixedMoment B raw42083step1 raw42083step1Labels := by
      have ha : raw42083step1 = (fun i j => raw42083step0 (permutation133 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42083step1 raw42083step0; decide +kernel
      have hl : raw42083step1Labels = raw42083step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42083step0 raw42083step0Labels permutation133 permutation7
    mixedMoment B raw42083step1 raw42083step1Labels = mixedMoment B raw42083step2 raw42083step2Labels := by
      have ha : raw42083step2 = raw42083step1 := by apply Matrix.ext; unfold raw42083step2 raw42083step1; decide +kernel
      have hl : raw42083step1Labels = labelEmbedding6 ∘ raw42083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42083step1 raw42083step1Labels raw42083step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw42084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42084Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42084step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42084step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42084step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42084 raw42084Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw42084 raw42084Labels = mixedMoment B raw42084step0 raw42084step0Labels := by
      have hz : ∀ j, raw42084 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42084step0 = (fun i j => raw42084 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42084step0 raw42084; decide +kernel
      have hl : raw42084step0Labels = raw42084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42084 raw42084Labels permutation346 hz
    mixedMoment B raw42084step0 raw42084step0Labels = mixedMoment B raw42084step1 raw42084step1Labels := by
      have ha : raw42084step1 = (fun i j => raw42084step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42084step1 raw42084step0; decide +kernel
      have hl : raw42084step1Labels = raw42084step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42084step0 raw42084step0Labels permutation151 permutation2
    mixedMoment B raw42084step1 raw42084step1Labels = mixedMoment B raw42084step2 raw42084step2Labels := by
      have ha : raw42084step2 = -raw42084step1 := by apply Matrix.ext; change ∀ i j, raw42084step2 i j = -(raw42084step1 i j); unfold raw42084step2 raw42084step1; decide +kernel
      have hl : raw42084step2Labels = raw42084step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42084step2 raw42084step2Labels = mixedMoment B raw42084step3 raw42084step3Labels := by
      have ha : raw42084step3 = raw42084step2 := by apply Matrix.ext; unfold raw42084step3 raw42084step2; decide +kernel
      have hl : raw42084step2Labels = labelEmbedding1 ∘ raw42084step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42084step2 raw42084step2Labels raw42084step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw42085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42085Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42085step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42085step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42085 raw42085Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42085 raw42085Labels = mixedMoment B raw42085step0 raw42085step0Labels := by
      have hz : ∀ j, raw42085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42085step0 = (fun i j => raw42085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42085step0 raw42085; decide +kernel
      have hl : raw42085step0Labels = raw42085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42085 raw42085Labels permutation346 hz
    mixedMoment B raw42085step0 raw42085step0Labels = mixedMoment B raw42085step1 raw42085step1Labels := by
      have ha : raw42085step1 = (fun i j => raw42085step0 (permutation146 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42085step1 raw42085step0; decide +kernel
      have hl : raw42085step1Labels = raw42085step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42085step0 raw42085step0Labels permutation146 permutation7
    mixedMoment B raw42085step1 raw42085step1Labels = mixedMoment B raw42085step2 raw42085step2Labels := by
      have ha : raw42085step2 = raw42085step1 := by apply Matrix.ext; unfold raw42085step2 raw42085step1; decide +kernel
      have hl : raw42085step1Labels = labelEmbedding6 ∘ raw42085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42085step1 raw42085step1Labels raw42085step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw42086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42086Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42086step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42086 raw42086Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw42086 raw42086Labels = mixedMoment B raw42086step0 raw42086step0Labels := by
      have hz : ∀ j, raw42086 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42086step0 = (fun i j => raw42086 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42086step0 raw42086; decide +kernel
      have hl : raw42086step0Labels = raw42086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42086 raw42086Labels permutation346 hz
    mixedMoment B raw42086step0 raw42086step0Labels = mixedMoment B raw42086step1 raw42086step1Labels := by
      have ha : raw42086step1 = (fun i j => raw42086step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42086step1 raw42086step0; decide +kernel
      have hl : raw42086step1Labels = raw42086step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42086step0 raw42086step0Labels permutation139 permutation4
    mixedMoment B raw42086step1 raw42086step1Labels = mixedMoment B raw42086step2 raw42086step2Labels := by
      have ha : raw42086step2 = raw42086step1 := by apply Matrix.ext; unfold raw42086step2 raw42086step1; decide +kernel
      have hl : raw42086step1Labels = labelEmbedding1 ∘ raw42086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42086step1 raw42086step1Labels raw42086step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw42087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42087Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42087step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42087step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42087 raw42087Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42087 raw42087Labels = mixedMoment B raw42087step0 raw42087step0Labels := by
      have hz : ∀ j, raw42087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42087step0 = (fun i j => raw42087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42087step0 raw42087; decide +kernel
      have hl : raw42087step0Labels = raw42087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42087 raw42087Labels permutation346 hz
    mixedMoment B raw42087step0 raw42087step0Labels = mixedMoment B raw42087step1 raw42087step1Labels := by
      have ha : raw42087step1 = (fun i j => raw42087step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42087step1 raw42087step0; decide +kernel
      have hl : raw42087step1Labels = raw42087step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42087step0 raw42087step0Labels permutation139 permutation4
    mixedMoment B raw42087step1 raw42087step1Labels = mixedMoment B raw42087step2 raw42087step2Labels := by
      have ha : raw42087step2 = raw42087step1 := by apply Matrix.ext; unfold raw42087step2 raw42087step1; decide +kernel
      have hl : raw42087step1Labels = labelEmbedding10 ∘ raw42087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42087step1 raw42087step1Labels raw42087step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw42088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42088Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42088 raw42088Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw42088 raw42088Labels = mixedMoment B raw42088step0 raw42088step0Labels := by
      have hz : ∀ j, raw42088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42088step0 = (fun i j => raw42088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42088step0 raw42088; decide +kernel
      have hl : raw42088step0Labels = raw42088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42088 raw42088Labels permutation346 hz
    mixedMoment B raw42088step0 raw42088step0Labels = mixedMoment B raw42088step1 raw42088step1Labels := by
      have ha : raw42088step1 = (fun i j => raw42088step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42088step1 raw42088step0; decide +kernel
      have hl : raw42088step1Labels = raw42088step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42088step0 raw42088step0Labels permutation149 permutation4
    mixedMoment B raw42088step1 raw42088step1Labels = mixedMoment B raw42088step2 raw42088step2Labels := by
      have ha : raw42088step2 = raw42088step1 := by apply Matrix.ext; unfold raw42088step2 raw42088step1; decide +kernel
      have hl : raw42088step1Labels = labelEmbedding1 ∘ raw42088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42088step1 raw42088step1Labels raw42088step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw42089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42089Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42089step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42089step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42089 raw42089Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw42089 raw42089Labels = mixedMoment B raw42089step0 raw42089step0Labels := by
      have hz : ∀ j, raw42089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42089step0 = (fun i j => raw42089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42089step0 raw42089; decide +kernel
      have hl : raw42089step0Labels = raw42089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42089 raw42089Labels permutation346 hz
    mixedMoment B raw42089step0 raw42089step0Labels = mixedMoment B raw42089step1 raw42089step1Labels := by
      have ha : raw42089step1 = (fun i j => raw42089step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42089step1 raw42089step0; decide +kernel
      have hl : raw42089step1Labels = raw42089step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42089step0 raw42089step0Labels permutation32 permutation3
    mixedMoment B raw42089step1 raw42089step1Labels = mixedMoment B raw42089step2 raw42089step2Labels := by
      have ha : raw42089step2 = raw42089step1 := by apply Matrix.ext; unfold raw42089step2 raw42089step1; decide +kernel
      have hl : raw42089step1Labels = labelEmbedding7 ∘ raw42089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42089step1 raw42089step1Labels raw42089step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw42090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42090Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42090 raw42090Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw42090 raw42090Labels = mixedMoment B raw42090step0 raw42090step0Labels := by
      have ha : raw42090step0 = (fun i j => raw42090 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42090step0 raw42090; decide +kernel
      have hl : raw42090step0Labels = raw42090Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42090 raw42090Labels permutation682 permutation2
    mixedMoment B raw42090step0 raw42090step0Labels = mixedMoment B raw42090step1 raw42090step1Labels := by
      have ha : raw42090step1 = -raw42090step0 := by apply Matrix.ext; change ∀ i j, raw42090step1 i j = -(raw42090step0 i j); unfold raw42090step1 raw42090step0; decide +kernel
      have hl : raw42090step1Labels = raw42090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42090step1 raw42090step1Labels = mixedMoment B raw42090step2 raw42090step2Labels := by
      have ha : raw42090step2 = raw42090step1 := by apply Matrix.ext; unfold raw42090step2 raw42090step1; decide +kernel
      have hl : raw42090step1Labels = labelEmbedding1 ∘ raw42090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42090step1 raw42090step1Labels raw42090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw42091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42091Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42091 raw42091Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42091 raw42091Labels = mixedMoment B raw42091step0 raw42091step0Labels := by
      have ha : raw42091step0 = (fun i j => raw42091 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42091step0 raw42091; decide +kernel
      have hl : raw42091step0Labels = raw42091Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42091 raw42091Labels permutation668 permutation7
    mixedMoment B raw42091step0 raw42091step0Labels = mixedMoment B raw42091step1 raw42091step1Labels := by
      have ha : raw42091step1 = raw42091step0 := by apply Matrix.ext; unfold raw42091step1 raw42091step0; decide +kernel
      have hl : raw42091step0Labels = labelEmbedding6 ∘ raw42091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42091step0 raw42091step0Labels raw42091step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw42092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42092Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42092step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42092 raw42092Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw42092 raw42092Labels = mixedMoment B raw42092step0 raw42092step0Labels := by
      have ha : raw42092step0 = (fun i j => raw42092 (permutation634 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42092step0 raw42092; decide +kernel
      have hl : raw42092step0Labels = raw42092Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42092 raw42092Labels permutation634 permutation4
    mixedMoment B raw42092step0 raw42092step0Labels = mixedMoment B raw42092step1 raw42092step1Labels := by
      have ha : raw42092step1 = raw42092step0 := by apply Matrix.ext; unfold raw42092step1 raw42092step0; decide +kernel
      have hl : raw42092step0Labels = labelEmbedding1 ∘ raw42092step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42092step0 raw42092step0Labels raw42092step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw42093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42093Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42093step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42093 raw42093Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42093 raw42093Labels = mixedMoment B raw42093step0 raw42093step0Labels := by
      have ha : raw42093step0 = (fun i j => raw42093 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42093step0 raw42093; decide +kernel
      have hl : raw42093step0Labels = raw42093Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42093 raw42093Labels permutation152 permutation3
    mixedMoment B raw42093step0 raw42093step0Labels = mixedMoment B raw42093step1 raw42093step1Labels := by
      have ha : raw42093step1 = raw42093step0 := by apply Matrix.ext; unfold raw42093step1 raw42093step0; decide +kernel
      have hl : raw42093step0Labels = labelEmbedding7 ∘ raw42093step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42093step0 raw42093step0Labels raw42093step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw42094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42094Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42094step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42094 raw42094Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw42094 raw42094Labels = mixedMoment B raw42094step0 raw42094step0Labels := by
      have ha : raw42094step0 = (fun i j => raw42094 (permutation203 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42094step0 raw42094; decide +kernel
      have hl : raw42094step0Labels = raw42094Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42094 raw42094Labels permutation203 permutation4
    mixedMoment B raw42094step0 raw42094step0Labels = mixedMoment B raw42094step1 raw42094step1Labels := by
      have ha : raw42094step1 = -raw42094step0 := by apply Matrix.ext; change ∀ i j, raw42094step1 i j = -(raw42094step0 i j); unfold raw42094step1 raw42094step0; decide +kernel
      have hl : raw42094step1Labels = raw42094step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42094step1 raw42094step1Labels = mixedMoment B raw42094step2 raw42094step2Labels := by
      have ha : raw42094step2 = raw42094step1 := by apply Matrix.ext; unfold raw42094step2 raw42094step1; decide +kernel
      have hl : raw42094step1Labels = labelEmbedding1 ∘ raw42094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42094step1 raw42094step1Labels raw42094step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw42095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42095Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42095step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42095 raw42095Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw42095 raw42095Labels = mixedMoment B raw42095step0 raw42095step0Labels := by
      have ha : raw42095step0 = (fun i j => raw42095 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42095step0 raw42095; decide +kernel
      have hl : raw42095step0Labels = raw42095Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42095 raw42095Labels permutation152 permutation3
    mixedMoment B raw42095step0 raw42095step0Labels = mixedMoment B raw42095step1 raw42095step1Labels := by
      have ha : raw42095step1 = raw42095step0 := by apply Matrix.ext; unfold raw42095step1 raw42095step0; decide +kernel
      have hl : raw42095step0Labels = labelEmbedding7 ∘ raw42095step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42095step0 raw42095step0Labels raw42095step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw42096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42096Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42096step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42096 raw42096Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw42096 raw42096Labels = mixedMoment B raw42096step0 raw42096step0Labels := by
      have ha : raw42096step0 = (fun i j => raw42096 (permutation423 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42096step0 raw42096; decide +kernel
      have hl : raw42096step0Labels = raw42096Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42096 raw42096Labels permutation423 permutation4
    mixedMoment B raw42096step0 raw42096step0Labels = mixedMoment B raw42096step1 raw42096step1Labels := by
      have ha : raw42096step1 = raw42096step0 := by apply Matrix.ext; unfold raw42096step1 raw42096step0; decide +kernel
      have hl : raw42096step0Labels = labelEmbedding1 ∘ raw42096step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42096step0 raw42096step0Labels raw42096step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw42097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42097Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42097step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42097 raw42097Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42097 raw42097Labels = mixedMoment B raw42097step0 raw42097step0Labels := by
      have ha : raw42097step0 = (fun i j => raw42097 (permutation423 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42097step0 raw42097; decide +kernel
      have hl : raw42097step0Labels = raw42097Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42097 raw42097Labels permutation423 permutation4
    mixedMoment B raw42097step0 raw42097step0Labels = mixedMoment B raw42097step1 raw42097step1Labels := by
      have ha : raw42097step1 = raw42097step0 := by apply Matrix.ext; unfold raw42097step1 raw42097step0; decide +kernel
      have hl : raw42097step0Labels = labelEmbedding10 ∘ raw42097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42097step0 raw42097step0Labels raw42097step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw42098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42098Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42098 raw42098Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw42098 raw42098Labels = mixedMoment B raw42098step0 raw42098step0Labels := by
      have hz : ∀ j, raw42098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42098step0 = (fun i j => raw42098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42098step0 raw42098; decide +kernel
      have hl : raw42098step0Labels = raw42098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42098 raw42098Labels permutation434 hz
    mixedMoment B raw42098step0 raw42098step0Labels = mixedMoment B raw42098step1 raw42098step1Labels := by
      have ha : raw42098step1 = raw42098step0 := by apply Matrix.ext; unfold raw42098step1 raw42098step0; decide +kernel
      have hl : raw42098step0Labels = labelEmbedding1 ∘ raw42098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42098step0 raw42098step0Labels raw42098step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw42099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42099Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42099step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw42099step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42099step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42099step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42099step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42099 raw42099Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw42099 raw42099Labels = mixedMoment B raw42099step0 raw42099step0Labels := by
      have hz : ∀ j, raw42099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42099step0 = (fun i j => raw42099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42099step0 raw42099; decide +kernel
      have hl : raw42099step0Labels = raw42099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42099 raw42099Labels permutation434 hz
    mixedMoment B raw42099step0 raw42099step0Labels = mixedMoment B raw42099step1 raw42099step1Labels := by
      have ha : raw42099step1 = (fun i j => raw42099step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42099step1 raw42099step0; decide +kernel
      have hl : raw42099step1Labels = raw42099step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42099step0 raw42099step0Labels permutation151 permutation3
    mixedMoment B raw42099step1 raw42099step1Labels = mixedMoment B raw42099step2 raw42099step2Labels := by
      have ha : raw42099step2 = -raw42099step1 := by apply Matrix.ext; change ∀ i j, raw42099step2 i j = -(raw42099step1 i j); unfold raw42099step2 raw42099step1; decide +kernel
      have hl : raw42099step2Labels = raw42099step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42099step2 raw42099step2Labels = mixedMoment B raw42099step3 raw42099step3Labels := by
      have ha : raw42099step3 = raw42099step2 := by apply Matrix.ext; unfold raw42099step3 raw42099step2; decide +kernel
      have hl : raw42099step2Labels = labelEmbedding7 ∘ raw42099step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42099step2 raw42099step2Labels raw42099step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw42100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42100Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42100step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42100step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42100step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42100 raw42100Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw42100 raw42100Labels = mixedMoment B raw42100step0 raw42100step0Labels := by
      have hz : ∀ j, raw42100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42100step0 = (fun i j => raw42100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42100step0 raw42100; decide +kernel
      have hl : raw42100step0Labels = raw42100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42100 raw42100Labels permutation434 hz
    mixedMoment B raw42100step0 raw42100step0Labels = mixedMoment B raw42100step1 raw42100step1Labels := by
      have ha : raw42100step1 = (fun i j => raw42100step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42100step1 raw42100step0; decide +kernel
      have hl : raw42100step1Labels = raw42100step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42100step0 raw42100step0Labels permutation151 permutation2
    mixedMoment B raw42100step1 raw42100step1Labels = mixedMoment B raw42100step2 raw42100step2Labels := by
      have ha : raw42100step2 = -raw42100step1 := by apply Matrix.ext; change ∀ i j, raw42100step2 i j = -(raw42100step1 i j); unfold raw42100step2 raw42100step1; decide +kernel
      have hl : raw42100step2Labels = raw42100step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42100step2 raw42100step2Labels = mixedMoment B raw42100step3 raw42100step3Labels := by
      have ha : raw42100step3 = raw42100step2 := by apply Matrix.ext; unfold raw42100step3 raw42100step2; decide +kernel
      have hl : raw42100step2Labels = labelEmbedding1 ∘ raw42100step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42100step2 raw42100step2Labels raw42100step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw42101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42101Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42101step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw42101step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42101step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42101step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42101step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42101 raw42101Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw42101 raw42101Labels = mixedMoment B raw42101step0 raw42101step0Labels := by
      have hz : ∀ j, raw42101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42101step0 = (fun i j => raw42101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42101step0 raw42101; decide +kernel
      have hl : raw42101step0Labels = raw42101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42101 raw42101Labels permutation434 hz
    mixedMoment B raw42101step0 raw42101step0Labels = mixedMoment B raw42101step1 raw42101step1Labels := by
      have ha : raw42101step1 = (fun i j => raw42101step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42101step1 raw42101step0; decide +kernel
      have hl : raw42101step1Labels = raw42101step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42101step0 raw42101step0Labels permutation38 permutation5
    mixedMoment B raw42101step1 raw42101step1Labels = mixedMoment B raw42101step2 raw42101step2Labels := by
      have ha : raw42101step2 = -raw42101step1 := by apply Matrix.ext; change ∀ i j, raw42101step2 i j = -(raw42101step1 i j); unfold raw42101step2 raw42101step1; decide +kernel
      have hl : raw42101step2Labels = raw42101step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42101step2 raw42101step2Labels = mixedMoment B raw42101step3 raw42101step3Labels := by
      have ha : raw42101step3 = raw42101step2 := by apply Matrix.ext; unfold raw42101step3 raw42101step2; decide +kernel
      have hl : raw42101step2Labels = labelEmbedding9 ∘ raw42101step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42101step2 raw42101step2Labels raw42101step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw42102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42102Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42102step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42102step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42102step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42102step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42102 raw42102Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw42102 raw42102Labels = mixedMoment B raw42102step0 raw42102step0Labels := by
      have hz : ∀ j, raw42102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42102step0 = (fun i j => raw42102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42102step0 raw42102; decide +kernel
      have hl : raw42102step0Labels = raw42102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42102 raw42102Labels permutation434 hz
    mixedMoment B raw42102step0 raw42102step0Labels = mixedMoment B raw42102step1 raw42102step1Labels := by
      have ha : raw42102step1 = (fun i j => raw42102step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42102step1 raw42102step0; decide +kernel
      have hl : raw42102step1Labels = raw42102step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42102step0 raw42102step0Labels permutation151 permutation2
    mixedMoment B raw42102step1 raw42102step1Labels = mixedMoment B raw42102step2 raw42102step2Labels := by
      have ha : raw42102step2 = -raw42102step1 := by apply Matrix.ext; change ∀ i j, raw42102step2 i j = -(raw42102step1 i j); unfold raw42102step2 raw42102step1; decide +kernel
      have hl : raw42102step2Labels = raw42102step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42102step2 raw42102step2Labels = mixedMoment B raw42102step3 raw42102step3Labels := by
      have ha : raw42102step3 = raw42102step2 := by apply Matrix.ext; unfold raw42102step3 raw42102step2; decide +kernel
      have hl : raw42102step2Labels = labelEmbedding1 ∘ raw42102step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42102step2 raw42102step2Labels raw42102step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw42103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42103Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42103step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42103step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42103step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42103step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42103step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42103 raw42103Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw42103 raw42103Labels = mixedMoment B raw42103step0 raw42103step0Labels := by
      have hz : ∀ j, raw42103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42103step0 = (fun i j => raw42103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42103step0 raw42103; decide +kernel
      have hl : raw42103step0Labels = raw42103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42103 raw42103Labels permutation434 hz
    mixedMoment B raw42103step0 raw42103step0Labels = mixedMoment B raw42103step1 raw42103step1Labels := by
      have ha : raw42103step1 = (fun i j => raw42103step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42103step1 raw42103step0; decide +kernel
      have hl : raw42103step1Labels = raw42103step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42103step0 raw42103step0Labels permutation42 permutation5
    mixedMoment B raw42103step1 raw42103step1Labels = mixedMoment B raw42103step2 raw42103step2Labels := by
      have ha : raw42103step2 = -raw42103step1 := by apply Matrix.ext; change ∀ i j, raw42103step2 i j = -(raw42103step1 i j); unfold raw42103step2 raw42103step1; decide +kernel
      have hl : raw42103step2Labels = raw42103step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42103step2 raw42103step2Labels = mixedMoment B raw42103step3 raw42103step3Labels := by
      have ha : raw42103step3 = raw42103step2 := by apply Matrix.ext; unfold raw42103step3 raw42103step2; decide +kernel
      have hl : raw42103step2Labels = labelEmbedding9 ∘ raw42103step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42103step2 raw42103step2Labels raw42103step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw42104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42104Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42104step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42104step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42104step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42104 raw42104Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw42104 raw42104Labels = mixedMoment B raw42104step0 raw42104step0Labels := by
      have ha : raw42104step0 = (fun i j => raw42104 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42104step0 raw42104; decide +kernel
      have hl : raw42104step0Labels = raw42104Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42104 raw42104Labels permutation682 permutation2
    mixedMoment B raw42104step0 raw42104step0Labels = mixedMoment B raw42104step1 raw42104step1Labels := by
      have ha : raw42104step1 = -raw42104step0 := by apply Matrix.ext; change ∀ i j, raw42104step1 i j = -(raw42104step0 i j); unfold raw42104step1 raw42104step0; decide +kernel
      have hl : raw42104step1Labels = raw42104step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42104step1 raw42104step1Labels = mixedMoment B raw42104step2 raw42104step2Labels := by
      have ha : raw42104step2 = raw42104step1 := by apply Matrix.ext; unfold raw42104step2 raw42104step1; decide +kernel
      have hl : raw42104step1Labels = labelEmbedding1 ∘ raw42104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42104step1 raw42104step1Labels raw42104step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw42105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42105Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42105step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42105step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42105step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42105 raw42105Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42105 raw42105Labels = mixedMoment B raw42105step0 raw42105step0Labels := by
      have ha : raw42105step0 = (fun i j => raw42105 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42105step0 raw42105; decide +kernel
      have hl : raw42105step0Labels = raw42105Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42105 raw42105Labels permutation682 permutation2
    mixedMoment B raw42105step0 raw42105step0Labels = mixedMoment B raw42105step1 raw42105step1Labels := by
      have ha : raw42105step1 = -raw42105step0 := by apply Matrix.ext; change ∀ i j, raw42105step1 i j = -(raw42105step0 i j); unfold raw42105step1 raw42105step0; decide +kernel
      have hl : raw42105step1Labels = raw42105step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42105step1 raw42105step1Labels = mixedMoment B raw42105step2 raw42105step2Labels := by
      have ha : raw42105step2 = raw42105step1 := by apply Matrix.ext; unfold raw42105step2 raw42105step1; decide +kernel
      have hl : raw42105step1Labels = labelEmbedding8 ∘ raw42105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42105step1 raw42105step1Labels raw42105step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw42106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42106Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42106step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42106 raw42106Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw42106 raw42106Labels = mixedMoment B raw42106step0 raw42106step0Labels := by
      have ha : raw42106step0 = (fun i j => raw42106 (permutation616 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42106step0 raw42106; decide +kernel
      have hl : raw42106step0Labels = raw42106Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42106 raw42106Labels permutation616 permutation4
    mixedMoment B raw42106step0 raw42106step0Labels = mixedMoment B raw42106step1 raw42106step1Labels := by
      have ha : raw42106step1 = raw42106step0 := by apply Matrix.ext; unfold raw42106step1 raw42106step0; decide +kernel
      have hl : raw42106step0Labels = labelEmbedding1 ∘ raw42106step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42106step0 raw42106step0Labels raw42106step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw42107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42107Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42107step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42107step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42107step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42107 raw42107Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42107 raw42107Labels = mixedMoment B raw42107step0 raw42107step0Labels := by
      have ha : raw42107step0 = (fun i j => raw42107 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42107step0 raw42107; decide +kernel
      have hl : raw42107step0Labels = raw42107Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42107 raw42107Labels permutation184 permutation5
    mixedMoment B raw42107step0 raw42107step0Labels = mixedMoment B raw42107step1 raw42107step1Labels := by
      have ha : raw42107step1 = -raw42107step0 := by apply Matrix.ext; change ∀ i j, raw42107step1 i j = -(raw42107step0 i j); unfold raw42107step1 raw42107step0; decide +kernel
      have hl : raw42107step1Labels = raw42107step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42107step1 raw42107step1Labels = mixedMoment B raw42107step2 raw42107step2Labels := by
      have ha : raw42107step2 = raw42107step1 := by apply Matrix.ext; unfold raw42107step2 raw42107step1; decide +kernel
      have hl : raw42107step1Labels = labelEmbedding9 ∘ raw42107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42107step1 raw42107step1Labels raw42107step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw42108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42108Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42108step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42108step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42108 raw42108Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw42108 raw42108Labels = mixedMoment B raw42108step0 raw42108step0Labels := by
      have ha : raw42108step0 = (fun i j => raw42108 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42108step0 raw42108; decide +kernel
      have hl : raw42108step0Labels = raw42108Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42108 raw42108Labels permutation155 permutation2
    mixedMoment B raw42108step0 raw42108step0Labels = mixedMoment B raw42108step1 raw42108step1Labels := by
      have ha : raw42108step1 = raw42108step0 := by apply Matrix.ext; unfold raw42108step1 raw42108step0; decide +kernel
      have hl : raw42108step0Labels = labelEmbedding1 ∘ raw42108step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42108step0 raw42108step0Labels raw42108step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw42109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42109Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw42109step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42109step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42109step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42109 raw42109Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw42109 raw42109Labels = mixedMoment B raw42109step0 raw42109step0Labels := by
      have ha : raw42109step0 = (fun i j => raw42109 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42109step0 raw42109; decide +kernel
      have hl : raw42109step0Labels = raw42109Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42109 raw42109Labels permutation182 permutation5
    mixedMoment B raw42109step0 raw42109step0Labels = mixedMoment B raw42109step1 raw42109step1Labels := by
      have ha : raw42109step1 = -raw42109step0 := by apply Matrix.ext; change ∀ i j, raw42109step1 i j = -(raw42109step0 i j); unfold raw42109step1 raw42109step0; decide +kernel
      have hl : raw42109step1Labels = raw42109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42109step1 raw42109step1Labels = mixedMoment B raw42109step2 raw42109step2Labels := by
      have ha : raw42109step2 = raw42109step1 := by apply Matrix.ext; unfold raw42109step2 raw42109step1; decide +kernel
      have hl : raw42109step1Labels = labelEmbedding9 ∘ raw42109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42109step1 raw42109step1Labels raw42109step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw42110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42110Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42110step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42110step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42110 raw42110Labels = mixedMoment B node4030 node4030Labels := by
  calc
    mixedMoment B raw42110 raw42110Labels = mixedMoment B raw42110step0 raw42110step0Labels := by
      have hz : ∀ j, raw42110 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42110step0 = (fun i j => raw42110 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42110step0 raw42110; decide +kernel
      have hl : raw42110step0Labels = raw42110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42110 raw42110Labels permutation434 hz
    mixedMoment B raw42110step0 raw42110step0Labels = mixedMoment B raw42110step1 raw42110step1Labels := by
      have hz : ∀ j, raw42110step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42110step1 = (fun i j => raw42110step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42110step1 raw42110step0; decide +kernel
      have hl : raw42110step1Labels = raw42110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42110step0 raw42110step0Labels permutation80 hz
    mixedMoment B raw42110step1 raw42110step1Labels = mixedMoment B raw42110step2 raw42110step2Labels := by
      have ha : raw42110step2 = raw42110step1 := by apply Matrix.ext; unfold raw42110step2 raw42110step1; decide +kernel
      have hl : raw42110step1Labels = labelEmbedding1 ∘ raw42110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42110step1 raw42110step1Labels raw42110step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4030 node4030Labels := by rfl

def raw42111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42111Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42111step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw42111step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42111step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42111step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42111step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42111 raw42111Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw42111 raw42111Labels = mixedMoment B raw42111step0 raw42111step0Labels := by
      have hz : ∀ j, raw42111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42111step0 = (fun i j => raw42111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42111step0 raw42111; decide +kernel
      have hl : raw42111step0Labels = raw42111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42111 raw42111Labels permutation434 hz
    mixedMoment B raw42111step0 raw42111step0Labels = mixedMoment B raw42111step1 raw42111step1Labels := by
      have hz : ∀ j, raw42111step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42111step1 = (fun i j => raw42111step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42111step1 raw42111step0; decide +kernel
      have hl : raw42111step1Labels = raw42111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42111step0 raw42111step0Labels permutation80 hz
    mixedMoment B raw42111step1 raw42111step1Labels = mixedMoment B raw42111step2 raw42111step2Labels := by
      have ha : raw42111step2 = (fun i j => raw42111step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42111step2 raw42111step1; decide +kernel
      have hl : raw42111step2Labels = raw42111step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42111step1 raw42111step1Labels permutation8 permutation3
    mixedMoment B raw42111step2 raw42111step2Labels = mixedMoment B raw42111step3 raw42111step3Labels := by
      have ha : raw42111step3 = raw42111step2 := by apply Matrix.ext; unfold raw42111step3 raw42111step2; decide +kernel
      have hl : raw42111step2Labels = labelEmbedding7 ∘ raw42111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42111step2 raw42111step2Labels raw42111step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
