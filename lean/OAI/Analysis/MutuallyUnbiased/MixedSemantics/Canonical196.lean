import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw25088 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25088step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw25088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25088 raw25088Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw25088 raw25088Labels = mixedMoment B raw25088step0 raw25088step0Labels := by
      have hz : ∀ j, raw25088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25088step0 = (fun i j => raw25088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25088step0 raw25088; decide +kernel
      have hl : raw25088step0Labels = raw25088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25088 raw25088Labels permutation346 hz
    mixedMoment B raw25088step0 raw25088step0Labels = mixedMoment B raw25088step1 raw25088step1Labels := by
      have ha : raw25088step1 = (fun i j => raw25088step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25088step1 raw25088step0; decide +kernel
      have hl : raw25088step1Labels = raw25088step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25088step0 raw25088step0Labels permutation32 permutation7
    mixedMoment B raw25088step1 raw25088step1Labels = mixedMoment B raw25088step2 raw25088step2Labels := by
      have ha : raw25088step2 = raw25088step1 := by apply Matrix.ext; unfold raw25088step2 raw25088step1; decide +kernel
      have hl : raw25088step1Labels = labelEmbedding10 ∘ raw25088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25088step1 raw25088step1Labels raw25088step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw25089 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw25089step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25089step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw25089step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25089step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25089 raw25089Labels = mixedMoment B node4275 node4275Labels := by
  calc
    mixedMoment B raw25089 raw25089Labels = mixedMoment B raw25089step0 raw25089step0Labels := by
      have hz : ∀ j, raw25089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25089step0 = (fun i j => raw25089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25089step0 raw25089; decide +kernel
      have hl : raw25089step0Labels = raw25089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25089 raw25089Labels permutation346 hz
    mixedMoment B raw25089step0 raw25089step0Labels = mixedMoment B raw25089step1 raw25089step1Labels := by
      have ha : raw25089step1 = (fun i j => raw25089step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw25089step1 raw25089step0; decide +kernel
      have hl : raw25089step1Labels = raw25089step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25089step0 raw25089step0Labels permutation53 permutation4
    mixedMoment B raw25089step1 raw25089step1Labels = mixedMoment B raw25089step2 raw25089step2Labels := by
      have ha : raw25089step2 = -raw25089step1 := by apply Matrix.ext; change ∀ i j, raw25089step2 i j = -(raw25089step1 i j); unfold raw25089step2 raw25089step1; decide +kernel
      have hl : raw25089step2Labels = raw25089step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25089step2 raw25089step2Labels = mixedMoment B raw25089step3 raw25089step3Labels := by
      have ha : raw25089step3 = raw25089step2 := by apply Matrix.ext; unfold raw25089step3 raw25089step2; decide +kernel
      have hl : raw25089step2Labels = labelEmbedding7 ∘ raw25089step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25089step2 raw25089step2Labels raw25089step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4275 node4275Labels := by rfl

def raw25090 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25090step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25090 raw25090Labels = mixedMoment B node4409 node4409Labels := by
  calc
    mixedMoment B raw25090 raw25090Labels = mixedMoment B raw25090step0 raw25090step0Labels := by
      have ha : raw25090step0 = (fun i j => raw25090 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25090step0 raw25090; decide +kernel
      have hl : raw25090step0Labels = raw25090Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25090 raw25090Labels permutation176 permutation6
    mixedMoment B raw25090step0 raw25090step0Labels = mixedMoment B raw25090step1 raw25090step1Labels := by
      have ha : raw25090step1 = raw25090step0 := by apply Matrix.ext; unfold raw25090step1 raw25090step0; decide +kernel
      have hl : raw25090step0Labels = labelEmbedding9 ∘ raw25090step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25090step0 raw25090step0Labels raw25090step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4409 node4409Labels := by rfl

def raw25091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25091step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25091 raw25091Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw25091 raw25091Labels = mixedMoment B raw25091step0 raw25091step0Labels := by
      have hz : ∀ j, raw25091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25091step0 = (fun i j => raw25091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25091step0 raw25091; decide +kernel
      have hl : raw25091step0Labels = raw25091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25091 raw25091Labels permutation346 hz
    mixedMoment B raw25091step0 raw25091step0Labels = mixedMoment B raw25091step1 raw25091step1Labels := by
      have ha : raw25091step1 = (fun i j => raw25091step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25091step1 raw25091step0; decide +kernel
      have hl : raw25091step1Labels = raw25091step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25091step0 raw25091step0Labels permutation32 permutation6
    mixedMoment B raw25091step1 raw25091step1Labels = mixedMoment B raw25091step2 raw25091step2Labels := by
      have ha : raw25091step2 = raw25091step1 := by apply Matrix.ext; unfold raw25091step2 raw25091step1; decide +kernel
      have hl : raw25091step1Labels = labelEmbedding9 ∘ raw25091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25091step1 raw25091step1Labels raw25091step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw25092 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25092step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25092 raw25092Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw25092 raw25092Labels = mixedMoment B raw25092step0 raw25092step0Labels := by
      have hz : ∀ j, raw25092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25092step0 = (fun i j => raw25092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25092step0 raw25092; decide +kernel
      have hl : raw25092step0Labels = raw25092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25092 raw25092Labels permutation346 hz
    mixedMoment B raw25092step0 raw25092step0Labels = mixedMoment B raw25092step1 raw25092step1Labels := by
      have ha : raw25092step1 = (fun i j => raw25092step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25092step1 raw25092step0; decide +kernel
      have hl : raw25092step1Labels = raw25092step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25092step0 raw25092step0Labels permutation34 permutation6
    mixedMoment B raw25092step1 raw25092step1Labels = mixedMoment B raw25092step2 raw25092step2Labels := by
      have ha : raw25092step2 = raw25092step1 := by apply Matrix.ext; unfold raw25092step2 raw25092step1; decide +kernel
      have hl : raw25092step1Labels = labelEmbedding9 ∘ raw25092step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25092step1 raw25092step1Labels raw25092step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw25093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25093step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25093step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25093 raw25093Labels = mixedMoment B node4477 node4477Labels := by
  calc
    mixedMoment B raw25093 raw25093Labels = mixedMoment B raw25093step0 raw25093step0Labels := by
      have hz : ∀ j, raw25093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25093step0 = (fun i j => raw25093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25093step0 raw25093; decide +kernel
      have hl : raw25093step0Labels = raw25093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25093 raw25093Labels permutation346 hz
    mixedMoment B raw25093step0 raw25093step0Labels = mixedMoment B raw25093step1 raw25093step1Labels := by
      have ha : raw25093step1 = (fun i j => raw25093step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25093step1 raw25093step0; decide +kernel
      have hl : raw25093step1Labels = raw25093step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25093step0 raw25093step0Labels permutation32 permutation6
    mixedMoment B raw25093step1 raw25093step1Labels = mixedMoment B raw25093step2 raw25093step2Labels := by
      have ha : raw25093step2 = raw25093step1 := by apply Matrix.ext; unfold raw25093step2 raw25093step1; decide +kernel
      have hl : raw25093step1Labels = labelEmbedding9 ∘ raw25093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25093step1 raw25093step1Labels raw25093step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4477 node4477Labels := by rfl

def raw25094 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25094step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25094 raw25094Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw25094 raw25094Labels = mixedMoment B raw25094step0 raw25094step0Labels := by
      have ha : raw25094step0 = (fun i j => raw25094 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25094step0 raw25094; decide +kernel
      have hl : raw25094step0Labels = raw25094Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25094 raw25094Labels permutation152 permutation6
    mixedMoment B raw25094step0 raw25094step0Labels = mixedMoment B raw25094step1 raw25094step1Labels := by
      have ha : raw25094step1 = raw25094step0 := by apply Matrix.ext; unfold raw25094step1 raw25094step0; decide +kernel
      have hl : raw25094step0Labels = labelEmbedding9 ∘ raw25094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25094step0 raw25094step0Labels raw25094step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

def raw25095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25095step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25095step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25095 raw25095Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw25095 raw25095Labels = mixedMoment B raw25095step0 raw25095step0Labels := by
      have hz : ∀ j, raw25095 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25095step0 = (fun i j => raw25095 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25095step0 raw25095; decide +kernel
      have hl : raw25095step0Labels = raw25095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25095 raw25095Labels permutation265 hz
    mixedMoment B raw25095step0 raw25095step0Labels = mixedMoment B raw25095step1 raw25095step1Labels := by
      have ha : raw25095step1 = (fun i j => raw25095step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25095step1 raw25095step0; decide +kernel
      have hl : raw25095step1Labels = raw25095step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25095step0 raw25095step0Labels permutation32 permutation6
    mixedMoment B raw25095step1 raw25095step1Labels = mixedMoment B raw25095step2 raw25095step2Labels := by
      have ha : raw25095step2 = raw25095step1 := by apply Matrix.ext; unfold raw25095step2 raw25095step1; decide +kernel
      have hl : raw25095step1Labels = labelEmbedding9 ∘ raw25095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25095step1 raw25095step1Labels raw25095step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw25096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25096step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25096 raw25096Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw25096 raw25096Labels = mixedMoment B raw25096step0 raw25096step0Labels := by
      have ha : raw25096step0 = (fun i j => raw25096 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25096step0 raw25096; decide +kernel
      have hl : raw25096step0Labels = raw25096Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25096 raw25096Labels permutation152 permutation6
    mixedMoment B raw25096step0 raw25096step0Labels = mixedMoment B raw25096step1 raw25096step1Labels := by
      have ha : raw25096step1 = raw25096step0 := by apply Matrix.ext; unfold raw25096step1 raw25096step0; decide +kernel
      have hl : raw25096step0Labels = labelEmbedding9 ∘ raw25096step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25096step0 raw25096step0Labels raw25096step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw25097 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25097step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25097 raw25097Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw25097 raw25097Labels = mixedMoment B raw25097step0 raw25097step0Labels := by
      have ha : raw25097step0 = (fun i j => raw25097 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25097step0 raw25097; decide +kernel
      have hl : raw25097step0Labels = raw25097Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25097 raw25097Labels permutation154 permutation6
    mixedMoment B raw25097step0 raw25097step0Labels = mixedMoment B raw25097step1 raw25097step1Labels := by
      have ha : raw25097step1 = raw25097step0 := by apply Matrix.ext; unfold raw25097step1 raw25097step0; decide +kernel
      have hl : raw25097step0Labels = labelEmbedding9 ∘ raw25097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25097step0 raw25097step0Labels raw25097step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw25098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25098step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25098 raw25098Labels = mixedMoment B node4441 node4441Labels := by
  calc
    mixedMoment B raw25098 raw25098Labels = mixedMoment B raw25098step0 raw25098step0Labels := by
      have ha : raw25098step0 = (fun i j => raw25098 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25098step0 raw25098; decide +kernel
      have hl : raw25098step0Labels = raw25098Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25098 raw25098Labels permutation152 permutation6
    mixedMoment B raw25098step0 raw25098step0Labels = mixedMoment B raw25098step1 raw25098step1Labels := by
      have ha : raw25098step1 = raw25098step0 := by apply Matrix.ext; unfold raw25098step1 raw25098step0; decide +kernel
      have hl : raw25098step0Labels = labelEmbedding9 ∘ raw25098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25098step0 raw25098step0Labels raw25098step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4441 node4441Labels := by rfl

def raw25099 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25099step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25099step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25099 raw25099Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw25099 raw25099Labels = mixedMoment B raw25099step0 raw25099step0Labels := by
      have hz : ∀ j, raw25099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25099step0 = (fun i j => raw25099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25099step0 raw25099; decide +kernel
      have hl : raw25099step0Labels = raw25099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25099 raw25099Labels permutation346 hz
    mixedMoment B raw25099step0 raw25099step0Labels = mixedMoment B raw25099step1 raw25099step1Labels := by
      have ha : raw25099step1 = (fun i j => raw25099step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25099step1 raw25099step0; decide +kernel
      have hl : raw25099step1Labels = raw25099step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25099step0 raw25099step0Labels permutation34 permutation6
    mixedMoment B raw25099step1 raw25099step1Labels = mixedMoment B raw25099step2 raw25099step2Labels := by
      have ha : raw25099step2 = raw25099step1 := by apply Matrix.ext; unfold raw25099step2 raw25099step1; decide +kernel
      have hl : raw25099step1Labels = labelEmbedding9 ∘ raw25099step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25099step1 raw25099step1Labels raw25099step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw25100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25100step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25100step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25100step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25100 raw25100Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw25100 raw25100Labels = mixedMoment B raw25100step0 raw25100step0Labels := by
      have hz : ∀ j, raw25100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25100step0 = (fun i j => raw25100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25100step0 raw25100; decide +kernel
      have hl : raw25100step0Labels = raw25100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25100 raw25100Labels permutation346 hz
    mixedMoment B raw25100step0 raw25100step0Labels = mixedMoment B raw25100step1 raw25100step1Labels := by
      have hz : ∀ j, raw25100step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25100step1 = (fun i j => raw25100step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25100step1 raw25100step0; decide +kernel
      have hl : raw25100step1Labels = raw25100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25100step0 raw25100step0Labels permutation56 hz
    mixedMoment B raw25100step1 raw25100step1Labels = mixedMoment B raw25100step2 raw25100step2Labels := by
      have ha : raw25100step2 = (fun i j => raw25100step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25100step2 raw25100step1; decide +kernel
      have hl : raw25100step2Labels = raw25100step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25100step1 raw25100step1Labels permutation10 permutation6
    mixedMoment B raw25100step2 raw25100step2Labels = mixedMoment B raw25100step3 raw25100step3Labels := by
      have ha : raw25100step3 = raw25100step2 := by apply Matrix.ext; unfold raw25100step3 raw25100step2; decide +kernel
      have hl : raw25100step2Labels = labelEmbedding9 ∘ raw25100step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25100step2 raw25100step2Labels raw25100step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw25101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25101step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25101 raw25101Labels = mixedMoment B node4400 node4400Labels := by
  calc
    mixedMoment B raw25101 raw25101Labels = mixedMoment B raw25101step0 raw25101step0Labels := by
      have ha : raw25101step0 = (fun i j => raw25101 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25101step0 raw25101; decide +kernel
      have hl : raw25101step0Labels = raw25101Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25101 raw25101Labels permutation178 permutation6
    mixedMoment B raw25101step0 raw25101step0Labels = mixedMoment B raw25101step1 raw25101step1Labels := by
      have ha : raw25101step1 = raw25101step0 := by apply Matrix.ext; unfold raw25101step1 raw25101step0; decide +kernel
      have hl : raw25101step0Labels = labelEmbedding9 ∘ raw25101step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25101step0 raw25101step0Labels raw25101step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4400 node4400Labels := by rfl

def raw25102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25102step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25102 raw25102Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw25102 raw25102Labels = mixedMoment B raw25102step0 raw25102step0Labels := by
      have hz : ∀ j, raw25102 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25102step0 = (fun i j => raw25102 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25102step0 raw25102; decide +kernel
      have hl : raw25102step0Labels = raw25102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25102 raw25102Labels permutation346 hz
    mixedMoment B raw25102step0 raw25102step0Labels = mixedMoment B raw25102step1 raw25102step1Labels := by
      have ha : raw25102step1 = (fun i j => raw25102step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25102step1 raw25102step0; decide +kernel
      have hl : raw25102step1Labels = raw25102step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25102step0 raw25102step0Labels permutation34 permutation6
    mixedMoment B raw25102step1 raw25102step1Labels = mixedMoment B raw25102step2 raw25102step2Labels := by
      have ha : raw25102step2 = raw25102step1 := by apply Matrix.ext; unfold raw25102step2 raw25102step1; decide +kernel
      have hl : raw25102step1Labels = labelEmbedding9 ∘ raw25102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25102step1 raw25102step1Labels raw25102step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw25103 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25103step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25103 raw25103Labels = mixedMoment B node4462 node4462Labels := by
  calc
    mixedMoment B raw25103 raw25103Labels = mixedMoment B raw25103step0 raw25103step0Labels := by
      have hz : ∀ j, raw25103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25103step0 = (fun i j => raw25103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25103step0 raw25103; decide +kernel
      have hl : raw25103step0Labels = raw25103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25103 raw25103Labels permutation346 hz
    mixedMoment B raw25103step0 raw25103step0Labels = mixedMoment B raw25103step1 raw25103step1Labels := by
      have ha : raw25103step1 = (fun i j => raw25103step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25103step1 raw25103step0; decide +kernel
      have hl : raw25103step1Labels = raw25103step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25103step0 raw25103step0Labels permutation34 permutation6
    mixedMoment B raw25103step1 raw25103step1Labels = mixedMoment B raw25103step2 raw25103step2Labels := by
      have ha : raw25103step2 = raw25103step1 := by apply Matrix.ext; unfold raw25103step2 raw25103step1; decide +kernel
      have hl : raw25103step1Labels = labelEmbedding9 ∘ raw25103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25103step1 raw25103step1Labels raw25103step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4462 node4462Labels := by rfl

def raw25104 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25104step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25104 raw25104Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw25104 raw25104Labels = mixedMoment B raw25104step0 raw25104step0Labels := by
      have hz : ∀ j, raw25104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25104step0 = (fun i j => raw25104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25104step0 raw25104; decide +kernel
      have hl : raw25104step0Labels = raw25104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25104 raw25104Labels permutation346 hz
    mixedMoment B raw25104step0 raw25104step0Labels = mixedMoment B raw25104step1 raw25104step1Labels := by
      have ha : raw25104step1 = (fun i j => raw25104step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25104step1 raw25104step0; decide +kernel
      have hl : raw25104step1Labels = raw25104step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25104step0 raw25104step0Labels permutation32 permutation6
    mixedMoment B raw25104step1 raw25104step1Labels = mixedMoment B raw25104step2 raw25104step2Labels := by
      have ha : raw25104step2 = raw25104step1 := by apply Matrix.ext; unfold raw25104step2 raw25104step1; decide +kernel
      have hl : raw25104step1Labels = labelEmbedding9 ∘ raw25104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25104step1 raw25104step1Labels raw25104step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw25105 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25105step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25105 raw25105Labels = mixedMoment B node4400 node4400Labels := by
  calc
    mixedMoment B raw25105 raw25105Labels = mixedMoment B raw25105step0 raw25105step0Labels := by
      have ha : raw25105step0 = (fun i j => raw25105 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25105step0 raw25105; decide +kernel
      have hl : raw25105step0Labels = raw25105Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25105 raw25105Labels permutation176 permutation6
    mixedMoment B raw25105step0 raw25105step0Labels = mixedMoment B raw25105step1 raw25105step1Labels := by
      have ha : raw25105step1 = raw25105step0 := by apply Matrix.ext; unfold raw25105step1 raw25105step0; decide +kernel
      have hl : raw25105step0Labels = labelEmbedding9 ∘ raw25105step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25105step0 raw25105step0Labels raw25105step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4400 node4400Labels := by rfl

def raw25106 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25106step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25106step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25106 raw25106Labels = mixedMoment B node4462 node4462Labels := by
  calc
    mixedMoment B raw25106 raw25106Labels = mixedMoment B raw25106step0 raw25106step0Labels := by
      have hz : ∀ j, raw25106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25106step0 = (fun i j => raw25106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25106step0 raw25106; decide +kernel
      have hl : raw25106step0Labels = raw25106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25106 raw25106Labels permutation346 hz
    mixedMoment B raw25106step0 raw25106step0Labels = mixedMoment B raw25106step1 raw25106step1Labels := by
      have ha : raw25106step1 = (fun i j => raw25106step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25106step1 raw25106step0; decide +kernel
      have hl : raw25106step1Labels = raw25106step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25106step0 raw25106step0Labels permutation32 permutation6
    mixedMoment B raw25106step1 raw25106step1Labels = mixedMoment B raw25106step2 raw25106step2Labels := by
      have ha : raw25106step2 = raw25106step1 := by apply Matrix.ext; unfold raw25106step2 raw25106step1; decide +kernel
      have hl : raw25106step1Labels = labelEmbedding9 ∘ raw25106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25106step1 raw25106step1Labels raw25106step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4462 node4462Labels := by rfl

def raw25107 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25107step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25107 raw25107Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw25107 raw25107Labels = mixedMoment B raw25107step0 raw25107step0Labels := by
      have hz : ∀ j, raw25107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25107step0 = (fun i j => raw25107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25107step0 raw25107; decide +kernel
      have hl : raw25107step0Labels = raw25107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25107 raw25107Labels permutation346 hz
    mixedMoment B raw25107step0 raw25107step0Labels = mixedMoment B raw25107step1 raw25107step1Labels := by
      have ha : raw25107step1 = (fun i j => raw25107step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25107step1 raw25107step0; decide +kernel
      have hl : raw25107step1Labels = raw25107step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25107step0 raw25107step0Labels permutation32 permutation6
    mixedMoment B raw25107step1 raw25107step1Labels = mixedMoment B raw25107step2 raw25107step2Labels := by
      have ha : raw25107step2 = raw25107step1 := by apply Matrix.ext; unfold raw25107step2 raw25107step1; decide +kernel
      have hl : raw25107step1Labels = labelEmbedding9 ∘ raw25107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25107step1 raw25107step1Labels raw25107step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw25108 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25108step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw25108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25108 raw25108Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25108 raw25108Labels = mixedMoment B raw25108step0 raw25108step0Labels := by
      have hz : ∀ j, raw25108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25108step0 = (fun i j => raw25108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25108step0 raw25108; decide +kernel
      have hl : raw25108step0Labels = raw25108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25108 raw25108Labels permutation346 hz
    mixedMoment B raw25108step0 raw25108step0Labels = mixedMoment B raw25108step1 raw25108step1Labels := by
      have ha : raw25108step1 = (fun i j => raw25108step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25108step1 raw25108step0; decide +kernel
      have hl : raw25108step1Labels = raw25108step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25108step0 raw25108step0Labels permutation34 permutation6
    mixedMoment B raw25108step1 raw25108step1Labels = mixedMoment B raw25108step2 raw25108step2Labels := by
      have ha : raw25108step2 = raw25108step1 := by apply Matrix.ext; unfold raw25108step2 raw25108step1; decide +kernel
      have hl : raw25108step1Labels = labelEmbedding9 ∘ raw25108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25108step1 raw25108step1Labels raw25108step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw25109 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25109 raw25109Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw25109 raw25109Labels = mixedMoment B raw25109step0 raw25109step0Labels := by
      have hz : ∀ j, raw25109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25109step0 = (fun i j => raw25109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25109step0 raw25109; decide +kernel
      have hl : raw25109step0Labels = raw25109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25109 raw25109Labels permutation346 hz
    mixedMoment B raw25109step0 raw25109step0Labels = mixedMoment B raw25109step1 raw25109step1Labels := by
      have ha : raw25109step1 = (fun i j => raw25109step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25109step1 raw25109step0; decide +kernel
      have hl : raw25109step1Labels = raw25109step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25109step0 raw25109step0Labels permutation32 permutation6
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw25110 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25110 raw25110Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw25110 raw25110Labels = mixedMoment B raw25110step0 raw25110step0Labels := by
      have hz : ∀ j, raw25110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25110step0 = (fun i j => raw25110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25110step0 raw25110; decide +kernel
      have hl : raw25110step0Labels = raw25110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25110 raw25110Labels permutation346 hz
    mixedMoment B raw25110step0 raw25110step0Labels = mixedMoment B raw25110step1 raw25110step1Labels := by
      have ha : raw25110step1 = (fun i j => raw25110step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25110step1 raw25110step0; decide +kernel
      have hl : raw25110step1Labels = raw25110step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25110step0 raw25110step0Labels permutation34 permutation6
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw25111 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25111 raw25111Labels = mixedMoment B node1270 node1270Labels := by
  calc
    mixedMoment B raw25111 raw25111Labels = mixedMoment B raw25111step0 raw25111step0Labels := by
      have hz : ∀ j, raw25111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25111step0 = (fun i j => raw25111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25111step0 raw25111; decide +kernel
      have hl : raw25111step0Labels = raw25111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25111 raw25111Labels permutation346 hz
    mixedMoment B raw25111step0 raw25111step0Labels = mixedMoment B raw25111step1 raw25111step1Labels := by
      have ha : raw25111step1 = (fun i j => raw25111step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25111step1 raw25111step0; decide +kernel
      have hl : raw25111step1Labels = raw25111step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25111step0 raw25111step0Labels permutation32 permutation6
    _ = mixedMoment B node1270 node1270Labels := by rfl

def raw25112 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25112step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25112 raw25112Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw25112 raw25112Labels = mixedMoment B raw25112step0 raw25112step0Labels := by
      have hz : ∀ j, raw25112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25112step0 = (fun i j => raw25112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25112step0 raw25112; decide +kernel
      have hl : raw25112step0Labels = raw25112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25112 raw25112Labels permutation346 hz
    mixedMoment B raw25112step0 raw25112step0Labels = mixedMoment B raw25112step1 raw25112step1Labels := by
      have ha : raw25112step1 = (fun i j => raw25112step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25112step1 raw25112step0; decide +kernel
      have hl : raw25112step1Labels = raw25112step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25112step0 raw25112step0Labels permutation32 permutation6
    _ = mixedMoment B node827 node827Labels := by rfl

def raw25113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25113 raw25113Labels = mixedMoment B node990 node990Labels := by
  calc
    mixedMoment B raw25113 raw25113Labels = mixedMoment B raw25113step0 raw25113step0Labels := by
      have ha : raw25113step0 = (fun i j => raw25113 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25113step0 raw25113; decide +kernel
      have hl : raw25113step0Labels = raw25113Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25113 raw25113Labels permutation176 permutation6
    _ = mixedMoment B node990 node990Labels := by rfl

def raw25114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25114 raw25114Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw25114 raw25114Labels = mixedMoment B raw25114step0 raw25114step0Labels := by
      have hz : ∀ j, raw25114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25114step0 = (fun i j => raw25114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25114step0 raw25114; decide +kernel
      have hl : raw25114step0Labels = raw25114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25114 raw25114Labels permutation346 hz
    mixedMoment B raw25114step0 raw25114step0Labels = mixedMoment B raw25114step1 raw25114step1Labels := by
      have ha : raw25114step1 = (fun i j => raw25114step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25114step1 raw25114step0; decide +kernel
      have hl : raw25114step1Labels = raw25114step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25114step0 raw25114step0Labels permutation32 permutation6
    _ = mixedMoment B node1058 node1058Labels := by rfl

def raw25115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25115 raw25115Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw25115 raw25115Labels = mixedMoment B raw25115step0 raw25115step0Labels := by
      have hz : ∀ j, raw25115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25115step0 = (fun i j => raw25115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25115step0 raw25115; decide +kernel
      have hl : raw25115step0Labels = raw25115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25115 raw25115Labels permutation346 hz
    mixedMoment B raw25115step0 raw25115step0Labels = mixedMoment B raw25115step1 raw25115step1Labels := by
      have ha : raw25115step1 = (fun i j => raw25115step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25115step1 raw25115step0; decide +kernel
      have hl : raw25115step1Labels = raw25115step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25115step0 raw25115step0Labels permutation34 permutation6
    _ = mixedMoment B node1058 node1058Labels := by rfl

def raw25116 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25116 raw25116Labels = mixedMoment B node1060 node1060Labels := by
  calc
    mixedMoment B raw25116 raw25116Labels = mixedMoment B raw25116step0 raw25116step0Labels := by
      have hz : ∀ j, raw25116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25116step0 = (fun i j => raw25116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25116step0 raw25116; decide +kernel
      have hl : raw25116step0Labels = raw25116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25116 raw25116Labels permutation346 hz
    mixedMoment B raw25116step0 raw25116step0Labels = mixedMoment B raw25116step1 raw25116step1Labels := by
      have ha : raw25116step1 = (fun i j => raw25116step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25116step1 raw25116step0; decide +kernel
      have hl : raw25116step1Labels = raw25116step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25116step0 raw25116step0Labels permutation32 permutation6
    _ = mixedMoment B node1060 node1060Labels := by rfl

def raw25117 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25117 raw25117Labels = mixedMoment B node786 node786Labels := by
  calc
    mixedMoment B raw25117 raw25117Labels = mixedMoment B raw25117step0 raw25117step0Labels := by
      have ha : raw25117step0 = (fun i j => raw25117 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25117step0 raw25117; decide +kernel
      have hl : raw25117step0Labels = raw25117Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25117 raw25117Labels permutation152 permutation6
    _ = mixedMoment B node786 node786Labels := by rfl

def raw25118 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25118 raw25118Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw25118 raw25118Labels = mixedMoment B raw25118step0 raw25118step0Labels := by
      have hz : ∀ j, raw25118 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw25118step0 = (fun i j => raw25118 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw25118step0 raw25118; decide +kernel
      have hl : raw25118step0Labels = raw25118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25118 raw25118Labels permutation265 hz
    mixedMoment B raw25118step0 raw25118step0Labels = mixedMoment B raw25118step1 raw25118step1Labels := by
      have ha : raw25118step1 = (fun i j => raw25118step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25118step1 raw25118step0; decide +kernel
      have hl : raw25118step1Labels = raw25118step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25118step0 raw25118step0Labels permutation32 permutation6
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw25119 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25119 raw25119Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw25119 raw25119Labels = mixedMoment B raw25119step0 raw25119step0Labels := by
      have ha : raw25119step0 = (fun i j => raw25119 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25119step0 raw25119; decide +kernel
      have hl : raw25119step0Labels = raw25119Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25119 raw25119Labels permutation152 permutation6
    _ = mixedMoment B node1021 node1021Labels := by rfl

def raw25120 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25120 raw25120Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw25120 raw25120Labels = mixedMoment B raw25120step0 raw25120step0Labels := by
      have ha : raw25120step0 = (fun i j => raw25120 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25120step0 raw25120; decide +kernel
      have hl : raw25120step0Labels = raw25120Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25120 raw25120Labels permutation154 permutation6
    _ = mixedMoment B node1021 node1021Labels := by rfl

def raw25121 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw25121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25121 raw25121Labels = mixedMoment B node1023 node1023Labels := by
  calc
    mixedMoment B raw25121 raw25121Labels = mixedMoment B raw25121step0 raw25121step0Labels := by
      have ha : raw25121step0 = (fun i j => raw25121 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25121step0 raw25121; decide +kernel
      have hl : raw25121step0Labels = raw25121Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25121 raw25121Labels permutation152 permutation6
    _ = mixedMoment B node1023 node1023Labels := by rfl

def raw25122 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25122 raw25122Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw25122 raw25122Labels = mixedMoment B raw25122step0 raw25122step0Labels := by
      have hz : ∀ j, raw25122 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25122step0 = (fun i j => raw25122 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25122step0 raw25122; decide +kernel
      have hl : raw25122step0Labels = raw25122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25122 raw25122Labels permutation346 hz
    mixedMoment B raw25122step0 raw25122step0Labels = mixedMoment B raw25122step1 raw25122step1Labels := by
      have ha : raw25122step1 = (fun i j => raw25122step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25122step1 raw25122step0; decide +kernel
      have hl : raw25122step1Labels = raw25122step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25122step0 raw25122step0Labels permutation34 permutation6
    _ = mixedMoment B node811 node811Labels := by rfl

def raw25123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25123Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25123step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25123step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25123 raw25123Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw25123 raw25123Labels = mixedMoment B raw25123step0 raw25123step0Labels := by
      have hz : ∀ j, raw25123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25123step0 = (fun i j => raw25123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25123step0 raw25123; decide +kernel
      have hl : raw25123step0Labels = raw25123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25123 raw25123Labels permutation346 hz
    mixedMoment B raw25123step0 raw25123step0Labels = mixedMoment B raw25123step1 raw25123step1Labels := by
      have hz : ∀ j, raw25123step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25123step1 = (fun i j => raw25123step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25123step1 raw25123step0; decide +kernel
      have hl : raw25123step1Labels = raw25123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25123step0 raw25123step0Labels permutation56 hz
    mixedMoment B raw25123step1 raw25123step1Labels = mixedMoment B raw25123step2 raw25123step2Labels := by
      have ha : raw25123step2 = (fun i j => raw25123step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25123step2 raw25123step1; decide +kernel
      have hl : raw25123step2Labels = raw25123step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25123step1 raw25123step1Labels permutation10 permutation6
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw25124 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw25124Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25124 raw25124Labels = mixedMoment B node981 node981Labels := by
  calc
    mixedMoment B raw25124 raw25124Labels = mixedMoment B raw25124step0 raw25124step0Labels := by
      have ha : raw25124step0 = (fun i j => raw25124 (permutation178 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25124step0 raw25124; decide +kernel
      have hl : raw25124step0Labels = raw25124Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25124 raw25124Labels permutation178 permutation6
    _ = mixedMoment B node981 node981Labels := by rfl

def raw25125 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25125Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25125step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25125step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25125 raw25125Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw25125 raw25125Labels = mixedMoment B raw25125step0 raw25125step0Labels := by
      have hz : ∀ j, raw25125 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25125step0 = (fun i j => raw25125 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25125step0 raw25125; decide +kernel
      have hl : raw25125step0Labels = raw25125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25125 raw25125Labels permutation346 hz
    mixedMoment B raw25125step0 raw25125step0Labels = mixedMoment B raw25125step1 raw25125step1Labels := by
      have ha : raw25125step1 = (fun i j => raw25125step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25125step1 raw25125step0; decide +kernel
      have hl : raw25125step1Labels = raw25125step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25125step0 raw25125step0Labels permutation34 permutation6
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw25126 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25126Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw25126step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25126 raw25126Labels = mixedMoment B node1045 node1045Labels := by
  calc
    mixedMoment B raw25126 raw25126Labels = mixedMoment B raw25126step0 raw25126step0Labels := by
      have hz : ∀ j, raw25126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25126step0 = (fun i j => raw25126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25126step0 raw25126; decide +kernel
      have hl : raw25126step0Labels = raw25126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25126 raw25126Labels permutation346 hz
    mixedMoment B raw25126step0 raw25126step0Labels = mixedMoment B raw25126step1 raw25126step1Labels := by
      have ha : raw25126step1 = (fun i j => raw25126step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25126step1 raw25126step0; decide +kernel
      have hl : raw25126step1Labels = raw25126step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25126step0 raw25126step0Labels permutation34 permutation6
    _ = mixedMoment B node1045 node1045Labels := by rfl

def raw25127 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25127Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25127step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25127step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25127 raw25127Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw25127 raw25127Labels = mixedMoment B raw25127step0 raw25127step0Labels := by
      have hz : ∀ j, raw25127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25127step0 = (fun i j => raw25127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25127step0 raw25127; decide +kernel
      have hl : raw25127step0Labels = raw25127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25127 raw25127Labels permutation346 hz
    mixedMoment B raw25127step0 raw25127step0Labels = mixedMoment B raw25127step1 raw25127step1Labels := by
      have ha : raw25127step1 = (fun i j => raw25127step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25127step1 raw25127step0; decide +kernel
      have hl : raw25127step1Labels = raw25127step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25127step0 raw25127step0Labels permutation32 permutation6
    _ = mixedMoment B node811 node811Labels := by rfl

def raw25128 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25128Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25128step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25128step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25128 raw25128Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw25128 raw25128Labels = mixedMoment B raw25128step0 raw25128step0Labels := by
      have hz : ∀ j, raw25128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25128step0 = (fun i j => raw25128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25128step0 raw25128; decide +kernel
      have hl : raw25128step0Labels = raw25128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25128 raw25128Labels permutation346 hz
    mixedMoment B raw25128step0 raw25128step0Labels = mixedMoment B raw25128step1 raw25128step1Labels := by
      have hz : ∀ j, raw25128step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw25128step1 = (fun i j => raw25128step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw25128step1 raw25128step0; decide +kernel
      have hl : raw25128step1Labels = raw25128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25128step0 raw25128step0Labels permutation56 hz
    mixedMoment B raw25128step1 raw25128step1Labels = mixedMoment B raw25128step2 raw25128step2Labels := by
      have ha : raw25128step2 = (fun i j => raw25128step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25128step2 raw25128step1; decide +kernel
      have hl : raw25128step2Labels = raw25128step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25128step1 raw25128step1Labels permutation8 permutation6
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw25129 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25129 raw25129Labels = mixedMoment B node981 node981Labels := by
  calc
    mixedMoment B raw25129 raw25129Labels = mixedMoment B raw25129step0 raw25129step0Labels := by
      have ha : raw25129step0 = (fun i j => raw25129 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25129step0 raw25129; decide +kernel
      have hl : raw25129step0Labels = raw25129Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25129 raw25129Labels permutation176 permutation6
    _ = mixedMoment B node981 node981Labels := by rfl

def raw25130 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25130Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw25130step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw25130step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25130 raw25130Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw25130 raw25130Labels = mixedMoment B raw25130step0 raw25130step0Labels := by
      have hz : ∀ j, raw25130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25130step0 = (fun i j => raw25130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25130step0 raw25130; decide +kernel
      have hl : raw25130step0Labels = raw25130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25130 raw25130Labels permutation346 hz
    mixedMoment B raw25130step0 raw25130step0Labels = mixedMoment B raw25130step1 raw25130step1Labels := by
      have ha : raw25130step1 = (fun i j => raw25130step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25130step1 raw25130step0; decide +kernel
      have hl : raw25130step1Labels = raw25130step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25130step0 raw25130step0Labels permutation32 permutation6
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw25131 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25131Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw25131step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw25131step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25131 raw25131Labels = mixedMoment B node1045 node1045Labels := by
  calc
    mixedMoment B raw25131 raw25131Labels = mixedMoment B raw25131step0 raw25131step0Labels := by
      have hz : ∀ j, raw25131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25131step0 = (fun i j => raw25131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25131step0 raw25131; decide +kernel
      have hl : raw25131step0Labels = raw25131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25131 raw25131Labels permutation346 hz
    mixedMoment B raw25131step0 raw25131step0Labels = mixedMoment B raw25131step1 raw25131step1Labels := by
      have ha : raw25131step1 = (fun i j => raw25131step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25131step1 raw25131step0; decide +kernel
      have hl : raw25131step1Labels = raw25131step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25131step0 raw25131step0Labels permutation32 permutation6
    _ = mixedMoment B node1045 node1045Labels := by rfl

def raw25132 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25132Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25132step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25132 raw25132Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw25132 raw25132Labels = mixedMoment B raw25132step0 raw25132step0Labels := by
      have hz : ∀ j, raw25132 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25132step0 = (fun i j => raw25132 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25132step0 raw25132; decide +kernel
      have hl : raw25132step0Labels = raw25132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25132 raw25132Labels permutation346 hz
    mixedMoment B raw25132step0 raw25132step0Labels = mixedMoment B raw25132step1 raw25132step1Labels := by
      have ha : raw25132step1 = (fun i j => raw25132step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25132step1 raw25132step0; decide +kernel
      have hl : raw25132step1Labels = raw25132step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25132step0 raw25132step0Labels permutation32 permutation6
    _ = mixedMoment B node810 node810Labels := by rfl

def raw25133 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25133Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw25133step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25133step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25133 raw25133Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw25133 raw25133Labels = mixedMoment B raw25133step0 raw25133step0Labels := by
      have hz : ∀ j, raw25133 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25133step0 = (fun i j => raw25133 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25133step0 raw25133; decide +kernel
      have hl : raw25133step0Labels = raw25133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25133 raw25133Labels permutation346 hz
    mixedMoment B raw25133step0 raw25133step0Labels = mixedMoment B raw25133step1 raw25133step1Labels := by
      have ha : raw25133step1 = (fun i j => raw25133step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25133step1 raw25133step0; decide +kernel
      have hl : raw25133step1Labels = raw25133step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25133step0 raw25133step0Labels permutation32 permutation6
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw25134 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25134Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25134step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25134 raw25134Labels = mixedMoment B node1041 node1041Labels := by
  calc
    mixedMoment B raw25134 raw25134Labels = mixedMoment B raw25134step0 raw25134step0Labels := by
      have hz : ∀ j, raw25134 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25134step0 = (fun i j => raw25134 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25134step0 raw25134; decide +kernel
      have hl : raw25134step0Labels = raw25134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25134 raw25134Labels permutation346 hz
    mixedMoment B raw25134step0 raw25134step0Labels = mixedMoment B raw25134step1 raw25134step1Labels := by
      have ha : raw25134step1 = (fun i j => raw25134step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw25134step1 raw25134step0; decide +kernel
      have hl : raw25134step1Labels = raw25134step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25134step0 raw25134step0Labels permutation34 permutation6
    _ = mixedMoment B node1041 node1041Labels := by rfl

def raw25135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25135step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25135 raw25135Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw25135 raw25135Labels = mixedMoment B raw25135step0 raw25135step0Labels := by
      have hz : ∀ j, raw25135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25135step0 = (fun i j => raw25135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25135step0 raw25135; decide +kernel
      have hl : raw25135step0Labels = raw25135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25135 raw25135Labels permutation346 hz
    mixedMoment B raw25135step0 raw25135step0Labels = mixedMoment B raw25135step1 raw25135step1Labels := by
      have ha : raw25135step1 = (fun i j => raw25135step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25135step1 raw25135step0; decide +kernel
      have hl : raw25135step1Labels = raw25135step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25135step0 raw25135step0Labels permutation34 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw25136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25136 raw25136Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw25136 raw25136Labels = mixedMoment B raw25136step0 raw25136step0Labels := by
      have ha : raw25136step0 = (fun i j => raw25136 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25136step0 raw25136; decide +kernel
      have hl : raw25136step0Labels = raw25136Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25136 raw25136Labels permutation178 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw25137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25137 raw25137Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw25137 raw25137Labels = mixedMoment B raw25137step0 raw25137step0Labels := by
      have hz : ∀ j, raw25137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25137step0 = (fun i j => raw25137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25137step0 raw25137; decide +kernel
      have hl : raw25137step0Labels = raw25137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25137 raw25137Labels permutation346 hz
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw25138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25138step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25138 raw25138Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw25138 raw25138Labels = mixedMoment B raw25138step0 raw25138step0Labels := by
      have hz : ∀ j, raw25138 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25138step0 = (fun i j => raw25138 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25138step0 raw25138; decide +kernel
      have hl : raw25138step0Labels = raw25138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25138 raw25138Labels permutation520 hz
    mixedMoment B raw25138step0 raw25138step0Labels = mixedMoment B raw25138step1 raw25138step1Labels := by
      have hz : ∀ j, raw25138step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25138step1 = (fun i j => raw25138step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25138step1 raw25138step0; decide +kernel
      have hl : raw25138step1Labels = raw25138step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25138step0 raw25138step0Labels permutation80 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw25139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25139 raw25139Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw25139 raw25139Labels = mixedMoment B raw25139step0 raw25139step0Labels := by
      have hz : ∀ j, raw25139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25139step0 = (fun i j => raw25139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25139step0 raw25139; decide +kernel
      have hl : raw25139step0Labels = raw25139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25139 raw25139Labels permutation346 hz
    mixedMoment B raw25139step0 raw25139step0Labels = mixedMoment B raw25139step1 raw25139step1Labels := by
      have ha : raw25139step1 = (fun i j => raw25139step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25139step1 raw25139step0; decide +kernel
      have hl : raw25139step1Labels = raw25139step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25139step0 raw25139step0Labels permutation34 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw25140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25140 raw25140Labels = mixedMoment B node4175 node4175Labels := by
  calc
    mixedMoment B raw25140 raw25140Labels = mixedMoment B raw25140step0 raw25140step0Labels := by
      have hz : ∀ j, raw25140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25140step0 = (fun i j => raw25140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25140step0 raw25140; decide +kernel
      have hl : raw25140step0Labels = raw25140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25140 raw25140Labels permutation346 hz
    mixedMoment B raw25140step0 raw25140step0Labels = mixedMoment B raw25140step1 raw25140step1Labels := by
      have ha : raw25140step1 = (fun i j => raw25140step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25140step1 raw25140step0; decide +kernel
      have hl : raw25140step1Labels = raw25140step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25140step0 raw25140step0Labels permutation44 permutation2
    _ = mixedMoment B node4175 node4175Labels := by rfl

def raw25141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25141 raw25141Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw25141 raw25141Labels = mixedMoment B raw25141step0 raw25141step0Labels := by
      have ha : raw25141step0 = (fun i j => raw25141 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25141step0 raw25141; decide +kernel
      have hl : raw25141step0Labels = raw25141Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25141 raw25141Labels permutation188 permutation2
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw25142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25142step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25142 raw25142Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25142 raw25142Labels = mixedMoment B raw25142step0 raw25142step0Labels := by
      have hz : ∀ j, raw25142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25142step0 = (fun i j => raw25142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25142step0 raw25142; decide +kernel
      have hl : raw25142step0Labels = raw25142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25142 raw25142Labels permutation346 hz
    mixedMoment B raw25142step0 raw25142step0Labels = mixedMoment B raw25142step1 raw25142step1Labels := by
      have ha : raw25142step1 = (fun i j => raw25142step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25142step1 raw25142step0; decide +kernel
      have hl : raw25142step1Labels = raw25142step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25142step0 raw25142step0Labels permutation40 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw25143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25143step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25143step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25143 raw25143Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw25143 raw25143Labels = mixedMoment B raw25143step0 raw25143step0Labels := by
      have hz : ∀ j, raw25143 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25143step0 = (fun i j => raw25143 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25143step0 raw25143; decide +kernel
      have hl : raw25143step0Labels = raw25143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25143 raw25143Labels permutation520 hz
    mixedMoment B raw25143step0 raw25143step0Labels = mixedMoment B raw25143step1 raw25143step1Labels := by
      have hz : ∀ j, raw25143step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25143step1 = (fun i j => raw25143step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25143step1 raw25143step0; decide +kernel
      have hl : raw25143step1Labels = raw25143step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25143step0 raw25143step0Labels permutation80 hz
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw25144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25144 raw25144Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw25144 raw25144Labels = mixedMoment B raw25144step0 raw25144step0Labels := by
      have hz : ∀ j, raw25144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25144step0 = (fun i j => raw25144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25144step0 raw25144; decide +kernel
      have hl : raw25144step0Labels = raw25144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25144 raw25144Labels permutation346 hz
    mixedMoment B raw25144step0 raw25144step0Labels = mixedMoment B raw25144step1 raw25144step1Labels := by
      have ha : raw25144step1 = (fun i j => raw25144step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25144step1 raw25144step0; decide +kernel
      have hl : raw25144step1Labels = raw25144step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25144step0 raw25144step0Labels permutation44 permutation2
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw25145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25145 raw25145Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw25145 raw25145Labels = mixedMoment B raw25145step0 raw25145step0Labels := by
      have ha : raw25145step0 = (fun i j => raw25145 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25145step0 raw25145; decide +kernel
      have hl : raw25145step0Labels = raw25145Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25145 raw25145Labels permutation154 permutation2
    _ = mixedMoment B node4150 node4150Labels := by rfl

def raw25146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25146 raw25146Labels = mixedMoment B node4364 node4364Labels := by
  calc
    mixedMoment B raw25146 raw25146Labels = mixedMoment B raw25146step0 raw25146step0Labels := by
      have ha : raw25146step0 = (fun i j => raw25146 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25146step0 raw25146; decide +kernel
      have hl : raw25146step0Labels = raw25146Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25146 raw25146Labels permutation154 permutation2
    _ = mixedMoment B node4364 node4364Labels := by rfl

def raw25147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25147 raw25147Labels = mixedMoment B node4438 node4438Labels := by
  calc
    mixedMoment B raw25147 raw25147Labels = mixedMoment B raw25147step0 raw25147step0Labels := by
      have ha : raw25147step0 = (fun i j => raw25147 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25147step0 raw25147; decide +kernel
      have hl : raw25147step0Labels = raw25147Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25147 raw25147Labels permutation158 permutation2
    _ = mixedMoment B node4438 node4438Labels := by rfl

def raw25148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25148 raw25148Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25148 raw25148Labels = mixedMoment B raw25148step0 raw25148step0Labels := by
      have hz : ∀ j, raw25148 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25148step0 = (fun i j => raw25148 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25148step0 raw25148; decide +kernel
      have hl : raw25148step0Labels = raw25148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25148 raw25148Labels permutation520 hz
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw25149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25149 raw25149Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw25149 raw25149Labels = mixedMoment B raw25149step0 raw25149step0Labels := by
      have ha : raw25149step0 = (fun i j => raw25149 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25149step0 raw25149; decide +kernel
      have hl : raw25149step0Labels = raw25149Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25149 raw25149Labels permutation154 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw25150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25150 raw25150Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw25150 raw25150Labels = mixedMoment B raw25150step0 raw25150step0Labels := by
      have hz : ∀ j, raw25150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25150step0 = (fun i j => raw25150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25150step0 raw25150; decide +kernel
      have hl : raw25150step0Labels = raw25150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25150 raw25150Labels permutation346 hz
    mixedMoment B raw25150step0 raw25150step0Labels = mixedMoment B raw25150step1 raw25150step1Labels := by
      have ha : raw25150step1 = (fun i j => raw25150step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25150step1 raw25150step0; decide +kernel
      have hl : raw25150step1Labels = raw25150step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25150step0 raw25150step0Labels permutation34 permutation2
    _ = mixedMoment B node4155 node4155Labels := by rfl

def raw25151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25151 raw25151Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw25151 raw25151Labels = mixedMoment B raw25151step0 raw25151step0Labels := by
      have hz : ∀ j, raw25151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25151step0 = (fun i j => raw25151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25151step0 raw25151; decide +kernel
      have hl : raw25151step0Labels = raw25151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25151 raw25151Labels permutation346 hz
    mixedMoment B raw25151step0 raw25151step0Labels = mixedMoment B raw25151step1 raw25151step1Labels := by
      have ha : raw25151step1 = (fun i j => raw25151step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25151step1 raw25151step0; decide +kernel
      have hl : raw25151step1Labels = raw25151step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25151step0 raw25151step0Labels permutation34 permutation2
    _ = mixedMoment B node4369 node4369Labels := by rfl

def raw25152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25152 raw25152Labels = mixedMoment B node4329 node4329Labels := by
  calc
    mixedMoment B raw25152 raw25152Labels = mixedMoment B raw25152step0 raw25152step0Labels := by
      have ha : raw25152step0 = (fun i j => raw25152 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25152step0 raw25152; decide +kernel
      have hl : raw25152step0Labels = raw25152Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25152 raw25152Labels permutation178 permutation2
    _ = mixedMoment B node4329 node4329Labels := by rfl

def raw25153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25153step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25153 raw25153Labels = mixedMoment B node4467 node4467Labels := by
  calc
    mixedMoment B raw25153 raw25153Labels = mixedMoment B raw25153step0 raw25153step0Labels := by
      have hz : ∀ j, raw25153 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25153step0 = (fun i j => raw25153 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25153step0 raw25153; decide +kernel
      have hl : raw25153step0Labels = raw25153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25153 raw25153Labels permutation520 hz
    mixedMoment B raw25153step0 raw25153step0Labels = mixedMoment B raw25153step1 raw25153step1Labels := by
      have hz : ∀ j, raw25153step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25153step1 = (fun i j => raw25153step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25153step1 raw25153step0; decide +kernel
      have hl : raw25153step1Labels = raw25153step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25153step0 raw25153step0Labels permutation80 hz
    _ = mixedMoment B node4467 node4467Labels := by rfl

def raw25154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25154 raw25154Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw25154 raw25154Labels = mixedMoment B raw25154step0 raw25154step0Labels := by
      have hz : ∀ j, raw25154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25154step0 = (fun i j => raw25154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25154step0 raw25154; decide +kernel
      have hl : raw25154step0Labels = raw25154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25154 raw25154Labels permutation346 hz
    mixedMoment B raw25154step0 raw25154step0Labels = mixedMoment B raw25154step1 raw25154step1Labels := by
      have ha : raw25154step1 = (fun i j => raw25154step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25154step1 raw25154step0; decide +kernel
      have hl : raw25154step1Labels = raw25154step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25154step0 raw25154step0Labels permutation35 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw25155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25155 raw25155Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw25155 raw25155Labels = mixedMoment B raw25155step0 raw25155step0Labels := by
      have hz : ∀ j, raw25155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25155step0 = (fun i j => raw25155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25155step0 raw25155; decide +kernel
      have hl : raw25155step0Labels = raw25155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25155 raw25155Labels permutation346 hz
    _ = mixedMoment B node4158 node4158Labels := by rfl

def raw25156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25156 raw25156Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw25156 raw25156Labels = mixedMoment B raw25156step0 raw25156step0Labels := by
      have hz : ∀ j, raw25156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25156step0 = (fun i j => raw25156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25156step0 raw25156; decide +kernel
      have hl : raw25156step0Labels = raw25156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25156 raw25156Labels permutation346 hz
    _ = mixedMoment B node4372 node4372Labels := by rfl

def raw25157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25157 raw25157Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw25157 raw25157Labels = mixedMoment B raw25157step0 raw25157step0Labels := by
      have ha : raw25157step0 = (fun i j => raw25157 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25157step0 raw25157; decide +kernel
      have hl : raw25157step0Labels = raw25157Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25157 raw25157Labels permutation176 permutation2
    _ = mixedMoment B node4332 node4332Labels := by rfl

def raw25158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25158 raw25158Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw25158 raw25158Labels = mixedMoment B raw25158step0 raw25158step0Labels := by
      have hz : ∀ j, raw25158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25158step0 = (fun i j => raw25158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25158step0 raw25158; decide +kernel
      have hl : raw25158step0Labels = raw25158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25158 raw25158Labels permutation346 hz
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw25159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25159 raw25159Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw25159 raw25159Labels = mixedMoment B raw25159step0 raw25159step0Labels := by
      have hz : ∀ j, raw25159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25159step0 = (fun i j => raw25159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25159step0 raw25159; decide +kernel
      have hl : raw25159step0Labels = raw25159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25159 raw25159Labels permutation346 hz
    mixedMoment B raw25159step0 raw25159step0Labels = mixedMoment B raw25159step1 raw25159step1Labels := by
      have ha : raw25159step1 = (fun i j => raw25159step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25159step1 raw25159step0; decide +kernel
      have hl : raw25159step1Labels = raw25159step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25159step0 raw25159step0Labels permutation33 permutation2
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw25160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25160 raw25160Labels = mixedMoment B node4153 node4153Labels := by
  calc
    mixedMoment B raw25160 raw25160Labels = mixedMoment B raw25160step0 raw25160step0Labels := by
      have hz : ∀ j, raw25160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25160step0 = (fun i j => raw25160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25160step0 raw25160; decide +kernel
      have hl : raw25160step0Labels = raw25160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25160 raw25160Labels permutation346 hz
    mixedMoment B raw25160step0 raw25160step0Labels = mixedMoment B raw25160step1 raw25160step1Labels := by
      have ha : raw25160step1 = (fun i j => raw25160step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25160step1 raw25160step0; decide +kernel
      have hl : raw25160step1Labels = raw25160step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25160step0 raw25160step0Labels permutation34 permutation2
    _ = mixedMoment B node4153 node4153Labels := by rfl

def raw25161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25161 raw25161Labels = mixedMoment B node4367 node4367Labels := by
  calc
    mixedMoment B raw25161 raw25161Labels = mixedMoment B raw25161step0 raw25161step0Labels := by
      have hz : ∀ j, raw25161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25161step0 = (fun i j => raw25161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25161step0 raw25161; decide +kernel
      have hl : raw25161step0Labels = raw25161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25161 raw25161Labels permutation346 hz
    mixedMoment B raw25161step0 raw25161step0Labels = mixedMoment B raw25161step1 raw25161step1Labels := by
      have ha : raw25161step1 = (fun i j => raw25161step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25161step1 raw25161step0; decide +kernel
      have hl : raw25161step1Labels = raw25161step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25161step0 raw25161step0Labels permutation34 permutation2
    _ = mixedMoment B node4367 node4367Labels := by rfl

def raw25162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25162 raw25162Labels = mixedMoment B node4327 node4327Labels := by
  calc
    mixedMoment B raw25162 raw25162Labels = mixedMoment B raw25162step0 raw25162step0Labels := by
      have ha : raw25162step0 = (fun i j => raw25162 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25162step0 raw25162; decide +kernel
      have hl : raw25162step0Labels = raw25162Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25162 raw25162Labels permutation178 permutation2
    _ = mixedMoment B node4327 node4327Labels := by rfl

def raw25163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25163 raw25163Labels = mixedMoment B node4440 node4440Labels := by
  calc
    mixedMoment B raw25163 raw25163Labels = mixedMoment B raw25163step0 raw25163step0Labels := by
      have hz : ∀ j, raw25163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25163step0 = (fun i j => raw25163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25163step0 raw25163; decide +kernel
      have hl : raw25163step0Labels = raw25163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25163 raw25163Labels permutation346 hz
    _ = mixedMoment B node4440 node4440Labels := by rfl

def raw25164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw25164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25164 raw25164Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw25164 raw25164Labels = mixedMoment B raw25164step0 raw25164step0Labels := by
      have hz : ∀ j, raw25164 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25164step0 = (fun i j => raw25164 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25164step0 raw25164; decide +kernel
      have hl : raw25164step0Labels = raw25164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25164 raw25164Labels permutation520 hz
    mixedMoment B raw25164step0 raw25164step0Labels = mixedMoment B raw25164step1 raw25164step1Labels := by
      have hz : ∀ j, raw25164step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25164step1 = (fun i j => raw25164step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25164step1 raw25164step0; decide +kernel
      have hl : raw25164step1Labels = raw25164step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25164step0 raw25164step0Labels permutation80 hz
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw25165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25165 raw25165Labels = mixedMoment B node3184 node3184Labels := by
  calc
    mixedMoment B raw25165 raw25165Labels = mixedMoment B raw25165step0 raw25165step0Labels := by
      have hz : ∀ j, raw25165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25165step0 = (fun i j => raw25165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25165step0 raw25165; decide +kernel
      have hl : raw25165step0Labels = raw25165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25165 raw25165Labels permutation346 hz
    mixedMoment B raw25165step0 raw25165step0Labels = mixedMoment B raw25165step1 raw25165step1Labels := by
      have ha : raw25165step1 = (fun i j => raw25165step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25165step1 raw25165step0; decide +kernel
      have hl : raw25165step1Labels = raw25165step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25165step0 raw25165step0Labels permutation32 permutation3
    _ = mixedMoment B node3184 node3184Labels := by rfl

def raw25166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25166 raw25166Labels = mixedMoment B node3204 node3204Labels := by
  calc
    mixedMoment B raw25166 raw25166Labels = mixedMoment B raw25166step0 raw25166step0Labels := by
      have ha : raw25166step0 = (fun i j => raw25166 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25166step0 raw25166; decide +kernel
      have hl : raw25166step0Labels = raw25166Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25166 raw25166Labels permutation176 permutation3
    _ = mixedMoment B node3204 node3204Labels := by rfl

def raw25167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw25167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25167 raw25167Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw25167 raw25167Labels = mixedMoment B raw25167step0 raw25167step0Labels := by
      have hz : ∀ j, raw25167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25167step0 = (fun i j => raw25167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25167step0 raw25167; decide +kernel
      have hl : raw25167step0Labels = raw25167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25167 raw25167Labels permutation346 hz
    mixedMoment B raw25167step0 raw25167step0Labels = mixedMoment B raw25167step1 raw25167step1Labels := by
      have ha : raw25167step1 = (fun i j => raw25167step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25167step1 raw25167step0; decide +kernel
      have hl : raw25167step1Labels = raw25167step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25167step0 raw25167step0Labels permutation32 permutation3
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw25168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25168step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25168step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25168step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw25168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25168 raw25168Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw25168 raw25168Labels = mixedMoment B raw25168step0 raw25168step0Labels := by
      have hz : ∀ j, raw25168 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25168step0 = (fun i j => raw25168 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25168step0 raw25168; decide +kernel
      have hl : raw25168step0Labels = raw25168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25168 raw25168Labels permutation520 hz
    mixedMoment B raw25168step0 raw25168step0Labels = mixedMoment B raw25168step1 raw25168step1Labels := by
      have hz : ∀ j, raw25168step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25168step1 = (fun i j => raw25168step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25168step1 raw25168step0; decide +kernel
      have hl : raw25168step1Labels = raw25168step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25168step0 raw25168step0Labels permutation80 hz
    mixedMoment B raw25168step1 raw25168step1Labels = mixedMoment B raw25168step2 raw25168step2Labels := by
      have ha : raw25168step2 = (fun i j => raw25168step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25168step2 raw25168step1; decide +kernel
      have hl : raw25168step2Labels = raw25168step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25168step1 raw25168step1Labels permutation8 permutation3
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw25169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25169step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25169 raw25169Labels = mixedMoment B node3228 node3228Labels := by
  calc
    mixedMoment B raw25169 raw25169Labels = mixedMoment B raw25169step0 raw25169step0Labels := by
      have hz : ∀ j, raw25169 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25169step0 = (fun i j => raw25169 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25169step0 raw25169; decide +kernel
      have hl : raw25169step0Labels = raw25169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25169 raw25169Labels permutation346 hz
    mixedMoment B raw25169step0 raw25169step0Labels = mixedMoment B raw25169step1 raw25169step1Labels := by
      have ha : raw25169step1 = (fun i j => raw25169step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25169step1 raw25169step0; decide +kernel
      have hl : raw25169step1Labels = raw25169step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25169step0 raw25169step0Labels permutation33 permutation3
    _ = mixedMoment B node3228 node3228Labels := by rfl

def raw25170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25170step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25170step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25170 raw25170Labels = mixedMoment B node644 node644Labels := by
  calc
    mixedMoment B raw25170 raw25170Labels = mixedMoment B raw25170step0 raw25170step0Labels := by
      have hz : ∀ j, raw25170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25170step0 = (fun i j => raw25170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25170step0 raw25170; decide +kernel
      have hl : raw25170step0Labels = raw25170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25170 raw25170Labels permutation346 hz
    mixedMoment B raw25170step0 raw25170step0Labels = mixedMoment B raw25170step1 raw25170step1Labels := by
      have ha : raw25170step1 = (fun i j => raw25170step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25170step1 raw25170step0; decide +kernel
      have hl : raw25170step1Labels = raw25170step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25170step0 raw25170step0Labels permutation32 permutation3
    _ = mixedMoment B node644 node644Labels := by rfl

def raw25171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25171step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25171 raw25171Labels = mixedMoment B node1339 node1339Labels := by
  calc
    mixedMoment B raw25171 raw25171Labels = mixedMoment B raw25171step0 raw25171step0Labels := by
      have ha : raw25171step0 = (fun i j => raw25171 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25171step0 raw25171; decide +kernel
      have hl : raw25171step0Labels = raw25171Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25171 raw25171Labels permutation176 permutation3
    _ = mixedMoment B node1339 node1339Labels := by rfl

def raw25172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25172 raw25172Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw25172 raw25172Labels = mixedMoment B raw25172step0 raw25172step0Labels := by
      have hz : ∀ j, raw25172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25172step0 = (fun i j => raw25172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25172step0 raw25172; decide +kernel
      have hl : raw25172step0Labels = raw25172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25172 raw25172Labels permutation346 hz
    mixedMoment B raw25172step0 raw25172step0Labels = mixedMoment B raw25172step1 raw25172step1Labels := by
      have ha : raw25172step1 = (fun i j => raw25172step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25172step1 raw25172step0; decide +kernel
      have hl : raw25172step1Labels = raw25172step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25172step0 raw25172step0Labels permutation38 permutation3
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw25173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25173step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25173step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25173step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw25173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25173 raw25173Labels = mixedMoment B node1447 node1447Labels := by
  calc
    mixedMoment B raw25173 raw25173Labels = mixedMoment B raw25173step0 raw25173step0Labels := by
      have hz : ∀ j, raw25173 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25173step0 = (fun i j => raw25173 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25173step0 raw25173; decide +kernel
      have hl : raw25173step0Labels = raw25173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25173 raw25173Labels permutation520 hz
    mixedMoment B raw25173step0 raw25173step0Labels = mixedMoment B raw25173step1 raw25173step1Labels := by
      have hz : ∀ j, raw25173step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25173step1 = (fun i j => raw25173step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25173step1 raw25173step0; decide +kernel
      have hl : raw25173step1Labels = raw25173step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25173step0 raw25173step0Labels permutation80 hz
    mixedMoment B raw25173step1 raw25173step1Labels = mixedMoment B raw25173step2 raw25173step2Labels := by
      have ha : raw25173step2 = (fun i j => raw25173step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25173step2 raw25173step1; decide +kernel
      have hl : raw25173step2Labels = raw25173step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25173step1 raw25173step1Labels permutation8 permutation3
    _ = mixedMoment B node1447 node1447Labels := by rfl

def raw25174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25174 raw25174Labels = mixedMoment B node1446 node1446Labels := by
  calc
    mixedMoment B raw25174 raw25174Labels = mixedMoment B raw25174step0 raw25174step0Labels := by
      have hz : ∀ j, raw25174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25174step0 = (fun i j => raw25174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25174step0 raw25174; decide +kernel
      have hl : raw25174step0Labels = raw25174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25174 raw25174Labels permutation346 hz
    mixedMoment B raw25174step0 raw25174step0Labels = mixedMoment B raw25174step1 raw25174step1Labels := by
      have ha : raw25174step1 = (fun i j => raw25174step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25174step1 raw25174step0; decide +kernel
      have hl : raw25174step1Labels = raw25174step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25174step0 raw25174step0Labels permutation33 permutation3
    _ = mixedMoment B node1446 node1446Labels := by rfl

def raw25175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25175step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25175 raw25175Labels = mixedMoment B node625 node625Labels := by
  calc
    mixedMoment B raw25175 raw25175Labels = mixedMoment B raw25175step0 raw25175step0Labels := by
      have ha : raw25175step0 = (fun i j => raw25175 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25175step0 raw25175; decide +kernel
      have hl : raw25175step0Labels = raw25175Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25175 raw25175Labels permutation158 permutation3
    _ = mixedMoment B node625 node625Labels := by rfl

def raw25176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25176 raw25176Labels = mixedMoment B node1316 node1316Labels := by
  calc
    mixedMoment B raw25176 raw25176Labels = mixedMoment B raw25176step0 raw25176step0Labels := by
      have ha : raw25176step0 = (fun i j => raw25176 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25176step0 raw25176; decide +kernel
      have hl : raw25176step0Labels = raw25176Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25176 raw25176Labels permutation158 permutation3
    _ = mixedMoment B node1316 node1316Labels := by rfl

def raw25177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25177step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25177 raw25177Labels = mixedMoment B node1386 node1386Labels := by
  calc
    mixedMoment B raw25177 raw25177Labels = mixedMoment B raw25177step0 raw25177step0Labels := by
      have ha : raw25177step0 = (fun i j => raw25177 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25177step0 raw25177; decide +kernel
      have hl : raw25177step0Labels = raw25177Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25177 raw25177Labels permutation158 permutation3
    _ = mixedMoment B node1386 node1386Labels := by rfl

def raw25178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25178 raw25178Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw25178 raw25178Labels = mixedMoment B raw25178step0 raw25178step0Labels := by
      have hz : ∀ j, raw25178 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25178step0 = (fun i j => raw25178 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25178step0 raw25178; decide +kernel
      have hl : raw25178step0Labels = raw25178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25178 raw25178Labels permutation520 hz
    mixedMoment B raw25178step0 raw25178step0Labels = mixedMoment B raw25178step1 raw25178step1Labels := by
      have ha : raw25178step1 = (fun i j => raw25178step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25178step1 raw25178step0; decide +kernel
      have hl : raw25178step1Labels = raw25178step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25178step0 raw25178step0Labels permutation34 permutation3
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw25179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25179 raw25179Labels = mixedMoment B node1409 node1409Labels := by
  calc
    mixedMoment B raw25179 raw25179Labels = mixedMoment B raw25179step0 raw25179step0Labels := by
      have ha : raw25179step0 = (fun i j => raw25179 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25179step0 raw25179; decide +kernel
      have hl : raw25179step0Labels = raw25179Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25179 raw25179Labels permutation162 permutation3
    _ = mixedMoment B node1409 node1409Labels := by rfl

def raw25180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25180 raw25180Labels = mixedMoment B node632 node632Labels := by
  calc
    mixedMoment B raw25180 raw25180Labels = mixedMoment B raw25180step0 raw25180step0Labels := by
      have hz : ∀ j, raw25180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25180step0 = (fun i j => raw25180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25180step0 raw25180; decide +kernel
      have hl : raw25180step0Labels = raw25180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25180 raw25180Labels permutation346 hz
    mixedMoment B raw25180step0 raw25180step0Labels = mixedMoment B raw25180step1 raw25180step1Labels := by
      have ha : raw25180step1 = (fun i j => raw25180step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25180step1 raw25180step0; decide +kernel
      have hl : raw25180step1Labels = raw25180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25180step0 raw25180step0Labels permutation34 permutation3
    _ = mixedMoment B node632 node632Labels := by rfl

def raw25181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25181 raw25181Labels = mixedMoment B node1322 node1322Labels := by
  calc
    mixedMoment B raw25181 raw25181Labels = mixedMoment B raw25181step0 raw25181step0Labels := by
      have hz : ∀ j, raw25181 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25181step0 = (fun i j => raw25181 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25181step0 raw25181; decide +kernel
      have hl : raw25181step0Labels = raw25181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25181 raw25181Labels permutation346 hz
    mixedMoment B raw25181step0 raw25181step0Labels = mixedMoment B raw25181step1 raw25181step1Labels := by
      have ha : raw25181step1 = (fun i j => raw25181step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25181step1 raw25181step0; decide +kernel
      have hl : raw25181step1Labels = raw25181step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25181step0 raw25181step0Labels permutation34 permutation3
    _ = mixedMoment B node1322 node1322Labels := by rfl

def raw25182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25182 raw25182Labels = mixedMoment B node1331 node1331Labels := by
  calc
    mixedMoment B raw25182 raw25182Labels = mixedMoment B raw25182step0 raw25182step0Labels := by
      have ha : raw25182step0 = (fun i j => raw25182 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25182step0 raw25182; decide +kernel
      have hl : raw25182step0Labels = raw25182Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25182 raw25182Labels permutation178 permutation3
    _ = mixedMoment B node1331 node1331Labels := by rfl

def raw25183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25183step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25183step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw25183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25183 raw25183Labels = mixedMoment B node1420 node1420Labels := by
  calc
    mixedMoment B raw25183 raw25183Labels = mixedMoment B raw25183step0 raw25183step0Labels := by
      have hz : ∀ j, raw25183 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25183step0 = (fun i j => raw25183 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25183step0 raw25183; decide +kernel
      have hl : raw25183step0Labels = raw25183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25183 raw25183Labels permutation520 hz
    mixedMoment B raw25183step0 raw25183step0Labels = mixedMoment B raw25183step1 raw25183step1Labels := by
      have hz : ∀ j, raw25183step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25183step1 = (fun i j => raw25183step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25183step1 raw25183step0; decide +kernel
      have hl : raw25183step1Labels = raw25183step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25183step0 raw25183step0Labels permutation80 hz
    mixedMoment B raw25183step1 raw25183step1Labels = mixedMoment B raw25183step2 raw25183step2Labels := by
      have ha : raw25183step2 = (fun i j => raw25183step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25183step2 raw25183step1; decide +kernel
      have hl : raw25183step2Labels = raw25183step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25183step1 raw25183step1Labels permutation8 permutation3
    _ = mixedMoment B node1420 node1420Labels := by rfl

def raw25184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25184 raw25184Labels = mixedMoment B node1411 node1411Labels := by
  calc
    mixedMoment B raw25184 raw25184Labels = mixedMoment B raw25184step0 raw25184step0Labels := by
      have hz : ∀ j, raw25184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25184step0 = (fun i j => raw25184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25184step0 raw25184; decide +kernel
      have hl : raw25184step0Labels = raw25184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25184 raw25184Labels permutation346 hz
    mixedMoment B raw25184step0 raw25184step0Labels = mixedMoment B raw25184step1 raw25184step1Labels := by
      have ha : raw25184step1 = (fun i j => raw25184step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25184step1 raw25184step0; decide +kernel
      have hl : raw25184step1Labels = raw25184step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25184step0 raw25184step0Labels permutation37 permutation3
    _ = mixedMoment B node1411 node1411Labels := by rfl

def raw25185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25185 raw25185Labels = mixedMoment B node627 node627Labels := by
  calc
    mixedMoment B raw25185 raw25185Labels = mixedMoment B raw25185step0 raw25185step0Labels := by
      have hz : ∀ j, raw25185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25185step0 = (fun i j => raw25185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25185step0 raw25185; decide +kernel
      have hl : raw25185step0Labels = raw25185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25185 raw25185Labels permutation346 hz
    mixedMoment B raw25185step0 raw25185step0Labels = mixedMoment B raw25185step1 raw25185step1Labels := by
      have ha : raw25185step1 = (fun i j => raw25185step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25185step1 raw25185step0; decide +kernel
      have hl : raw25185step1Labels = raw25185step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25185step0 raw25185step0Labels permutation33 permutation3
    _ = mixedMoment B node627 node627Labels := by rfl

def raw25186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25186Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25186step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25186 raw25186Labels = mixedMoment B node1318 node1318Labels := by
  calc
    mixedMoment B raw25186 raw25186Labels = mixedMoment B raw25186step0 raw25186step0Labels := by
      have hz : ∀ j, raw25186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25186step0 = (fun i j => raw25186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25186step0 raw25186; decide +kernel
      have hl : raw25186step0Labels = raw25186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25186 raw25186Labels permutation346 hz
    mixedMoment B raw25186step0 raw25186step0Labels = mixedMoment B raw25186step1 raw25186step1Labels := by
      have ha : raw25186step1 = (fun i j => raw25186step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25186step1 raw25186step0; decide +kernel
      have hl : raw25186step1Labels = raw25186step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25186step0 raw25186step0Labels permutation33 permutation3
    _ = mixedMoment B node1318 node1318Labels := by rfl

def raw25187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25187Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw25187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25187 raw25187Labels = mixedMoment B node1328 node1328Labels := by
  calc
    mixedMoment B raw25187 raw25187Labels = mixedMoment B raw25187step0 raw25187step0Labels := by
      have ha : raw25187step0 = (fun i j => raw25187 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25187step0 raw25187; decide +kernel
      have hl : raw25187step0Labels = raw25187Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25187 raw25187Labels permutation177 permutation3
    _ = mixedMoment B node1328 node1328Labels := by rfl

def raw25188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25188Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25188step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw25188step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25188 raw25188Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw25188 raw25188Labels = mixedMoment B raw25188step0 raw25188step0Labels := by
      have hz : ∀ j, raw25188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25188step0 = (fun i j => raw25188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25188step0 raw25188; decide +kernel
      have hl : raw25188step0Labels = raw25188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25188 raw25188Labels permutation346 hz
    mixedMoment B raw25188step0 raw25188step0Labels = mixedMoment B raw25188step1 raw25188step1Labels := by
      have ha : raw25188step1 = (fun i j => raw25188step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25188step1 raw25188step0; decide +kernel
      have hl : raw25188step1Labels = raw25188step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25188step0 raw25188step0Labels permutation33 permutation3
    _ = mixedMoment B node1391 node1391Labels := by rfl

def raw25189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25189Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw25189step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25189 raw25189Labels = mixedMoment B node1410 node1410Labels := by
  calc
    mixedMoment B raw25189 raw25189Labels = mixedMoment B raw25189step0 raw25189step0Labels := by
      have hz : ∀ j, raw25189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25189step0 = (fun i j => raw25189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25189step0 raw25189; decide +kernel
      have hl : raw25189step0Labels = raw25189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25189 raw25189Labels permutation346 hz
    mixedMoment B raw25189step0 raw25189step0Labels = mixedMoment B raw25189step1 raw25189step1Labels := by
      have ha : raw25189step1 = (fun i j => raw25189step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25189step1 raw25189step0; decide +kernel
      have hl : raw25189step1Labels = raw25189step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25189step0 raw25189step0Labels permutation33 permutation3
    _ = mixedMoment B node1410 node1410Labels := by rfl

def raw25190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25190Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25190step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25190 raw25190Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw25190 raw25190Labels = mixedMoment B raw25190step0 raw25190step0Labels := by
      have hz : ∀ j, raw25190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25190step0 = (fun i j => raw25190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25190step0 raw25190; decide +kernel
      have hl : raw25190step0Labels = raw25190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25190 raw25190Labels permutation346 hz
    mixedMoment B raw25190step0 raw25190step0Labels = mixedMoment B raw25190step1 raw25190step1Labels := by
      have ha : raw25190step1 = (fun i j => raw25190step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25190step1 raw25190step0; decide +kernel
      have hl : raw25190step1Labels = raw25190step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25190step0 raw25190step0Labels permutation32 permutation3
    _ = mixedMoment B node626 node626Labels := by rfl

def raw25191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25191Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25191step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25191 raw25191Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw25191 raw25191Labels = mixedMoment B raw25191step0 raw25191step0Labels := by
      have hz : ∀ j, raw25191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25191step0 = (fun i j => raw25191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25191step0 raw25191; decide +kernel
      have hl : raw25191step0Labels = raw25191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25191 raw25191Labels permutation346 hz
    mixedMoment B raw25191step0 raw25191step0Labels = mixedMoment B raw25191step1 raw25191step1Labels := by
      have ha : raw25191step1 = (fun i j => raw25191step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25191step1 raw25191step0; decide +kernel
      have hl : raw25191step1Labels = raw25191step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25191step0 raw25191step0Labels permutation32 permutation3
    _ = mixedMoment B node1317 node1317Labels := by rfl

def raw25192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25192Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw25192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25192 raw25192Labels = mixedMoment B node1327 node1327Labels := by
  calc
    mixedMoment B raw25192 raw25192Labels = mixedMoment B raw25192step0 raw25192step0Labels := by
      have ha : raw25192step0 = (fun i j => raw25192 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25192step0 raw25192; decide +kernel
      have hl : raw25192step0Labels = raw25192Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25192 raw25192Labels permutation176 permutation3
    _ = mixedMoment B node1327 node1327Labels := by rfl

def raw25193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25193Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw25193step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw25193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25193 raw25193Labels = mixedMoment B node1388 node1388Labels := by
  calc
    mixedMoment B raw25193 raw25193Labels = mixedMoment B raw25193step0 raw25193step0Labels := by
      have hz : ∀ j, raw25193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25193step0 = (fun i j => raw25193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25193step0 raw25193; decide +kernel
      have hl : raw25193step0Labels = raw25193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25193 raw25193Labels permutation346 hz
    mixedMoment B raw25193step0 raw25193step0Labels = mixedMoment B raw25193step1 raw25193step1Labels := by
      have ha : raw25193step1 = (fun i j => raw25193step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25193step1 raw25193step0; decide +kernel
      have hl : raw25193step1Labels = raw25193step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25193step0 raw25193step0Labels permutation32 permutation3
    _ = mixedMoment B node1388 node1388Labels := by rfl

def raw25194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw25194Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw25194step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25194step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw25194step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25194step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw25194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25194 raw25194Labels = mixedMoment B node1413 node1413Labels := by
  calc
    mixedMoment B raw25194 raw25194Labels = mixedMoment B raw25194step0 raw25194step0Labels := by
      have hz : ∀ j, raw25194 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25194step0 = (fun i j => raw25194 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25194step0 raw25194; decide +kernel
      have hl : raw25194step0Labels = raw25194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25194 raw25194Labels permutation520 hz
    mixedMoment B raw25194step0 raw25194step0Labels = mixedMoment B raw25194step1 raw25194step1Labels := by
      have hz : ∀ j, raw25194step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25194step1 = (fun i j => raw25194step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25194step1 raw25194step0; decide +kernel
      have hl : raw25194step1Labels = raw25194step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25194step0 raw25194step0Labels permutation80 hz
    mixedMoment B raw25194step1 raw25194step1Labels = mixedMoment B raw25194step2 raw25194step2Labels := by
      have ha : raw25194step2 = (fun i j => raw25194step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25194step2 raw25194step1; decide +kernel
      have hl : raw25194step2Labels = raw25194step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25194step1 raw25194step1Labels permutation8 permutation3
    _ = mixedMoment B node1413 node1413Labels := by rfl

def raw25195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25195 raw25195Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw25195 raw25195Labels = mixedMoment B raw25195step0 raw25195step0Labels := by
      have hz : ∀ j, raw25195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25195step0 = (fun i j => raw25195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25195step0 raw25195; decide +kernel
      have hl : raw25195step0Labels = raw25195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25195 raw25195Labels permutation346 hz
    mixedMoment B raw25195step0 raw25195step0Labels = mixedMoment B raw25195step1 raw25195step1Labels := by
      have ha : raw25195step1 = (fun i j => raw25195step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25195step1 raw25195step0; decide +kernel
      have hl : raw25195step1Labels = raw25195step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25195step0 raw25195step0Labels permutation44 permutation7
    mixedMoment B raw25195step1 raw25195step1Labels = mixedMoment B raw25195step2 raw25195step2Labels := by
      have ha : raw25195step2 = -raw25195step1 := by apply Matrix.ext; change ∀ i j, raw25195step2 i j = -(raw25195step1 i j); unfold raw25195step2 raw25195step1; decide +kernel
      have hl : raw25195step2Labels = raw25195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25195step2 raw25195step2Labels = mixedMoment B raw25195step3 raw25195step3Labels := by
      have ha : raw25195step3 = raw25195step2 := by apply Matrix.ext; unfold raw25195step3 raw25195step2; decide +kernel
      have hl : raw25195step2Labels = labelEmbedding1 ∘ raw25195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25195step2 raw25195step2Labels raw25195step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw25196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25196 raw25196Labels = mixedMoment B node2202 node2202Labels := by
  calc
    mixedMoment B raw25196 raw25196Labels = mixedMoment B raw25196step0 raw25196step0Labels := by
      have ha : raw25196step0 = (fun i j => raw25196 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25196step0 raw25196; decide +kernel
      have hl : raw25196step0Labels = raw25196Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25196 raw25196Labels permutation188 permutation7
    mixedMoment B raw25196step0 raw25196step0Labels = mixedMoment B raw25196step1 raw25196step1Labels := by
      have ha : raw25196step1 = -raw25196step0 := by apply Matrix.ext; change ∀ i j, raw25196step1 i j = -(raw25196step0 i j); unfold raw25196step1 raw25196step0; decide +kernel
      have hl : raw25196step1Labels = raw25196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25196step1 raw25196step1Labels = mixedMoment B raw25196step2 raw25196step2Labels := by
      have ha : raw25196step2 = raw25196step1 := by apply Matrix.ext; unfold raw25196step2 raw25196step1; decide +kernel
      have hl : raw25196step1Labels = labelEmbedding1 ∘ raw25196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25196step1 raw25196step1Labels raw25196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2202 node2202Labels := by rfl

def raw25197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25197step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25197step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25197step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25197step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25197 raw25197Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw25197 raw25197Labels = mixedMoment B raw25197step0 raw25197step0Labels := by
      have hz : ∀ j, raw25197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25197step0 = (fun i j => raw25197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25197step0 raw25197; decide +kernel
      have hl : raw25197step0Labels = raw25197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25197 raw25197Labels permutation346 hz
    mixedMoment B raw25197step0 raw25197step0Labels = mixedMoment B raw25197step1 raw25197step1Labels := by
      have ha : raw25197step1 = (fun i j => raw25197step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25197step1 raw25197step0; decide +kernel
      have hl : raw25197step1Labels = raw25197step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25197step0 raw25197step0Labels permutation44 permutation7
    mixedMoment B raw25197step1 raw25197step1Labels = mixedMoment B raw25197step2 raw25197step2Labels := by
      have ha : raw25197step2 = -raw25197step1 := by apply Matrix.ext; change ∀ i j, raw25197step2 i j = -(raw25197step1 i j); unfold raw25197step2 raw25197step1; decide +kernel
      have hl : raw25197step2Labels = raw25197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25197step2 raw25197step2Labels = mixedMoment B raw25197step3 raw25197step3Labels := by
      have ha : raw25197step3 = raw25197step2 := by apply Matrix.ext; unfold raw25197step3 raw25197step2; decide +kernel
      have hl : raw25197step2Labels = labelEmbedding1 ∘ raw25197step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25197step2 raw25197step2Labels raw25197step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw25198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25198step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25198step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25198step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25198step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25198step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25198step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25198step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25198step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25198step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25198 raw25198Labels = mixedMoment B node2291 node2291Labels := by
  calc
    mixedMoment B raw25198 raw25198Labels = mixedMoment B raw25198step0 raw25198step0Labels := by
      have hz : ∀ j, raw25198 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25198step0 = (fun i j => raw25198 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25198step0 raw25198; decide +kernel
      have hl : raw25198step0Labels = raw25198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25198 raw25198Labels permutation520 hz
    mixedMoment B raw25198step0 raw25198step0Labels = mixedMoment B raw25198step1 raw25198step1Labels := by
      have hz : ∀ j, raw25198step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25198step1 = (fun i j => raw25198step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25198step1 raw25198step0; decide +kernel
      have hl : raw25198step1Labels = raw25198step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25198step0 raw25198step0Labels permutation80 hz
    mixedMoment B raw25198step1 raw25198step1Labels = mixedMoment B raw25198step2 raw25198step2Labels := by
      have ha : raw25198step2 = (fun i j => raw25198step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25198step2 raw25198step1; decide +kernel
      have hl : raw25198step2Labels = raw25198step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25198step1 raw25198step1Labels permutation8 permutation7
    mixedMoment B raw25198step2 raw25198step2Labels = mixedMoment B raw25198step3 raw25198step3Labels := by
      have ha : raw25198step3 = -raw25198step2 := by apply Matrix.ext; change ∀ i j, raw25198step3 i j = -(raw25198step2 i j); unfold raw25198step3 raw25198step2; decide +kernel
      have hl : raw25198step3Labels = raw25198step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25198step3 raw25198step3Labels = mixedMoment B raw25198step4 raw25198step4Labels := by
      have ha : raw25198step4 = raw25198step3 := by apply Matrix.ext; unfold raw25198step4 raw25198step3; decide +kernel
      have hl : raw25198step3Labels = labelEmbedding1 ∘ raw25198step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25198step3 raw25198step3Labels raw25198step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2291 node2291Labels := by rfl

def raw25199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25199step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25199step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25199step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25199step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25199 raw25199Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw25199 raw25199Labels = mixedMoment B raw25199step0 raw25199step0Labels := by
      have hz : ∀ j, raw25199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25199step0 = (fun i j => raw25199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25199step0 raw25199; decide +kernel
      have hl : raw25199step0Labels = raw25199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25199 raw25199Labels permutation346 hz
    mixedMoment B raw25199step0 raw25199step0Labels = mixedMoment B raw25199step1 raw25199step1Labels := by
      have ha : raw25199step1 = (fun i j => raw25199step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25199step1 raw25199step0; decide +kernel
      have hl : raw25199step1Labels = raw25199step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25199step0 raw25199step0Labels permutation44 permutation7
    mixedMoment B raw25199step1 raw25199step1Labels = mixedMoment B raw25199step2 raw25199step2Labels := by
      have ha : raw25199step2 = -raw25199step1 := by apply Matrix.ext; change ∀ i j, raw25199step2 i j = -(raw25199step1 i j); unfold raw25199step2 raw25199step1; decide +kernel
      have hl : raw25199step2Labels = raw25199step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25199step2 raw25199step2Labels = mixedMoment B raw25199step3 raw25199step3Labels := by
      have ha : raw25199step3 = raw25199step2 := by apply Matrix.ext; unfold raw25199step3 raw25199step2; decide +kernel
      have hl : raw25199step2Labels = labelEmbedding1 ∘ raw25199step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25199step2 raw25199step2Labels raw25199step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw25200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25200step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25200step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25200step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25200 raw25200Labels = mixedMoment B node1517 node1517Labels := by
  calc
    mixedMoment B raw25200 raw25200Labels = mixedMoment B raw25200step0 raw25200step0Labels := by
      have hz : ∀ j, raw25200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25200step0 = (fun i j => raw25200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25200step0 raw25200; decide +kernel
      have hl : raw25200step0Labels = raw25200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25200 raw25200Labels permutation346 hz
    mixedMoment B raw25200step0 raw25200step0Labels = mixedMoment B raw25200step1 raw25200step1Labels := by
      have ha : raw25200step1 = (fun i j => raw25200step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25200step1 raw25200step0; decide +kernel
      have hl : raw25200step1Labels = raw25200step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25200step0 raw25200step0Labels permutation44 permutation7
    mixedMoment B raw25200step1 raw25200step1Labels = mixedMoment B raw25200step2 raw25200step2Labels := by
      have ha : raw25200step2 = -raw25200step1 := by apply Matrix.ext; change ∀ i j, raw25200step2 i j = -(raw25200step1 i j); unfold raw25200step2 raw25200step1; decide +kernel
      have hl : raw25200step2Labels = raw25200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25200step2 raw25200step2Labels = mixedMoment B raw25200step3 raw25200step3Labels := by
      have ha : raw25200step3 = raw25200step2 := by apply Matrix.ext; unfold raw25200step3 raw25200step2; decide +kernel
      have hl : raw25200step2Labels = labelEmbedding1 ∘ raw25200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25200step2 raw25200step2Labels raw25200step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1517 node1517Labels := by rfl

def raw25201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25201step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25201step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25201step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25201 raw25201Labels = mixedMoment B node1673 node1673Labels := by
  calc
    mixedMoment B raw25201 raw25201Labels = mixedMoment B raw25201step0 raw25201step0Labels := by
      have ha : raw25201step0 = (fun i j => raw25201 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25201step0 raw25201; decide +kernel
      have hl : raw25201step0Labels = raw25201Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25201 raw25201Labels permutation188 permutation7
    mixedMoment B raw25201step0 raw25201step0Labels = mixedMoment B raw25201step1 raw25201step1Labels := by
      have ha : raw25201step1 = -raw25201step0 := by apply Matrix.ext; change ∀ i j, raw25201step1 i j = -(raw25201step0 i j); unfold raw25201step1 raw25201step0; decide +kernel
      have hl : raw25201step1Labels = raw25201step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25201step1 raw25201step1Labels = mixedMoment B raw25201step2 raw25201step2Labels := by
      have ha : raw25201step2 = raw25201step1 := by apply Matrix.ext; unfold raw25201step2 raw25201step1; decide +kernel
      have hl : raw25201step1Labels = labelEmbedding1 ∘ raw25201step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25201step1 raw25201step1Labels raw25201step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1673 node1673Labels := by rfl

def raw25202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25202 raw25202Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw25202 raw25202Labels = mixedMoment B raw25202step0 raw25202step0Labels := by
      have hz : ∀ j, raw25202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25202step0 = (fun i j => raw25202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25202step0 raw25202; decide +kernel
      have hl : raw25202step0Labels = raw25202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25202 raw25202Labels permutation346 hz
    mixedMoment B raw25202step0 raw25202step0Labels = mixedMoment B raw25202step1 raw25202step1Labels := by
      have ha : raw25202step1 = (fun i j => raw25202step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25202step1 raw25202step0; decide +kernel
      have hl : raw25202step1Labels = raw25202step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25202step0 raw25202step0Labels permutation46 permutation7
    mixedMoment B raw25202step1 raw25202step1Labels = mixedMoment B raw25202step2 raw25202step2Labels := by
      have ha : raw25202step2 = -raw25202step1 := by apply Matrix.ext; change ∀ i j, raw25202step2 i j = -(raw25202step1 i j); unfold raw25202step2 raw25202step1; decide +kernel
      have hl : raw25202step2Labels = raw25202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25202step2 raw25202step2Labels = mixedMoment B raw25202step3 raw25202step3Labels := by
      have ha : raw25202step3 = raw25202step2 := by apply Matrix.ext; unfold raw25202step3 raw25202step2; decide +kernel
      have hl : raw25202step2Labels = labelEmbedding1 ∘ raw25202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25202step2 raw25202step2Labels raw25202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw25203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25203step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw25203step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25203step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25203step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25203step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25203step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw25203step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25203 raw25203Labels = mixedMoment B node1753 node1753Labels := by
  calc
    mixedMoment B raw25203 raw25203Labels = mixedMoment B raw25203step0 raw25203step0Labels := by
      have hz : ∀ j, raw25203 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25203step0 = (fun i j => raw25203 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25203step0 raw25203; decide +kernel
      have hl : raw25203step0Labels = raw25203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25203 raw25203Labels permutation520 hz
    mixedMoment B raw25203step0 raw25203step0Labels = mixedMoment B raw25203step1 raw25203step1Labels := by
      have hz : ∀ j, raw25203step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25203step1 = (fun i j => raw25203step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25203step1 raw25203step0; decide +kernel
      have hl : raw25203step1Labels = raw25203step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25203step0 raw25203step0Labels permutation80 hz
    mixedMoment B raw25203step1 raw25203step1Labels = mixedMoment B raw25203step2 raw25203step2Labels := by
      have ha : raw25203step2 = (fun i j => raw25203step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25203step2 raw25203step1; decide +kernel
      have hl : raw25203step2Labels = raw25203step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25203step1 raw25203step1Labels permutation8 permutation7
    mixedMoment B raw25203step2 raw25203step2Labels = mixedMoment B raw25203step3 raw25203step3Labels := by
      have ha : raw25203step3 = -raw25203step2 := by apply Matrix.ext; change ∀ i j, raw25203step3 i j = -(raw25203step2 i j); unfold raw25203step3 raw25203step2; decide +kernel
      have hl : raw25203step3Labels = raw25203step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25203step3 raw25203step3Labels = mixedMoment B raw25203step4 raw25203step4Labels := by
      have ha : raw25203step4 = raw25203step3 := by apply Matrix.ext; unfold raw25203step4 raw25203step3; decide +kernel
      have hl : raw25203step3Labels = labelEmbedding1 ∘ raw25203step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25203step3 raw25203step3Labels raw25203step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1753 node1753Labels := by rfl

def raw25204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25204step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25204step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25204 raw25204Labels = mixedMoment B node1726 node1726Labels := by
  calc
    mixedMoment B raw25204 raw25204Labels = mixedMoment B raw25204step0 raw25204step0Labels := by
      have hz : ∀ j, raw25204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25204step0 = (fun i j => raw25204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25204step0 raw25204; decide +kernel
      have hl : raw25204step0Labels = raw25204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25204 raw25204Labels permutation346 hz
    mixedMoment B raw25204step0 raw25204step0Labels = mixedMoment B raw25204step1 raw25204step1Labels := by
      have ha : raw25204step1 = (fun i j => raw25204step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25204step1 raw25204step0; decide +kernel
      have hl : raw25204step1Labels = raw25204step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25204step0 raw25204step0Labels permutation44 permutation7
    mixedMoment B raw25204step1 raw25204step1Labels = mixedMoment B raw25204step2 raw25204step2Labels := by
      have ha : raw25204step2 = -raw25204step1 := by apply Matrix.ext; change ∀ i j, raw25204step2 i j = -(raw25204step1 i j); unfold raw25204step2 raw25204step1; decide +kernel
      have hl : raw25204step2Labels = raw25204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25204step2 raw25204step2Labels = mixedMoment B raw25204step3 raw25204step3Labels := by
      have ha : raw25204step3 = raw25204step2 := by apply Matrix.ext; unfold raw25204step3 raw25204step2; decide +kernel
      have hl : raw25204step2Labels = labelEmbedding1 ∘ raw25204step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25204step2 raw25204step2Labels raw25204step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1726 node1726Labels := by rfl

def raw25205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25205step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25205step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25205step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25205step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25205 raw25205Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw25205 raw25205Labels = mixedMoment B raw25205step0 raw25205step0Labels := by
      have ha : raw25205step0 = (fun i j => raw25205 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25205step0 raw25205; decide +kernel
      have hl : raw25205step0Labels = raw25205Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25205 raw25205Labels permutation188 permutation7
    mixedMoment B raw25205step0 raw25205step0Labels = mixedMoment B raw25205step1 raw25205step1Labels := by
      have ha : raw25205step1 = -raw25205step0 := by apply Matrix.ext; change ∀ i j, raw25205step1 i j = -(raw25205step0 i j); unfold raw25205step1 raw25205step0; decide +kernel
      have hl : raw25205step1Labels = raw25205step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25205step1 raw25205step1Labels = mixedMoment B raw25205step2 raw25205step2Labels := by
      have ha : raw25205step2 = raw25205step1 := by apply Matrix.ext; unfold raw25205step2 raw25205step1; decide +kernel
      have hl : raw25205step1Labels = labelEmbedding1 ∘ raw25205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25205step1 raw25205step1Labels raw25205step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

def raw25206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25206step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25206step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25206step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25206 raw25206Labels = mixedMoment B node1703 node1703Labels := by
  calc
    mixedMoment B raw25206 raw25206Labels = mixedMoment B raw25206step0 raw25206step0Labels := by
      have ha : raw25206step0 = (fun i j => raw25206 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25206step0 raw25206; decide +kernel
      have hl : raw25206step0Labels = raw25206Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25206 raw25206Labels permutation188 permutation7
    mixedMoment B raw25206step0 raw25206step0Labels = mixedMoment B raw25206step1 raw25206step1Labels := by
      have ha : raw25206step1 = -raw25206step0 := by apply Matrix.ext; change ∀ i j, raw25206step1 i j = -(raw25206step0 i j); unfold raw25206step1 raw25206step0; decide +kernel
      have hl : raw25206step1Labels = raw25206step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25206step1 raw25206step1Labels = mixedMoment B raw25206step2 raw25206step2Labels := by
      have ha : raw25206step2 = raw25206step1 := by apply Matrix.ext; unfold raw25206step2 raw25206step1; decide +kernel
      have hl : raw25206step1Labels = labelEmbedding1 ∘ raw25206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25206step1 raw25206step1Labels raw25206step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1703 node1703Labels := by rfl

def raw25207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25207step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25207step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25207 raw25207Labels = mixedMoment B node1705 node1705Labels := by
  calc
    mixedMoment B raw25207 raw25207Labels = mixedMoment B raw25207step0 raw25207step0Labels := by
      have ha : raw25207step0 = (fun i j => raw25207 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25207step0 raw25207; decide +kernel
      have hl : raw25207step0Labels = raw25207Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25207 raw25207Labels permutation188 permutation7
    mixedMoment B raw25207step0 raw25207step0Labels = mixedMoment B raw25207step1 raw25207step1Labels := by
      have ha : raw25207step1 = -raw25207step0 := by apply Matrix.ext; change ∀ i j, raw25207step1 i j = -(raw25207step0 i j); unfold raw25207step1 raw25207step0; decide +kernel
      have hl : raw25207step1Labels = raw25207step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25207step1 raw25207step1Labels = mixedMoment B raw25207step2 raw25207step2Labels := by
      have ha : raw25207step2 = raw25207step1 := by apply Matrix.ext; unfold raw25207step2 raw25207step1; decide +kernel
      have hl : raw25207step1Labels = labelEmbedding1 ∘ raw25207step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25207step1 raw25207step1Labels raw25207step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1705 node1705Labels := by rfl

def raw25208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw25208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25208step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25208step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25208 raw25208Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw25208 raw25208Labels = mixedMoment B raw25208step0 raw25208step0Labels := by
      have hz : ∀ j, raw25208 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25208step0 = (fun i j => raw25208 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25208step0 raw25208; decide +kernel
      have hl : raw25208step0Labels = raw25208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25208 raw25208Labels permutation520 hz
    mixedMoment B raw25208step0 raw25208step0Labels = mixedMoment B raw25208step1 raw25208step1Labels := by
      have ha : raw25208step1 = (fun i j => raw25208step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25208step1 raw25208step0; decide +kernel
      have hl : raw25208step1Labels = raw25208step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25208step0 raw25208step0Labels permutation38 permutation7
    mixedMoment B raw25208step1 raw25208step1Labels = mixedMoment B raw25208step2 raw25208step2Labels := by
      have ha : raw25208step2 = -raw25208step1 := by apply Matrix.ext; change ∀ i j, raw25208step2 i j = -(raw25208step1 i j); unfold raw25208step2 raw25208step1; decide +kernel
      have hl : raw25208step2Labels = raw25208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25208step2 raw25208step2Labels = mixedMoment B raw25208step3 raw25208step3Labels := by
      have ha : raw25208step3 = raw25208step2 := by apply Matrix.ext; unfold raw25208step3 raw25208step2; decide +kernel
      have hl : raw25208step2Labels = labelEmbedding1 ∘ raw25208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25208step2 raw25208step2Labels raw25208step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw25209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25209step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25209 raw25209Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw25209 raw25209Labels = mixedMoment B raw25209step0 raw25209step0Labels := by
      have ha : raw25209step0 = (fun i j => raw25209 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25209step0 raw25209; decide +kernel
      have hl : raw25209step0Labels = raw25209Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25209 raw25209Labels permutation188 permutation7
    mixedMoment B raw25209step0 raw25209step0Labels = mixedMoment B raw25209step1 raw25209step1Labels := by
      have ha : raw25209step1 = -raw25209step0 := by apply Matrix.ext; change ∀ i j, raw25209step1 i j = -(raw25209step0 i j); unfold raw25209step1 raw25209step0; decide +kernel
      have hl : raw25209step1Labels = raw25209step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25209step1 raw25209step1Labels = mixedMoment B raw25209step2 raw25209step2Labels := by
      have ha : raw25209step2 = raw25209step1 := by apply Matrix.ext; unfold raw25209step2 raw25209step1; decide +kernel
      have hl : raw25209step1Labels = labelEmbedding1 ∘ raw25209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25209step1 raw25209step1Labels raw25209step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw25210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw25210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25210step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25210step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25210step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25210 raw25210Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw25210 raw25210Labels = mixedMoment B raw25210step0 raw25210step0Labels := by
      have hz : ∀ j, raw25210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25210step0 = (fun i j => raw25210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25210step0 raw25210; decide +kernel
      have hl : raw25210step0Labels = raw25210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25210 raw25210Labels permutation346 hz
    mixedMoment B raw25210step0 raw25210step0Labels = mixedMoment B raw25210step1 raw25210step1Labels := by
      have ha : raw25210step1 = (fun i j => raw25210step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25210step1 raw25210step0; decide +kernel
      have hl : raw25210step1Labels = raw25210step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25210step0 raw25210step0Labels permutation44 permutation7
    mixedMoment B raw25210step1 raw25210step1Labels = mixedMoment B raw25210step2 raw25210step2Labels := by
      have ha : raw25210step2 = -raw25210step1 := by apply Matrix.ext; change ∀ i j, raw25210step2 i j = -(raw25210step1 i j); unfold raw25210step2 raw25210step1; decide +kernel
      have hl : raw25210step2Labels = raw25210step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25210step2 raw25210step2Labels = mixedMoment B raw25210step3 raw25210step3Labels := by
      have ha : raw25210step3 = raw25210step2 := by apply Matrix.ext; unfold raw25210step3 raw25210step2; decide +kernel
      have hl : raw25210step2Labels = labelEmbedding1 ∘ raw25210step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25210step2 raw25210step2Labels raw25210step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

def raw25211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw25211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw25211step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25211step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw25211step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25211 raw25211Labels = mixedMoment B node1721 node1721Labels := by
  calc
    mixedMoment B raw25211 raw25211Labels = mixedMoment B raw25211step0 raw25211step0Labels := by
      have hz : ∀ j, raw25211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25211step0 = (fun i j => raw25211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25211step0 raw25211; decide +kernel
      have hl : raw25211step0Labels = raw25211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25211 raw25211Labels permutation346 hz
    mixedMoment B raw25211step0 raw25211step0Labels = mixedMoment B raw25211step1 raw25211step1Labels := by
      have ha : raw25211step1 = (fun i j => raw25211step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25211step1 raw25211step0; decide +kernel
      have hl : raw25211step1Labels = raw25211step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25211step0 raw25211step0Labels permutation44 permutation7
    mixedMoment B raw25211step1 raw25211step1Labels = mixedMoment B raw25211step2 raw25211step2Labels := by
      have ha : raw25211step2 = -raw25211step1 := by apply Matrix.ext; change ∀ i j, raw25211step2 i j = -(raw25211step1 i j); unfold raw25211step2 raw25211step1; decide +kernel
      have hl : raw25211step2Labels = raw25211step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25211step2 raw25211step2Labels = mixedMoment B raw25211step3 raw25211step3Labels := by
      have ha : raw25211step3 = raw25211step2 := by apply Matrix.ext; unfold raw25211step3 raw25211step2; decide +kernel
      have hl : raw25211step2Labels = labelEmbedding1 ∘ raw25211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25211step2 raw25211step2Labels raw25211step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1721 node1721Labels := by rfl

def raw25212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw25212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw25212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25212step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25212 raw25212Labels = mixedMoment B node1671 node1671Labels := by
  calc
    mixedMoment B raw25212 raw25212Labels = mixedMoment B raw25212step0 raw25212step0Labels := by
      have ha : raw25212step0 = (fun i j => raw25212 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25212step0 raw25212; decide +kernel
      have hl : raw25212step0Labels = raw25212Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25212 raw25212Labels permutation188 permutation7
    mixedMoment B raw25212step0 raw25212step0Labels = mixedMoment B raw25212step1 raw25212step1Labels := by
      have ha : raw25212step1 = -raw25212step0 := by apply Matrix.ext; change ∀ i j, raw25212step1 i j = -(raw25212step0 i j); unfold raw25212step1 raw25212step0; decide +kernel
      have hl : raw25212step1Labels = raw25212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25212step1 raw25212step1Labels = mixedMoment B raw25212step2 raw25212step2Labels := by
      have ha : raw25212step2 = raw25212step1 := by apply Matrix.ext; unfold raw25212step2 raw25212step1; decide +kernel
      have hl : raw25212step1Labels = labelEmbedding1 ∘ raw25212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25212step1 raw25212step1Labels raw25212step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1671 node1671Labels := by rfl

def raw25213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw25213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw25213step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw25213step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw25213step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25213step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25213step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw25213step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25213 raw25213Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw25213 raw25213Labels = mixedMoment B raw25213step0 raw25213step0Labels := by
      have hz : ∀ j, raw25213 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25213step0 = (fun i j => raw25213 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25213step0 raw25213; decide +kernel
      have hl : raw25213step0Labels = raw25213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25213 raw25213Labels permutation520 hz
    mixedMoment B raw25213step0 raw25213step0Labels = mixedMoment B raw25213step1 raw25213step1Labels := by
      have hz : ∀ j, raw25213step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25213step1 = (fun i j => raw25213step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25213step1 raw25213step0; decide +kernel
      have hl : raw25213step1Labels = raw25213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25213step0 raw25213step0Labels permutation80 hz
    mixedMoment B raw25213step1 raw25213step1Labels = mixedMoment B raw25213step2 raw25213step2Labels := by
      have ha : raw25213step2 = (fun i j => raw25213step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25213step2 raw25213step1; decide +kernel
      have hl : raw25213step2Labels = raw25213step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25213step1 raw25213step1Labels permutation8 permutation7
    mixedMoment B raw25213step2 raw25213step2Labels = mixedMoment B raw25213step3 raw25213step3Labels := by
      have ha : raw25213step3 = -raw25213step2 := by apply Matrix.ext; change ∀ i j, raw25213step3 i j = -(raw25213step2 i j); unfold raw25213step3 raw25213step2; decide +kernel
      have hl : raw25213step3Labels = raw25213step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25213step3 raw25213step3Labels = mixedMoment B raw25213step4 raw25213step4Labels := by
      have ha : raw25213step4 = raw25213step3 := by apply Matrix.ext; unfold raw25213step4 raw25213step3; decide +kernel
      have hl : raw25213step3Labels = labelEmbedding1 ∘ raw25213step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25213step3 raw25213step3Labels raw25213step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1751 node1751Labels := by rfl

def raw25214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw25214step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25214step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25214step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25214step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25214 raw25214Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw25214 raw25214Labels = mixedMoment B raw25214step0 raw25214step0Labels := by
      have hz : ∀ j, raw25214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25214step0 = (fun i j => raw25214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25214step0 raw25214; decide +kernel
      have hl : raw25214step0Labels = raw25214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25214 raw25214Labels permutation346 hz
    mixedMoment B raw25214step0 raw25214step0Labels = mixedMoment B raw25214step1 raw25214step1Labels := by
      have ha : raw25214step1 = (fun i j => raw25214step0 (permutation45 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25214step1 raw25214step0; decide +kernel
      have hl : raw25214step1Labels = raw25214step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25214step0 raw25214step0Labels permutation45 permutation7
    mixedMoment B raw25214step1 raw25214step1Labels = mixedMoment B raw25214step2 raw25214step2Labels := by
      have ha : raw25214step2 = -raw25214step1 := by apply Matrix.ext; change ∀ i j, raw25214step2 i j = -(raw25214step1 i j); unfold raw25214step2 raw25214step1; decide +kernel
      have hl : raw25214step2Labels = raw25214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25214step2 raw25214step2Labels = mixedMoment B raw25214step3 raw25214step3Labels := by
      have ha : raw25214step3 = raw25214step2 := by apply Matrix.ext; unfold raw25214step3 raw25214step2; decide +kernel
      have hl : raw25214step2Labels = labelEmbedding1 ∘ raw25214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25214step2 raw25214step2Labels raw25214step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw25215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25215step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25215step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25215step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25215 raw25215Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw25215 raw25215Labels = mixedMoment B raw25215step0 raw25215step0Labels := by
      have hz : ∀ j, raw25215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25215step0 = (fun i j => raw25215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25215step0 raw25215; decide +kernel
      have hl : raw25215step0Labels = raw25215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25215 raw25215Labels permutation346 hz
    mixedMoment B raw25215step0 raw25215step0Labels = mixedMoment B raw25215step1 raw25215step1Labels := by
      have ha : raw25215step1 = (fun i j => raw25215step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25215step1 raw25215step0; decide +kernel
      have hl : raw25215step1Labels = raw25215step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25215step0 raw25215step0Labels permutation44 permutation7
    mixedMoment B raw25215step1 raw25215step1Labels = mixedMoment B raw25215step2 raw25215step2Labels := by
      have ha : raw25215step2 = -raw25215step1 := by apply Matrix.ext; change ∀ i j, raw25215step2 i j = -(raw25215step1 i j); unfold raw25215step2 raw25215step1; decide +kernel
      have hl : raw25215step2Labels = raw25215step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25215step2 raw25215step2Labels = mixedMoment B raw25215step3 raw25215step3Labels := by
      have ha : raw25215step3 = raw25215step2 := by apply Matrix.ext; unfold raw25215step3 raw25215step2; decide +kernel
      have hl : raw25215step2Labels = labelEmbedding1 ∘ raw25215step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25215step2 raw25215step2Labels raw25215step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
