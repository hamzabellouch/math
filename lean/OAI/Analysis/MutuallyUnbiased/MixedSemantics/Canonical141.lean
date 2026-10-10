import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18048step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18048step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18048step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18048 raw18048Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw18048 raw18048Labels = mixedMoment B raw18048step0 raw18048step0Labels := by
      have hz : ∀ j, raw18048 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18048step0 = (fun i j => raw18048 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18048step0 raw18048; decide +kernel
      have hl : raw18048step0Labels = raw18048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18048 raw18048Labels permutation434 hz
    mixedMoment B raw18048step0 raw18048step0Labels = mixedMoment B raw18048step1 raw18048step1Labels := by
      have ha : raw18048step1 = (fun i j => raw18048step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18048step1 raw18048step0; decide +kernel
      have hl : raw18048step1Labels = raw18048step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18048step0 raw18048step0Labels permutation32 permutation3
    mixedMoment B raw18048step1 raw18048step1Labels = mixedMoment B raw18048step2 raw18048step2Labels := by
      have ha : raw18048step2 = raw18048step1 := by apply Matrix.ext; unfold raw18048step2 raw18048step1; decide +kernel
      have hl : raw18048step1Labels = labelEmbedding6 ∘ raw18048step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18048step1 raw18048step1Labels raw18048step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw18049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18049step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18049step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18049step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18049step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18049 raw18049Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw18049 raw18049Labels = mixedMoment B raw18049step0 raw18049step0Labels := by
      have hz : ∀ j, raw18049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18049step0 = (fun i j => raw18049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18049step0 raw18049; decide +kernel
      have hl : raw18049step0Labels = raw18049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18049 raw18049Labels permutation434 hz
    mixedMoment B raw18049step0 raw18049step0Labels = mixedMoment B raw18049step1 raw18049step1Labels := by
      have ha : raw18049step1 = (fun i j => raw18049step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18049step1 raw18049step0; decide +kernel
      have hl : raw18049step1Labels = raw18049step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18049step0 raw18049step0Labels permutation57 permutation5
    mixedMoment B raw18049step1 raw18049step1Labels = mixedMoment B raw18049step2 raw18049step2Labels := by
      have ha : raw18049step2 = -raw18049step1 := by apply Matrix.ext; change ∀ i j, raw18049step2 i j = -(raw18049step1 i j); unfold raw18049step2 raw18049step1; decide +kernel
      have hl : raw18049step2Labels = raw18049step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18049step2 raw18049step2Labels = mixedMoment B raw18049step3 raw18049step3Labels := by
      have ha : raw18049step3 = raw18049step2 := by apply Matrix.ext; unfold raw18049step3 raw18049step2; decide +kernel
      have hl : raw18049step2Labels = labelEmbedding8 ∘ raw18049step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18049step2 raw18049step2Labels raw18049step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw18050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18050step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18050 raw18050Labels = mixedMoment B node5467 node5467Labels := by
  calc
    mixedMoment B raw18050 raw18050Labels = mixedMoment B raw18050step0 raw18050step0Labels := by
      have ha : raw18050step0 = (fun i j => raw18050 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18050step0 raw18050; decide +kernel
      have hl : raw18050step0Labels = raw18050Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18050 raw18050Labels permutation158 permutation3
    mixedMoment B raw18050step0 raw18050step0Labels = mixedMoment B raw18050step1 raw18050step1Labels := by
      have ha : raw18050step1 = raw18050step0 := by apply Matrix.ext; unfold raw18050step1 raw18050step0; decide +kernel
      have hl : raw18050step0Labels = labelEmbedding6 ∘ raw18050step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18050step0 raw18050step0Labels raw18050step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5467 node5467Labels := by rfl

def raw18051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18051step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18051 raw18051Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18051 raw18051Labels = mixedMoment B raw18051step0 raw18051step0Labels := by
      have hz : ∀ j, raw18051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18051step0 = (fun i j => raw18051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18051step0 raw18051; decide +kernel
      have hl : raw18051step0Labels = raw18051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18051 raw18051Labels permutation434 hz
    mixedMoment B raw18051step0 raw18051step0Labels = mixedMoment B raw18051step1 raw18051step1Labels := by
      have ha : raw18051step1 = (fun i j => raw18051step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18051step1 raw18051step0; decide +kernel
      have hl : raw18051step1Labels = raw18051step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18051step0 raw18051step0Labels permutation34 permutation3
    mixedMoment B raw18051step1 raw18051step1Labels = mixedMoment B raw18051step2 raw18051step2Labels := by
      have ha : raw18051step2 = raw18051step1 := by apply Matrix.ext; unfold raw18051step2 raw18051step1; decide +kernel
      have hl : raw18051step1Labels = labelEmbedding6 ∘ raw18051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18051step1 raw18051step1Labels raw18051step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18052step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18052step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18052step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18052 raw18052Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18052 raw18052Labels = mixedMoment B raw18052step0 raw18052step0Labels := by
      have hz : ∀ j, raw18052 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18052step0 = (fun i j => raw18052 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18052step0 raw18052; decide +kernel
      have hl : raw18052step0Labels = raw18052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18052 raw18052Labels permutation434 hz
    mixedMoment B raw18052step0 raw18052step0Labels = mixedMoment B raw18052step1 raw18052step1Labels := by
      have ha : raw18052step1 = (fun i j => raw18052step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18052step1 raw18052step0; decide +kernel
      have hl : raw18052step1Labels = raw18052step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18052step0 raw18052step0Labels permutation60 permutation5
    mixedMoment B raw18052step1 raw18052step1Labels = mixedMoment B raw18052step2 raw18052step2Labels := by
      have ha : raw18052step2 = -raw18052step1 := by apply Matrix.ext; change ∀ i j, raw18052step2 i j = -(raw18052step1 i j); unfold raw18052step2 raw18052step1; decide +kernel
      have hl : raw18052step2Labels = raw18052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18052step2 raw18052step2Labels = mixedMoment B raw18052step3 raw18052step3Labels := by
      have ha : raw18052step3 = raw18052step2 := by apply Matrix.ext; unfold raw18052step3 raw18052step2; decide +kernel
      have hl : raw18052step2Labels = labelEmbedding8 ∘ raw18052step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18052step2 raw18052step2Labels raw18052step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18053step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18053step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18053 raw18053Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw18053 raw18053Labels = mixedMoment B raw18053step0 raw18053step0Labels := by
      have hz : ∀ j, raw18053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18053step0 = (fun i j => raw18053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18053step0 raw18053; decide +kernel
      have hl : raw18053step0Labels = raw18053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18053 raw18053Labels permutation346 hz
    mixedMoment B raw18053step0 raw18053step0Labels = mixedMoment B raw18053step1 raw18053step1Labels := by
      have ha : raw18053step1 = (fun i j => raw18053step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18053step1 raw18053step0; decide +kernel
      have hl : raw18053step1Labels = raw18053step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18053step0 raw18053step0Labels permutation32 permutation3
    mixedMoment B raw18053step1 raw18053step1Labels = mixedMoment B raw18053step2 raw18053step2Labels := by
      have ha : raw18053step2 = raw18053step1 := by apply Matrix.ext; unfold raw18053step2 raw18053step1; decide +kernel
      have hl : raw18053step1Labels = labelEmbedding6 ∘ raw18053step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18053step1 raw18053step1Labels raw18053step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw18054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18054step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18054step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18054step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18054 raw18054Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw18054 raw18054Labels = mixedMoment B raw18054step0 raw18054step0Labels := by
      have hz : ∀ j, raw18054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18054step0 = (fun i j => raw18054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18054step0 raw18054; decide +kernel
      have hl : raw18054step0Labels = raw18054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18054 raw18054Labels permutation346 hz
    mixedMoment B raw18054step0 raw18054step0Labels = mixedMoment B raw18054step1 raw18054step1Labels := by
      have ha : raw18054step1 = (fun i j => raw18054step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18054step1 raw18054step0; decide +kernel
      have hl : raw18054step1Labels = raw18054step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18054step0 raw18054step0Labels permutation57 permutation5
    mixedMoment B raw18054step1 raw18054step1Labels = mixedMoment B raw18054step2 raw18054step2Labels := by
      have ha : raw18054step2 = -raw18054step1 := by apply Matrix.ext; change ∀ i j, raw18054step2 i j = -(raw18054step1 i j); unfold raw18054step2 raw18054step1; decide +kernel
      have hl : raw18054step2Labels = raw18054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18054step2 raw18054step2Labels = mixedMoment B raw18054step3 raw18054step3Labels := by
      have ha : raw18054step3 = raw18054step2 := by apply Matrix.ext; unfold raw18054step3 raw18054step2; decide +kernel
      have hl : raw18054step2Labels = labelEmbedding8 ∘ raw18054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18054step2 raw18054step2Labels raw18054step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw18055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, -1, -1]]
def raw18055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18055step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18055 raw18055Labels = mixedMoment B node5467 node5467Labels := by
  calc
    mixedMoment B raw18055 raw18055Labels = mixedMoment B raw18055step0 raw18055step0Labels := by
      have ha : raw18055step0 = (fun i j => raw18055 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18055step0 raw18055; decide +kernel
      have hl : raw18055step0Labels = raw18055Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18055 raw18055Labels permutation152 permutation3
    mixedMoment B raw18055step0 raw18055step0Labels = mixedMoment B raw18055step1 raw18055step1Labels := by
      have ha : raw18055step1 = raw18055step0 := by apply Matrix.ext; unfold raw18055step1 raw18055step0; decide +kernel
      have hl : raw18055step0Labels = labelEmbedding6 ∘ raw18055step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18055step0 raw18055step0Labels raw18055step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5467 node5467Labels := by rfl

def raw18056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, -1, -1]]
def raw18056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18056step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18056step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18056 raw18056Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18056 raw18056Labels = mixedMoment B raw18056step0 raw18056step0Labels := by
      have hz : ∀ j, raw18056 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18056step0 = (fun i j => raw18056 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18056step0 raw18056; decide +kernel
      have hl : raw18056step0Labels = raw18056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18056 raw18056Labels permutation346 hz
    mixedMoment B raw18056step0 raw18056step0Labels = mixedMoment B raw18056step1 raw18056step1Labels := by
      have ha : raw18056step1 = (fun i j => raw18056step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18056step1 raw18056step0; decide +kernel
      have hl : raw18056step1Labels = raw18056step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18056step0 raw18056step0Labels permutation34 permutation3
    mixedMoment B raw18056step1 raw18056step1Labels = mixedMoment B raw18056step2 raw18056step2Labels := by
      have ha : raw18056step2 = raw18056step1 := by apply Matrix.ext; unfold raw18056step2 raw18056step1; decide +kernel
      have hl : raw18056step1Labels = labelEmbedding6 ∘ raw18056step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18056step1 raw18056step1Labels raw18056step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1]]
def raw18057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18057step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18057step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18057step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18057 raw18057Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18057 raw18057Labels = mixedMoment B raw18057step0 raw18057step0Labels := by
      have hz : ∀ j, raw18057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18057step0 = (fun i j => raw18057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18057step0 raw18057; decide +kernel
      have hl : raw18057step0Labels = raw18057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18057 raw18057Labels permutation346 hz
    mixedMoment B raw18057step0 raw18057step0Labels = mixedMoment B raw18057step1 raw18057step1Labels := by
      have ha : raw18057step1 = (fun i j => raw18057step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18057step1 raw18057step0; decide +kernel
      have hl : raw18057step1Labels = raw18057step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18057step0 raw18057step0Labels permutation60 permutation5
    mixedMoment B raw18057step1 raw18057step1Labels = mixedMoment B raw18057step2 raw18057step2Labels := by
      have ha : raw18057step2 = -raw18057step1 := by apply Matrix.ext; change ∀ i j, raw18057step2 i j = -(raw18057step1 i j); unfold raw18057step2 raw18057step1; decide +kernel
      have hl : raw18057step2Labels = raw18057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18057step2 raw18057step2Labels = mixedMoment B raw18057step3 raw18057step3Labels := by
      have ha : raw18057step3 = raw18057step2 := by apply Matrix.ext; unfold raw18057step3 raw18057step2; decide +kernel
      have hl : raw18057step2Labels = labelEmbedding8 ∘ raw18057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18057step2 raw18057step2Labels raw18057step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw18058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18058step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18058step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18058step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18058 raw18058Labels = mixedMoment B node5023 node5023Labels := by
  calc
    mixedMoment B raw18058 raw18058Labels = mixedMoment B raw18058step0 raw18058step0Labels := by
      have hz : ∀ j, raw18058 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18058step0 = (fun i j => raw18058 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18058step0 raw18058; decide +kernel
      have hl : raw18058step0Labels = raw18058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18058 raw18058Labels permutation434 hz
    mixedMoment B raw18058step0 raw18058step0Labels = mixedMoment B raw18058step1 raw18058step1Labels := by
      have hz : ∀ j, raw18058step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18058step1 = (fun i j => raw18058step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18058step1 raw18058step0; decide +kernel
      have hl : raw18058step1Labels = raw18058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18058step0 raw18058step0Labels permutation80 hz
    mixedMoment B raw18058step1 raw18058step1Labels = mixedMoment B raw18058step2 raw18058step2Labels := by
      have ha : raw18058step2 = (fun i j => raw18058step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18058step2 raw18058step1; decide +kernel
      have hl : raw18058step2Labels = raw18058step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18058step1 raw18058step1Labels permutation9 permutation3
    mixedMoment B raw18058step2 raw18058step2Labels = mixedMoment B raw18058step3 raw18058step3Labels := by
      have ha : raw18058step3 = raw18058step2 := by apply Matrix.ext; unfold raw18058step3 raw18058step2; decide +kernel
      have hl : raw18058step2Labels = labelEmbedding6 ∘ raw18058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18058step2 raw18058step2Labels raw18058step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5023 node5023Labels := by rfl

def raw18059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![2, -3, 1], ![2, -1, -1]]
def raw18059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18059step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18059step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18059step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18059step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18059 raw18059Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw18059 raw18059Labels = mixedMoment B raw18059step0 raw18059step0Labels := by
      have hz : ∀ j, raw18059 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18059step0 = (fun i j => raw18059 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18059step0 raw18059; decide +kernel
      have hl : raw18059step0Labels = raw18059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18059 raw18059Labels permutation434 hz
    mixedMoment B raw18059step0 raw18059step0Labels = mixedMoment B raw18059step1 raw18059step1Labels := by
      have hz : ∀ j, raw18059step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18059step1 = (fun i j => raw18059step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18059step1 raw18059step0; decide +kernel
      have hl : raw18059step1Labels = raw18059step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18059step0 raw18059step0Labels permutation80 hz
    mixedMoment B raw18059step1 raw18059step1Labels = mixedMoment B raw18059step2 raw18059step2Labels := by
      have ha : raw18059step2 = (fun i j => raw18059step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18059step2 raw18059step1; decide +kernel
      have hl : raw18059step2Labels = raw18059step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18059step1 raw18059step1Labels permutation24 permutation5
    mixedMoment B raw18059step2 raw18059step2Labels = mixedMoment B raw18059step3 raw18059step3Labels := by
      have ha : raw18059step3 = raw18059step2 := by apply Matrix.ext; unfold raw18059step3 raw18059step2; decide +kernel
      have hl : raw18059step2Labels = labelEmbedding8 ∘ raw18059step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18059step2 raw18059step2Labels raw18059step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5021 node5021Labels := by rfl

def raw18060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18060step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18060step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18060 raw18060Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw18060 raw18060Labels = mixedMoment B raw18060step0 raw18060step0Labels := by
      have hz : ∀ j, raw18060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18060step0 = (fun i j => raw18060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18060step0 raw18060; decide +kernel
      have hl : raw18060step0Labels = raw18060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18060 raw18060Labels permutation434 hz
    mixedMoment B raw18060step0 raw18060step0Labels = mixedMoment B raw18060step1 raw18060step1Labels := by
      have ha : raw18060step1 = (fun i j => raw18060step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18060step1 raw18060step0; decide +kernel
      have hl : raw18060step1Labels = raw18060step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18060step0 raw18060step0Labels permutation126 permutation5
    mixedMoment B raw18060step1 raw18060step1Labels = mixedMoment B raw18060step2 raw18060step2Labels := by
      have ha : raw18060step2 = raw18060step1 := by apply Matrix.ext; unfold raw18060step2 raw18060step1; decide +kernel
      have hl : raw18060step1Labels = labelEmbedding8 ∘ raw18060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18060step1 raw18060step1Labels raw18060step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw18061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, -1, -1]]
def raw18061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18061step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18061step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18061 raw18061Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw18061 raw18061Labels = mixedMoment B raw18061step0 raw18061step0Labels := by
      have hz : ∀ j, raw18061 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18061step0 = (fun i j => raw18061 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18061step0 raw18061; decide +kernel
      have hl : raw18061step0Labels = raw18061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18061 raw18061Labels permutation346 hz
    mixedMoment B raw18061step0 raw18061step0Labels = mixedMoment B raw18061step1 raw18061step1Labels := by
      have ha : raw18061step1 = (fun i j => raw18061step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18061step1 raw18061step0; decide +kernel
      have hl : raw18061step1Labels = raw18061step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18061step0 raw18061step0Labels permutation126 permutation5
    mixedMoment B raw18061step1 raw18061step1Labels = mixedMoment B raw18061step2 raw18061step2Labels := by
      have ha : raw18061step2 = raw18061step1 := by apply Matrix.ext; unfold raw18061step2 raw18061step1; decide +kernel
      have hl : raw18061step1Labels = labelEmbedding8 ∘ raw18061step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18061step1 raw18061step1Labels raw18061step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw18062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1]]
def raw18062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1]]
def raw18062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![2, -3, 1], ![1, 0, -1]]
def raw18062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18062step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18062step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18062step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18062 raw18062Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw18062 raw18062Labels = mixedMoment B raw18062step0 raw18062step0Labels := by
      have hz : ∀ j, raw18062 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18062step0 = (fun i j => raw18062 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18062step0 raw18062; decide +kernel
      have hl : raw18062step0Labels = raw18062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18062 raw18062Labels permutation434 hz
    mixedMoment B raw18062step0 raw18062step0Labels = mixedMoment B raw18062step1 raw18062step1Labels := by
      have hz : ∀ j, raw18062step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18062step1 = (fun i j => raw18062step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18062step1 raw18062step0; decide +kernel
      have hl : raw18062step1Labels = raw18062step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18062step0 raw18062step0Labels permutation80 hz
    mixedMoment B raw18062step1 raw18062step1Labels = mixedMoment B raw18062step2 raw18062step2Labels := by
      have ha : raw18062step2 = (fun i j => raw18062step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18062step2 raw18062step1; decide +kernel
      have hl : raw18062step2Labels = raw18062step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18062step1 raw18062step1Labels permutation24 permutation5
    mixedMoment B raw18062step2 raw18062step2Labels = mixedMoment B raw18062step3 raw18062step3Labels := by
      have ha : raw18062step3 = raw18062step2 := by apply Matrix.ext; unfold raw18062step3 raw18062step2; decide +kernel
      have hl : raw18062step2Labels = labelEmbedding8 ∘ raw18062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18062step2 raw18062step2Labels raw18062step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw18063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw18063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18063step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18063step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw18063step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18063 raw18063Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw18063 raw18063Labels = mixedMoment B raw18063step0 raw18063step0Labels := by
      have hz : ∀ j, raw18063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18063step0 = (fun i j => raw18063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18063step0 raw18063; decide +kernel
      have hl : raw18063step0Labels = raw18063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18063 raw18063Labels permutation434 hz
    mixedMoment B raw18063step0 raw18063step0Labels = mixedMoment B raw18063step1 raw18063step1Labels := by
      have hz : ∀ j, raw18063step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18063step1 = (fun i j => raw18063step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18063step1 raw18063step0; decide +kernel
      have hl : raw18063step1Labels = raw18063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18063step0 raw18063step0Labels permutation80 hz
    mixedMoment B raw18063step1 raw18063step1Labels = mixedMoment B raw18063step2 raw18063step2Labels := by
      have ha : raw18063step2 = (fun i j => raw18063step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18063step2 raw18063step1; decide +kernel
      have hl : raw18063step2Labels = raw18063step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18063step1 raw18063step1Labels permutation8 permutation3
    mixedMoment B raw18063step2 raw18063step2Labels = mixedMoment B raw18063step3 raw18063step3Labels := by
      have ha : raw18063step3 = raw18063step2 := by apply Matrix.ext; unfold raw18063step3 raw18063step2; decide +kernel
      have hl : raw18063step2Labels = labelEmbedding6 ∘ raw18063step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18063step2 raw18063step2Labels raw18063step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5021 node5021Labels := by rfl

def raw18064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 3, -1], ![1, -2, 1], ![3, -2, -1]]
def raw18064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-2, 1, 1], ![-2, -1, 3]]
def raw18064step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18064step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18064step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw18064step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18064 raw18064Labels = mixedMoment B node5023 node5023Labels := by
  calc
    mixedMoment B raw18064 raw18064Labels = mixedMoment B raw18064step0 raw18064step0Labels := by
      have hz : ∀ j, raw18064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18064step0 = (fun i j => raw18064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18064step0 raw18064; decide +kernel
      have hl : raw18064step0Labels = raw18064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18064 raw18064Labels permutation434 hz
    mixedMoment B raw18064step0 raw18064step0Labels = mixedMoment B raw18064step1 raw18064step1Labels := by
      have hz : ∀ j, raw18064step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18064step1 = (fun i j => raw18064step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18064step1 raw18064step0; decide +kernel
      have hl : raw18064step1Labels = raw18064step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18064step0 raw18064step0Labels permutation80 hz
    mixedMoment B raw18064step1 raw18064step1Labels = mixedMoment B raw18064step2 raw18064step2Labels := by
      have ha : raw18064step2 = (fun i j => raw18064step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18064step2 raw18064step1; decide +kernel
      have hl : raw18064step2Labels = raw18064step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18064step1 raw18064step1Labels permutation30 permutation3
    mixedMoment B raw18064step2 raw18064step2Labels = mixedMoment B raw18064step3 raw18064step3Labels := by
      have ha : raw18064step3 = -raw18064step2 := by apply Matrix.ext; change ∀ i j, raw18064step3 i j = -(raw18064step2 i j); unfold raw18064step3 raw18064step2; decide +kernel
      have hl : raw18064step3Labels = raw18064step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18064step3 raw18064step3Labels = mixedMoment B raw18064step4 raw18064step4Labels := by
      have ha : raw18064step4 = raw18064step3 := by apply Matrix.ext; unfold raw18064step4 raw18064step3; decide +kernel
      have hl : raw18064step3Labels = labelEmbedding6 ∘ raw18064step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18064step3 raw18064step3Labels raw18064step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5023 node5023Labels := by rfl

def raw18065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18065step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18065step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18065step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18065step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18065step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18065 raw18065Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw18065 raw18065Labels = mixedMoment B raw18065step0 raw18065step0Labels := by
      have hz : ∀ j, raw18065 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18065step0 = (fun i j => raw18065 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18065step0 raw18065; decide +kernel
      have hl : raw18065step0Labels = raw18065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18065 raw18065Labels permutation434 hz
    mixedMoment B raw18065step0 raw18065step0Labels = mixedMoment B raw18065step1 raw18065step1Labels := by
      have ha : raw18065step1 = (fun i j => raw18065step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18065step1 raw18065step0; decide +kernel
      have hl : raw18065step1Labels = raw18065step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18065step0 raw18065step0Labels permutation151 permutation3
    mixedMoment B raw18065step1 raw18065step1Labels = mixedMoment B raw18065step2 raw18065step2Labels := by
      have ha : raw18065step2 = -raw18065step1 := by apply Matrix.ext; change ∀ i j, raw18065step2 i j = -(raw18065step1 i j); unfold raw18065step2 raw18065step1; decide +kernel
      have hl : raw18065step2Labels = raw18065step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18065step2 raw18065step2Labels = mixedMoment B raw18065step3 raw18065step3Labels := by
      have ha : raw18065step3 = raw18065step2 := by apply Matrix.ext; unfold raw18065step3 raw18065step2; decide +kernel
      have hl : raw18065step2Labels = labelEmbedding6 ∘ raw18065step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18065step2 raw18065step2Labels raw18065step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw18066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -2, -1]]
def raw18066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18066step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18066step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18066step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw18066step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18066 raw18066Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw18066 raw18066Labels = mixedMoment B raw18066step0 raw18066step0Labels := by
      have hz : ∀ j, raw18066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18066step0 = (fun i j => raw18066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18066step0 raw18066; decide +kernel
      have hl : raw18066step0Labels = raw18066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18066 raw18066Labels permutation346 hz
    mixedMoment B raw18066step0 raw18066step0Labels = mixedMoment B raw18066step1 raw18066step1Labels := by
      have ha : raw18066step1 = (fun i j => raw18066step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18066step1 raw18066step0; decide +kernel
      have hl : raw18066step1Labels = raw18066step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18066step0 raw18066step0Labels permutation151 permutation3
    mixedMoment B raw18066step1 raw18066step1Labels = mixedMoment B raw18066step2 raw18066step2Labels := by
      have ha : raw18066step2 = -raw18066step1 := by apply Matrix.ext; change ∀ i j, raw18066step2 i j = -(raw18066step1 i j); unfold raw18066step2 raw18066step1; decide +kernel
      have hl : raw18066step2Labels = raw18066step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18066step2 raw18066step2Labels = mixedMoment B raw18066step3 raw18066step3Labels := by
      have ha : raw18066step3 = raw18066step2 := by apply Matrix.ext; unfold raw18066step3 raw18066step2; decide +kernel
      have hl : raw18066step2Labels = labelEmbedding6 ∘ raw18066step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18066step2 raw18066step2Labels raw18066step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw18067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw18067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw18067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![3, -2, -1]]
def raw18067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw18067step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18067step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18067step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18067step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw18067step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18067 raw18067Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw18067 raw18067Labels = mixedMoment B raw18067step0 raw18067step0Labels := by
      have hz : ∀ j, raw18067 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18067step0 = (fun i j => raw18067 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18067step0 raw18067; decide +kernel
      have hl : raw18067step0Labels = raw18067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18067 raw18067Labels permutation434 hz
    mixedMoment B raw18067step0 raw18067step0Labels = mixedMoment B raw18067step1 raw18067step1Labels := by
      have hz : ∀ j, raw18067step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18067step1 = (fun i j => raw18067step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18067step1 raw18067step0; decide +kernel
      have hl : raw18067step1Labels = raw18067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18067step0 raw18067step0Labels permutation80 hz
    mixedMoment B raw18067step1 raw18067step1Labels = mixedMoment B raw18067step2 raw18067step2Labels := by
      have ha : raw18067step2 = (fun i j => raw18067step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18067step2 raw18067step1; decide +kernel
      have hl : raw18067step2Labels = raw18067step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18067step1 raw18067step1Labels permutation31 permutation3
    mixedMoment B raw18067step2 raw18067step2Labels = mixedMoment B raw18067step3 raw18067step3Labels := by
      have ha : raw18067step3 = -raw18067step2 := by apply Matrix.ext; change ∀ i j, raw18067step3 i j = -(raw18067step2 i j); unfold raw18067step3 raw18067step2; decide +kernel
      have hl : raw18067step3Labels = raw18067step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18067step3 raw18067step3Labels = mixedMoment B raw18067step4 raw18067step4Labels := by
      have ha : raw18067step4 = raw18067step3 := by apply Matrix.ext; unfold raw18067step4 raw18067step3; decide +kernel
      have hl : raw18067step3Labels = labelEmbedding6 ∘ raw18067step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18067step3 raw18067step3Labels raw18067step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw18068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw18068step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18068step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18068step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18068step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18068step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18068 raw18068Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw18068 raw18068Labels = mixedMoment B raw18068step0 raw18068step0Labels := by
      have hz : ∀ j, raw18068 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18068step0 = (fun i j => raw18068 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18068step0 raw18068; decide +kernel
      have hl : raw18068step0Labels = raw18068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18068 raw18068Labels permutation434 hz
    mixedMoment B raw18068step0 raw18068step0Labels = mixedMoment B raw18068step1 raw18068step1Labels := by
      have hz : ∀ j, raw18068step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18068step1 = (fun i j => raw18068step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18068step1 raw18068step0; decide +kernel
      have hl : raw18068step1Labels = raw18068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18068step0 raw18068step0Labels permutation80 hz
    mixedMoment B raw18068step1 raw18068step1Labels = mixedMoment B raw18068step2 raw18068step2Labels := by
      have ha : raw18068step2 = (fun i j => raw18068step1 (permutation18 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18068step2 raw18068step1; decide +kernel
      have hl : raw18068step2Labels = raw18068step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18068step1 raw18068step1Labels permutation18 permutation5
    mixedMoment B raw18068step2 raw18068step2Labels = mixedMoment B raw18068step3 raw18068step3Labels := by
      have ha : raw18068step3 = -raw18068step2 := by apply Matrix.ext; change ∀ i j, raw18068step3 i j = -(raw18068step2 i j); unfold raw18068step3 raw18068step2; decide +kernel
      have hl : raw18068step3Labels = raw18068step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18068step3 raw18068step3Labels = mixedMoment B raw18068step4 raw18068step4Labels := by
      have ha : raw18068step4 = raw18068step3 := by apply Matrix.ext; unfold raw18068step4 raw18068step3; decide +kernel
      have hl : raw18068step3Labels = labelEmbedding8 ∘ raw18068step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18068step3 raw18068step3Labels raw18068step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw18069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18069step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18069step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18069 raw18069Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw18069 raw18069Labels = mixedMoment B raw18069step0 raw18069step0Labels := by
      have hz : ∀ j, raw18069 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18069step0 = (fun i j => raw18069 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18069step0 raw18069; decide +kernel
      have hl : raw18069step0Labels = raw18069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18069 raw18069Labels permutation434 hz
    mixedMoment B raw18069step0 raw18069step0Labels = mixedMoment B raw18069step1 raw18069step1Labels := by
      have ha : raw18069step1 = (fun i j => raw18069step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18069step1 raw18069step0; decide +kernel
      have hl : raw18069step1Labels = raw18069step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18069step0 raw18069step0Labels permutation137 permutation7
    mixedMoment B raw18069step1 raw18069step1Labels = mixedMoment B raw18069step2 raw18069step2Labels := by
      have ha : raw18069step2 = raw18069step1 := by apply Matrix.ext; unfold raw18069step2 raw18069step1; decide +kernel
      have hl : raw18069step1Labels = labelEmbedding10 ∘ raw18069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18069step1 raw18069step1Labels raw18069step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw18070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18070step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18070 raw18070Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw18070 raw18070Labels = mixedMoment B raw18070step0 raw18070step0Labels := by
      have hz : ∀ j, raw18070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18070step0 = (fun i j => raw18070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18070step0 raw18070; decide +kernel
      have hl : raw18070step0Labels = raw18070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18070 raw18070Labels permutation346 hz
    mixedMoment B raw18070step0 raw18070step0Labels = mixedMoment B raw18070step1 raw18070step1Labels := by
      have ha : raw18070step1 = (fun i j => raw18070step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18070step1 raw18070step0; decide +kernel
      have hl : raw18070step1Labels = raw18070step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18070step0 raw18070step0Labels permutation137 permutation7
    mixedMoment B raw18070step1 raw18070step1Labels = mixedMoment B raw18070step2 raw18070step2Labels := by
      have ha : raw18070step2 = raw18070step1 := by apply Matrix.ext; unfold raw18070step2 raw18070step1; decide +kernel
      have hl : raw18070step1Labels = labelEmbedding10 ∘ raw18070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18070step1 raw18070step1Labels raw18070step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw18071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18071step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18071step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18071step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18071 raw18071Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw18071 raw18071Labels = mixedMoment B raw18071step0 raw18071step0Labels := by
      have hz : ∀ j, raw18071 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18071step0 = (fun i j => raw18071 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18071step0 raw18071; decide +kernel
      have hl : raw18071step0Labels = raw18071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18071 raw18071Labels permutation434 hz
    mixedMoment B raw18071step0 raw18071step0Labels = mixedMoment B raw18071step1 raw18071step1Labels := by
      have hz : ∀ j, raw18071step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18071step1 = (fun i j => raw18071step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18071step1 raw18071step0; decide +kernel
      have hl : raw18071step1Labels = raw18071step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18071step0 raw18071step0Labels permutation80 hz
    mixedMoment B raw18071step1 raw18071step1Labels = mixedMoment B raw18071step2 raw18071step2Labels := by
      have ha : raw18071step2 = (fun i j => raw18071step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18071step2 raw18071step1; decide +kernel
      have hl : raw18071step2Labels = raw18071step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18071step1 raw18071step1Labels permutation29 permutation7
    mixedMoment B raw18071step2 raw18071step2Labels = mixedMoment B raw18071step3 raw18071step3Labels := by
      have ha : raw18071step3 = raw18071step2 := by apply Matrix.ext; unfold raw18071step3 raw18071step2; decide +kernel
      have hl : raw18071step2Labels = labelEmbedding10 ∘ raw18071step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18071step2 raw18071step2Labels raw18071step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw18072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18072step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18072step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18072step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw18072step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18072 raw18072Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw18072 raw18072Labels = mixedMoment B raw18072step0 raw18072step0Labels := by
      have hz : ∀ j, raw18072 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18072step0 = (fun i j => raw18072 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18072step0 raw18072; decide +kernel
      have hl : raw18072step0Labels = raw18072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18072 raw18072Labels permutation434 hz
    mixedMoment B raw18072step0 raw18072step0Labels = mixedMoment B raw18072step1 raw18072step1Labels := by
      have hz : ∀ j, raw18072step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18072step1 = (fun i j => raw18072step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18072step1 raw18072step0; decide +kernel
      have hl : raw18072step1Labels = raw18072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18072step0 raw18072step0Labels permutation80 hz
    mixedMoment B raw18072step1 raw18072step1Labels = mixedMoment B raw18072step2 raw18072step2Labels := by
      have ha : raw18072step2 = (fun i j => raw18072step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18072step2 raw18072step1; decide +kernel
      have hl : raw18072step2Labels = raw18072step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18072step1 raw18072step1Labels permutation21 permutation4
    mixedMoment B raw18072step2 raw18072step2Labels = mixedMoment B raw18072step3 raw18072step3Labels := by
      have ha : raw18072step3 = raw18072step2 := by apply Matrix.ext; unfold raw18072step3 raw18072step2; decide +kernel
      have hl : raw18072step2Labels = labelEmbedding7 ∘ raw18072step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18072step2 raw18072step2Labels raw18072step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

def raw18073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18073step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18073step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18073step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18073step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18073 raw18073Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw18073 raw18073Labels = mixedMoment B raw18073step0 raw18073step0Labels := by
      have hz : ∀ j, raw18073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18073step0 = (fun i j => raw18073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18073step0 raw18073; decide +kernel
      have hl : raw18073step0Labels = raw18073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18073 raw18073Labels permutation434 hz
    mixedMoment B raw18073step0 raw18073step0Labels = mixedMoment B raw18073step1 raw18073step1Labels := by
      have ha : raw18073step1 = (fun i j => raw18073step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18073step1 raw18073step0; decide +kernel
      have hl : raw18073step1Labels = raw18073step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18073step0 raw18073step0Labels permutation60 permutation5
    mixedMoment B raw18073step1 raw18073step1Labels = mixedMoment B raw18073step2 raw18073step2Labels := by
      have ha : raw18073step2 = -raw18073step1 := by apply Matrix.ext; change ∀ i j, raw18073step2 i j = -(raw18073step1 i j); unfold raw18073step2 raw18073step1; decide +kernel
      have hl : raw18073step2Labels = raw18073step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18073step2 raw18073step2Labels = mixedMoment B raw18073step3 raw18073step3Labels := by
      have ha : raw18073step3 = raw18073step2 := by apply Matrix.ext; unfold raw18073step3 raw18073step2; decide +kernel
      have hl : raw18073step2Labels = labelEmbedding8 ∘ raw18073step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18073step2 raw18073step2Labels raw18073step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw18074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18074 raw18074Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw18074 raw18074Labels = mixedMoment B raw18074step0 raw18074step0Labels := by
      have ha : raw18074step0 = (fun i j => raw18074 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18074step0 raw18074; decide +kernel
      have hl : raw18074step0Labels = raw18074Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18074 raw18074Labels permutation202 permutation2
    _ = mixedMoment B node5420 node5420Labels := by rfl

def raw18075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18075 raw18075Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18075 raw18075Labels = mixedMoment B raw18075step0 raw18075step0Labels := by
      have hz : ∀ j, raw18075 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18075step0 = (fun i j => raw18075 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18075step0 raw18075; decide +kernel
      have hl : raw18075step0Labels = raw18075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18075 raw18075Labels permutation434 hz
    mixedMoment B raw18075step0 raw18075step0Labels = mixedMoment B raw18075step1 raw18075step1Labels := by
      have ha : raw18075step1 = (fun i j => raw18075step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18075step1 raw18075step0; decide +kernel
      have hl : raw18075step1Labels = raw18075step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18075step0 raw18075step0Labels permutation145 permutation2
    mixedMoment B raw18075step1 raw18075step1Labels = mixedMoment B raw18075step2 raw18075step2Labels := by
      have ha : raw18075step2 = -raw18075step1 := by apply Matrix.ext; change ∀ i j, raw18075step2 i j = -(raw18075step1 i j); unfold raw18075step2 raw18075step1; decide +kernel
      have hl : raw18075step2Labels = raw18075step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw18076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18076step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18076step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18076step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18076 raw18076Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw18076 raw18076Labels = mixedMoment B raw18076step0 raw18076step0Labels := by
      have hz : ∀ j, raw18076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18076step0 = (fun i j => raw18076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18076step0 raw18076; decide +kernel
      have hl : raw18076step0Labels = raw18076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18076 raw18076Labels permutation434 hz
    mixedMoment B raw18076step0 raw18076step0Labels = mixedMoment B raw18076step1 raw18076step1Labels := by
      have ha : raw18076step1 = (fun i j => raw18076step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18076step1 raw18076step0; decide +kernel
      have hl : raw18076step1Labels = raw18076step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18076step0 raw18076step0Labels permutation46 permutation7
    mixedMoment B raw18076step1 raw18076step1Labels = mixedMoment B raw18076step2 raw18076step2Labels := by
      have ha : raw18076step2 = -raw18076step1 := by apply Matrix.ext; change ∀ i j, raw18076step2 i j = -(raw18076step1 i j); unfold raw18076step2 raw18076step1; decide +kernel
      have hl : raw18076step2Labels = raw18076step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18076step2 raw18076step2Labels = mixedMoment B raw18076step3 raw18076step3Labels := by
      have ha : raw18076step3 = raw18076step2 := by apply Matrix.ext; unfold raw18076step3 raw18076step2; decide +kernel
      have hl : raw18076step2Labels = labelEmbedding10 ∘ raw18076step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18076step2 raw18076step2Labels raw18076step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw18077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18077step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18077step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18077step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18077 raw18077Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw18077 raw18077Labels = mixedMoment B raw18077step0 raw18077step0Labels := by
      have hz : ∀ j, raw18077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18077step0 = (fun i j => raw18077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18077step0 raw18077; decide +kernel
      have hl : raw18077step0Labels = raw18077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18077 raw18077Labels permutation346 hz
    mixedMoment B raw18077step0 raw18077step0Labels = mixedMoment B raw18077step1 raw18077step1Labels := by
      have ha : raw18077step1 = (fun i j => raw18077step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18077step1 raw18077step0; decide +kernel
      have hl : raw18077step1Labels = raw18077step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18077step0 raw18077step0Labels permutation60 permutation5
    mixedMoment B raw18077step1 raw18077step1Labels = mixedMoment B raw18077step2 raw18077step2Labels := by
      have ha : raw18077step2 = -raw18077step1 := by apply Matrix.ext; change ∀ i j, raw18077step2 i j = -(raw18077step1 i j); unfold raw18077step2 raw18077step1; decide +kernel
      have hl : raw18077step2Labels = raw18077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18077step2 raw18077step2Labels = mixedMoment B raw18077step3 raw18077step3Labels := by
      have ha : raw18077step3 = raw18077step2 := by apply Matrix.ext; unfold raw18077step3 raw18077step2; decide +kernel
      have hl : raw18077step2Labels = labelEmbedding8 ∘ raw18077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18077step2 raw18077step2Labels raw18077step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw18078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18078 raw18078Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw18078 raw18078Labels = mixedMoment B raw18078step0 raw18078step0Labels := by
      have ha : raw18078step0 = (fun i j => raw18078 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18078step0 raw18078; decide +kernel
      have hl : raw18078step0Labels = raw18078Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18078 raw18078Labels permutation178 permutation2
    _ = mixedMoment B node5420 node5420Labels := by rfl

def raw18079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18079 raw18079Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18079 raw18079Labels = mixedMoment B raw18079step0 raw18079step0Labels := by
      have hz : ∀ j, raw18079 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18079step0 = (fun i j => raw18079 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18079step0 raw18079; decide +kernel
      have hl : raw18079step0Labels = raw18079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18079 raw18079Labels permutation346 hz
    mixedMoment B raw18079step0 raw18079step0Labels = mixedMoment B raw18079step1 raw18079step1Labels := by
      have ha : raw18079step1 = (fun i j => raw18079step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18079step1 raw18079step0; decide +kernel
      have hl : raw18079step1Labels = raw18079step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18079step0 raw18079step0Labels permutation145 permutation2
    mixedMoment B raw18079step1 raw18079step1Labels = mixedMoment B raw18079step2 raw18079step2Labels := by
      have ha : raw18079step2 = -raw18079step1 := by apply Matrix.ext; change ∀ i j, raw18079step2 i j = -(raw18079step1 i j); unfold raw18079step2 raw18079step1; decide +kernel
      have hl : raw18079step2Labels = raw18079step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw18080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18080step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18080step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18080step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18080step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18080 raw18080Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw18080 raw18080Labels = mixedMoment B raw18080step0 raw18080step0Labels := by
      have hz : ∀ j, raw18080 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18080step0 = (fun i j => raw18080 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18080step0 raw18080; decide +kernel
      have hl : raw18080step0Labels = raw18080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18080 raw18080Labels permutation346 hz
    mixedMoment B raw18080step0 raw18080step0Labels = mixedMoment B raw18080step1 raw18080step1Labels := by
      have ha : raw18080step1 = (fun i j => raw18080step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18080step1 raw18080step0; decide +kernel
      have hl : raw18080step1Labels = raw18080step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18080step0 raw18080step0Labels permutation46 permutation7
    mixedMoment B raw18080step1 raw18080step1Labels = mixedMoment B raw18080step2 raw18080step2Labels := by
      have ha : raw18080step2 = -raw18080step1 := by apply Matrix.ext; change ∀ i j, raw18080step2 i j = -(raw18080step1 i j); unfold raw18080step2 raw18080step1; decide +kernel
      have hl : raw18080step2Labels = raw18080step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18080step2 raw18080step2Labels = mixedMoment B raw18080step3 raw18080step3Labels := by
      have ha : raw18080step3 = raw18080step2 := by apply Matrix.ext; unfold raw18080step3 raw18080step2; decide +kernel
      have hl : raw18080step2Labels = labelEmbedding10 ∘ raw18080step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18080step2 raw18080step2Labels raw18080step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw18081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18081step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18081step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18081 raw18081Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw18081 raw18081Labels = mixedMoment B raw18081step0 raw18081step0Labels := by
      have hz : ∀ j, raw18081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18081step0 = (fun i j => raw18081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18081step0 raw18081; decide +kernel
      have hl : raw18081step0Labels = raw18081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18081 raw18081Labels permutation434 hz
    mixedMoment B raw18081step0 raw18081step0Labels = mixedMoment B raw18081step1 raw18081step1Labels := by
      have hz : ∀ j, raw18081step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18081step1 = (fun i j => raw18081step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18081step1 raw18081step0; decide +kernel
      have hl : raw18081step1Labels = raw18081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18081step0 raw18081step0Labels permutation80 hz
    mixedMoment B raw18081step1 raw18081step1Labels = mixedMoment B raw18081step2 raw18081step2Labels := by
      have ha : raw18081step2 = (fun i j => raw18081step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18081step2 raw18081step1; decide +kernel
      have hl : raw18081step2Labels = raw18081step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18081step1 raw18081step1Labels permutation24 permutation5
    mixedMoment B raw18081step2 raw18081step2Labels = mixedMoment B raw18081step3 raw18081step3Labels := by
      have ha : raw18081step3 = raw18081step2 := by apply Matrix.ext; unfold raw18081step3 raw18081step2; decide +kernel
      have hl : raw18081step2Labels = labelEmbedding8 ∘ raw18081step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18081step2 raw18081step2Labels raw18081step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5235 node5235Labels := by rfl

def raw18082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18082step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18082 raw18082Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw18082 raw18082Labels = mixedMoment B raw18082step0 raw18082step0Labels := by
      have hz : ∀ j, raw18082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18082step0 = (fun i j => raw18082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18082step0 raw18082; decide +kernel
      have hl : raw18082step0Labels = raw18082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18082 raw18082Labels permutation434 hz
    mixedMoment B raw18082step0 raw18082step0Labels = mixedMoment B raw18082step1 raw18082step1Labels := by
      have ha : raw18082step1 = (fun i j => raw18082step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18082step1 raw18082step0; decide +kernel
      have hl : raw18082step1Labels = raw18082step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18082step0 raw18082step0Labels permutation123 permutation5
    mixedMoment B raw18082step1 raw18082step1Labels = mixedMoment B raw18082step2 raw18082step2Labels := by
      have ha : raw18082step2 = raw18082step1 := by apply Matrix.ext; unfold raw18082step2 raw18082step1; decide +kernel
      have hl : raw18082step1Labels = labelEmbedding8 ∘ raw18082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18082step1 raw18082step1Labels raw18082step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw18083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18083step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18083step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18083 raw18083Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw18083 raw18083Labels = mixedMoment B raw18083step0 raw18083step0Labels := by
      have hz : ∀ j, raw18083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18083step0 = (fun i j => raw18083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18083step0 raw18083; decide +kernel
      have hl : raw18083step0Labels = raw18083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18083 raw18083Labels permutation346 hz
    mixedMoment B raw18083step0 raw18083step0Labels = mixedMoment B raw18083step1 raw18083step1Labels := by
      have ha : raw18083step1 = (fun i j => raw18083step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18083step1 raw18083step0; decide +kernel
      have hl : raw18083step1Labels = raw18083step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18083step0 raw18083step0Labels permutation123 permutation5
    mixedMoment B raw18083step1 raw18083step1Labels = mixedMoment B raw18083step2 raw18083step2Labels := by
      have ha : raw18083step2 = raw18083step1 := by apply Matrix.ext; unfold raw18083step2 raw18083step1; decide +kernel
      have hl : raw18083step1Labels = labelEmbedding8 ∘ raw18083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18083step1 raw18083step1Labels raw18083step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw18084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18084step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18084step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18084step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18084 raw18084Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw18084 raw18084Labels = mixedMoment B raw18084step0 raw18084step0Labels := by
      have hz : ∀ j, raw18084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18084step0 = (fun i j => raw18084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18084step0 raw18084; decide +kernel
      have hl : raw18084step0Labels = raw18084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18084 raw18084Labels permutation434 hz
    mixedMoment B raw18084step0 raw18084step0Labels = mixedMoment B raw18084step1 raw18084step1Labels := by
      have hz : ∀ j, raw18084step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18084step1 = (fun i j => raw18084step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18084step1 raw18084step0; decide +kernel
      have hl : raw18084step1Labels = raw18084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18084step0 raw18084step0Labels permutation80 hz
    mixedMoment B raw18084step1 raw18084step1Labels = mixedMoment B raw18084step2 raw18084step2Labels := by
      have ha : raw18084step2 = (fun i j => raw18084step1 (permutation21 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18084step2 raw18084step1; decide +kernel
      have hl : raw18084step2Labels = raw18084step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18084step1 raw18084step1Labels permutation21 permutation5
    mixedMoment B raw18084step2 raw18084step2Labels = mixedMoment B raw18084step3 raw18084step3Labels := by
      have ha : raw18084step3 = raw18084step2 := by apply Matrix.ext; unfold raw18084step3 raw18084step2; decide +kernel
      have hl : raw18084step2Labels = labelEmbedding8 ∘ raw18084step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18084step2 raw18084step2Labels raw18084step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw18085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw18085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18085step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18085step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18085 raw18085Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw18085 raw18085Labels = mixedMoment B raw18085step0 raw18085step0Labels := by
      have hz : ∀ j, raw18085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18085step0 = (fun i j => raw18085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18085step0 raw18085; decide +kernel
      have hl : raw18085step0Labels = raw18085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18085 raw18085Labels permutation434 hz
    mixedMoment B raw18085step0 raw18085step0Labels = mixedMoment B raw18085step1 raw18085step1Labels := by
      have hz : ∀ j, raw18085step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18085step1 = (fun i j => raw18085step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18085step1 raw18085step0; decide +kernel
      have hl : raw18085step1Labels = raw18085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18085step0 raw18085step0Labels permutation80 hz
    mixedMoment B raw18085step1 raw18085step1Labels = mixedMoment B raw18085step2 raw18085step2Labels := by
      have ha : raw18085step2 = (fun i j => raw18085step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18085step2 raw18085step1; decide +kernel
      have hl : raw18085step2Labels = raw18085step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18085step1 raw18085step1Labels permutation31 permutation2
    mixedMoment B raw18085step2 raw18085step2Labels = mixedMoment B raw18085step3 raw18085step3Labels := by
      have ha : raw18085step3 = -raw18085step2 := by apply Matrix.ext; change ∀ i j, raw18085step3 i j = -(raw18085step2 i j); unfold raw18085step3 raw18085step2; decide +kernel
      have hl : raw18085step3Labels = raw18085step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw18086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18086 raw18086Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw18086 raw18086Labels = mixedMoment B raw18086step0 raw18086step0Labels := by
      have hz : ∀ j, raw18086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18086step0 = (fun i j => raw18086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18086step0 raw18086; decide +kernel
      have hl : raw18086step0Labels = raw18086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18086 raw18086Labels permutation434 hz
    mixedMoment B raw18086step0 raw18086step0Labels = mixedMoment B raw18086step1 raw18086step1Labels := by
      have ha : raw18086step1 = (fun i j => raw18086step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18086step1 raw18086step0; decide +kernel
      have hl : raw18086step1Labels = raw18086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18086step0 raw18086step0Labels permutation149 permutation2
    mixedMoment B raw18086step1 raw18086step1Labels = mixedMoment B raw18086step2 raw18086step2Labels := by
      have ha : raw18086step2 = -raw18086step1 := by apply Matrix.ext; change ∀ i j, raw18086step2 i j = -(raw18086step1 i j); unfold raw18086step2 raw18086step1; decide +kernel
      have hl : raw18086step2Labels = raw18086step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw18087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18087 raw18087Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw18087 raw18087Labels = mixedMoment B raw18087step0 raw18087step0Labels := by
      have hz : ∀ j, raw18087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18087step0 = (fun i j => raw18087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18087step0 raw18087; decide +kernel
      have hl : raw18087step0Labels = raw18087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18087 raw18087Labels permutation346 hz
    mixedMoment B raw18087step0 raw18087step0Labels = mixedMoment B raw18087step1 raw18087step1Labels := by
      have ha : raw18087step1 = (fun i j => raw18087step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18087step1 raw18087step0; decide +kernel
      have hl : raw18087step1Labels = raw18087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18087step0 raw18087step0Labels permutation149 permutation2
    mixedMoment B raw18087step1 raw18087step1Labels = mixedMoment B raw18087step2 raw18087step2Labels := by
      have ha : raw18087step2 = -raw18087step1 := by apply Matrix.ext; change ∀ i j, raw18087step2 i j = -(raw18087step1 i j); unfold raw18087step2 raw18087step1; decide +kernel
      have hl : raw18087step2Labels = raw18087step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw18088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18088step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18088step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw18088step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18088step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18088step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18088step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18088 raw18088Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw18088 raw18088Labels = mixedMoment B raw18088step0 raw18088step0Labels := by
      have hz : ∀ j, raw18088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18088step0 = (fun i j => raw18088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18088step0 raw18088; decide +kernel
      have hl : raw18088step0Labels = raw18088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18088 raw18088Labels permutation434 hz
    mixedMoment B raw18088step0 raw18088step0Labels = mixedMoment B raw18088step1 raw18088step1Labels := by
      have hz : ∀ j, raw18088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18088step1 = (fun i j => raw18088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18088step1 raw18088step0; decide +kernel
      have hl : raw18088step1Labels = raw18088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18088step0 raw18088step0Labels permutation80 hz
    mixedMoment B raw18088step1 raw18088step1Labels = mixedMoment B raw18088step2 raw18088step2Labels := by
      have ha : raw18088step2 = (fun i j => raw18088step1 (permutation18 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18088step2 raw18088step1; decide +kernel
      have hl : raw18088step2Labels = raw18088step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18088step1 raw18088step1Labels permutation18 permutation5
    mixedMoment B raw18088step2 raw18088step2Labels = mixedMoment B raw18088step3 raw18088step3Labels := by
      have ha : raw18088step3 = -raw18088step2 := by apply Matrix.ext; change ∀ i j, raw18088step3 i j = -(raw18088step2 i j); unfold raw18088step3 raw18088step2; decide +kernel
      have hl : raw18088step3Labels = raw18088step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18088step3 raw18088step3Labels = mixedMoment B raw18088step4 raw18088step4Labels := by
      have ha : raw18088step4 = raw18088step3 := by apply Matrix.ext; unfold raw18088step4 raw18088step3; decide +kernel
      have hl : raw18088step3Labels = labelEmbedding1 ∘ raw18088step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18088step3 raw18088step3Labels raw18088step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw18089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18089step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18089 raw18089Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw18089 raw18089Labels = mixedMoment B raw18089step0 raw18089step0Labels := by
      have hz : ∀ j, raw18089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18089step0 = (fun i j => raw18089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18089step0 raw18089; decide +kernel
      have hl : raw18089step0Labels = raw18089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18089 raw18089Labels permutation434 hz
    mixedMoment B raw18089step0 raw18089step0Labels = mixedMoment B raw18089step1 raw18089step1Labels := by
      have ha : raw18089step1 = (fun i j => raw18089step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18089step1 raw18089step0; decide +kernel
      have hl : raw18089step1Labels = raw18089step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18089step0 raw18089step0Labels permutation137 permutation7
    mixedMoment B raw18089step1 raw18089step1Labels = mixedMoment B raw18089step2 raw18089step2Labels := by
      have ha : raw18089step2 = raw18089step1 := by apply Matrix.ext; unfold raw18089step2 raw18089step1; decide +kernel
      have hl : raw18089step1Labels = labelEmbedding1 ∘ raw18089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18089step1 raw18089step1Labels raw18089step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw18090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18090step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18090 raw18090Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw18090 raw18090Labels = mixedMoment B raw18090step0 raw18090step0Labels := by
      have hz : ∀ j, raw18090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18090step0 = (fun i j => raw18090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18090step0 raw18090; decide +kernel
      have hl : raw18090step0Labels = raw18090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18090 raw18090Labels permutation346 hz
    mixedMoment B raw18090step0 raw18090step0Labels = mixedMoment B raw18090step1 raw18090step1Labels := by
      have ha : raw18090step1 = (fun i j => raw18090step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18090step1 raw18090step0; decide +kernel
      have hl : raw18090step1Labels = raw18090step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18090step0 raw18090step0Labels permutation137 permutation7
    mixedMoment B raw18090step1 raw18090step1Labels = mixedMoment B raw18090step2 raw18090step2Labels := by
      have ha : raw18090step2 = raw18090step1 := by apply Matrix.ext; unfold raw18090step2 raw18090step1; decide +kernel
      have hl : raw18090step1Labels = labelEmbedding1 ∘ raw18090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18090step1 raw18090step1Labels raw18090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw18091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18091step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18091step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18091step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18091 raw18091Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw18091 raw18091Labels = mixedMoment B raw18091step0 raw18091step0Labels := by
      have hz : ∀ j, raw18091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18091step0 = (fun i j => raw18091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18091step0 raw18091; decide +kernel
      have hl : raw18091step0Labels = raw18091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18091 raw18091Labels permutation434 hz
    mixedMoment B raw18091step0 raw18091step0Labels = mixedMoment B raw18091step1 raw18091step1Labels := by
      have hz : ∀ j, raw18091step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18091step1 = (fun i j => raw18091step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18091step1 raw18091step0; decide +kernel
      have hl : raw18091step1Labels = raw18091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18091step0 raw18091step0Labels permutation80 hz
    mixedMoment B raw18091step1 raw18091step1Labels = mixedMoment B raw18091step2 raw18091step2Labels := by
      have ha : raw18091step2 = (fun i j => raw18091step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18091step2 raw18091step1; decide +kernel
      have hl : raw18091step2Labels = raw18091step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18091step1 raw18091step1Labels permutation29 permutation7
    mixedMoment B raw18091step2 raw18091step2Labels = mixedMoment B raw18091step3 raw18091step3Labels := by
      have ha : raw18091step3 = raw18091step2 := by apply Matrix.ext; unfold raw18091step3 raw18091step2; decide +kernel
      have hl : raw18091step2Labels = labelEmbedding1 ∘ raw18091step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18091step2 raw18091step2Labels raw18091step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw18092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18092step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2]]
def raw18092step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18092step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18092step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18092step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18092 raw18092Labels = mixedMoment B node4004 node4004Labels := by
  calc
    mixedMoment B raw18092 raw18092Labels = mixedMoment B raw18092step0 raw18092step0Labels := by
      have hz : ∀ j, raw18092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18092step0 = (fun i j => raw18092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18092step0 raw18092; decide +kernel
      have hl : raw18092step0Labels = raw18092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18092 raw18092Labels permutation434 hz
    mixedMoment B raw18092step0 raw18092step0Labels = mixedMoment B raw18092step1 raw18092step1Labels := by
      have hz : ∀ j, raw18092step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18092step1 = (fun i j => raw18092step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18092step1 raw18092step0; decide +kernel
      have hl : raw18092step1Labels = raw18092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18092step0 raw18092step0Labels permutation80 hz
    mixedMoment B raw18092step1 raw18092step1Labels = mixedMoment B raw18092step2 raw18092step2Labels := by
      have ha : raw18092step2 = (fun i j => raw18092step1 (permutation21 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18092step2 raw18092step1; decide +kernel
      have hl : raw18092step2Labels = raw18092step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18092step1 raw18092step1Labels permutation21 permutation5
    mixedMoment B raw18092step2 raw18092step2Labels = mixedMoment B raw18092step3 raw18092step3Labels := by
      have ha : raw18092step3 = raw18092step2 := by apply Matrix.ext; unfold raw18092step3 raw18092step2; decide +kernel
      have hl : raw18092step2Labels = labelEmbedding1 ∘ raw18092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18092step2 raw18092step2Labels raw18092step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4004 node4004Labels := by rfl

def raw18093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18093step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18093step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18093 raw18093Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw18093 raw18093Labels = mixedMoment B raw18093step0 raw18093step0Labels := by
      have hz : ∀ j, raw18093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18093step0 = (fun i j => raw18093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18093step0 raw18093; decide +kernel
      have hl : raw18093step0Labels = raw18093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18093 raw18093Labels permutation434 hz
    mixedMoment B raw18093step0 raw18093step0Labels = mixedMoment B raw18093step1 raw18093step1Labels := by
      have ha : raw18093step1 = (fun i j => raw18093step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18093step1 raw18093step0; decide +kernel
      have hl : raw18093step1Labels = raw18093step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18093step0 raw18093step0Labels permutation60 permutation5
    mixedMoment B raw18093step1 raw18093step1Labels = mixedMoment B raw18093step2 raw18093step2Labels := by
      have ha : raw18093step2 = -raw18093step1 := by apply Matrix.ext; change ∀ i j, raw18093step2 i j = -(raw18093step1 i j); unfold raw18093step2 raw18093step1; decide +kernel
      have hl : raw18093step2Labels = raw18093step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18093step2 raw18093step2Labels = mixedMoment B raw18093step3 raw18093step3Labels := by
      have ha : raw18093step3 = raw18093step2 := by apply Matrix.ext; unfold raw18093step3 raw18093step2; decide +kernel
      have hl : raw18093step2Labels = labelEmbedding1 ∘ raw18093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18093step2 raw18093step2Labels raw18093step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw18094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18094 raw18094Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw18094 raw18094Labels = mixedMoment B raw18094step0 raw18094step0Labels := by
      have ha : raw18094step0 = (fun i j => raw18094 (permutation609 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18094step0 raw18094; decide +kernel
      have hl : raw18094step0Labels = raw18094Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18094 raw18094Labels permutation609 permutation7
    mixedMoment B raw18094step0 raw18094step0Labels = mixedMoment B raw18094step1 raw18094step1Labels := by
      have ha : raw18094step1 = raw18094step0 := by apply Matrix.ext; unfold raw18094step1 raw18094step0; decide +kernel
      have hl : raw18094step0Labels = labelEmbedding1 ∘ raw18094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18094step0 raw18094step0Labels raw18094step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3870 node3870Labels := by rfl

def raw18095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18095step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18095step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18095step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18095 raw18095Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw18095 raw18095Labels = mixedMoment B raw18095step0 raw18095step0Labels := by
      have hz : ∀ j, raw18095 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18095step0 = (fun i j => raw18095 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18095step0 raw18095; decide +kernel
      have hl : raw18095step0Labels = raw18095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18095 raw18095Labels permutation434 hz
    mixedMoment B raw18095step0 raw18095step0Labels = mixedMoment B raw18095step1 raw18095step1Labels := by
      have ha : raw18095step1 = (fun i j => raw18095step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18095step1 raw18095step0; decide +kernel
      have hl : raw18095step1Labels = raw18095step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18095step0 raw18095step0Labels permutation46 permutation7
    mixedMoment B raw18095step1 raw18095step1Labels = mixedMoment B raw18095step2 raw18095step2Labels := by
      have ha : raw18095step2 = -raw18095step1 := by apply Matrix.ext; change ∀ i j, raw18095step2 i j = -(raw18095step1 i j); unfold raw18095step2 raw18095step1; decide +kernel
      have hl : raw18095step2Labels = raw18095step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18095step2 raw18095step2Labels = mixedMoment B raw18095step3 raw18095step3Labels := by
      have ha : raw18095step3 = raw18095step2 := by apply Matrix.ext; unfold raw18095step3 raw18095step2; decide +kernel
      have hl : raw18095step2Labels = labelEmbedding1 ∘ raw18095step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18095step2 raw18095step2Labels raw18095step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw18096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18096step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18096step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18096step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18096 raw18096Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw18096 raw18096Labels = mixedMoment B raw18096step0 raw18096step0Labels := by
      have hz : ∀ j, raw18096 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18096step0 = (fun i j => raw18096 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18096step0 raw18096; decide +kernel
      have hl : raw18096step0Labels = raw18096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18096 raw18096Labels permutation434 hz
    mixedMoment B raw18096step0 raw18096step0Labels = mixedMoment B raw18096step1 raw18096step1Labels := by
      have ha : raw18096step1 = (fun i j => raw18096step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18096step1 raw18096step0; decide +kernel
      have hl : raw18096step1Labels = raw18096step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18096step0 raw18096step0Labels permutation46 permutation7
    mixedMoment B raw18096step1 raw18096step1Labels = mixedMoment B raw18096step2 raw18096step2Labels := by
      have ha : raw18096step2 = -raw18096step1 := by apply Matrix.ext; change ∀ i j, raw18096step2 i j = -(raw18096step1 i j); unfold raw18096step2 raw18096step1; decide +kernel
      have hl : raw18096step2Labels = raw18096step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18096step2 raw18096step2Labels = mixedMoment B raw18096step3 raw18096step3Labels := by
      have ha : raw18096step3 = raw18096step2 := by apply Matrix.ext; unfold raw18096step3 raw18096step2; decide +kernel
      have hl : raw18096step2Labels = labelEmbedding1 ∘ raw18096step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18096step2 raw18096step2Labels raw18096step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw18097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18097step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18097step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18097step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18097 raw18097Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw18097 raw18097Labels = mixedMoment B raw18097step0 raw18097step0Labels := by
      have hz : ∀ j, raw18097 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18097step0 = (fun i j => raw18097 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18097step0 raw18097; decide +kernel
      have hl : raw18097step0Labels = raw18097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18097 raw18097Labels permutation346 hz
    mixedMoment B raw18097step0 raw18097step0Labels = mixedMoment B raw18097step1 raw18097step1Labels := by
      have ha : raw18097step1 = (fun i j => raw18097step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18097step1 raw18097step0; decide +kernel
      have hl : raw18097step1Labels = raw18097step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18097step0 raw18097step0Labels permutation60 permutation5
    mixedMoment B raw18097step1 raw18097step1Labels = mixedMoment B raw18097step2 raw18097step2Labels := by
      have ha : raw18097step2 = -raw18097step1 := by apply Matrix.ext; change ∀ i j, raw18097step2 i j = -(raw18097step1 i j); unfold raw18097step2 raw18097step1; decide +kernel
      have hl : raw18097step2Labels = raw18097step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18097step2 raw18097step2Labels = mixedMoment B raw18097step3 raw18097step3Labels := by
      have ha : raw18097step3 = raw18097step2 := by apply Matrix.ext; unfold raw18097step3 raw18097step2; decide +kernel
      have hl : raw18097step2Labels = labelEmbedding1 ∘ raw18097step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18097step2 raw18097step2Labels raw18097step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw18098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18098 raw18098Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw18098 raw18098Labels = mixedMoment B raw18098step0 raw18098step0Labels := by
      have ha : raw18098step0 = (fun i j => raw18098 (permutation614 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18098step0 raw18098; decide +kernel
      have hl : raw18098step0Labels = raw18098Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18098 raw18098Labels permutation614 permutation7
    mixedMoment B raw18098step0 raw18098step0Labels = mixedMoment B raw18098step1 raw18098step1Labels := by
      have ha : raw18098step1 = raw18098step0 := by apply Matrix.ext; unfold raw18098step1 raw18098step0; decide +kernel
      have hl : raw18098step0Labels = labelEmbedding1 ∘ raw18098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18098step0 raw18098step0Labels raw18098step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3870 node3870Labels := by rfl

def raw18099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18099step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18099step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18099step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18099 raw18099Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw18099 raw18099Labels = mixedMoment B raw18099step0 raw18099step0Labels := by
      have hz : ∀ j, raw18099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18099step0 = (fun i j => raw18099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18099step0 raw18099; decide +kernel
      have hl : raw18099step0Labels = raw18099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18099 raw18099Labels permutation346 hz
    mixedMoment B raw18099step0 raw18099step0Labels = mixedMoment B raw18099step1 raw18099step1Labels := by
      have ha : raw18099step1 = (fun i j => raw18099step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18099step1 raw18099step0; decide +kernel
      have hl : raw18099step1Labels = raw18099step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18099step0 raw18099step0Labels permutation46 permutation7
    mixedMoment B raw18099step1 raw18099step1Labels = mixedMoment B raw18099step2 raw18099step2Labels := by
      have ha : raw18099step2 = -raw18099step1 := by apply Matrix.ext; change ∀ i j, raw18099step2 i j = -(raw18099step1 i j); unfold raw18099step2 raw18099step1; decide +kernel
      have hl : raw18099step2Labels = raw18099step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18099step2 raw18099step2Labels = mixedMoment B raw18099step3 raw18099step3Labels := by
      have ha : raw18099step3 = raw18099step2 := by apply Matrix.ext; unfold raw18099step3 raw18099step2; decide +kernel
      have hl : raw18099step2Labels = labelEmbedding1 ∘ raw18099step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18099step2 raw18099step2Labels raw18099step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw18100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw18100step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18100step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18100step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18100 raw18100Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw18100 raw18100Labels = mixedMoment B raw18100step0 raw18100step0Labels := by
      have hz : ∀ j, raw18100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18100step0 = (fun i j => raw18100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18100step0 raw18100; decide +kernel
      have hl : raw18100step0Labels = raw18100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18100 raw18100Labels permutation346 hz
    mixedMoment B raw18100step0 raw18100step0Labels = mixedMoment B raw18100step1 raw18100step1Labels := by
      have ha : raw18100step1 = (fun i j => raw18100step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18100step1 raw18100step0; decide +kernel
      have hl : raw18100step1Labels = raw18100step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18100step0 raw18100step0Labels permutation46 permutation7
    mixedMoment B raw18100step1 raw18100step1Labels = mixedMoment B raw18100step2 raw18100step2Labels := by
      have ha : raw18100step2 = -raw18100step1 := by apply Matrix.ext; change ∀ i j, raw18100step2 i j = -(raw18100step1 i j); unfold raw18100step2 raw18100step1; decide +kernel
      have hl : raw18100step2Labels = raw18100step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18100step2 raw18100step2Labels = mixedMoment B raw18100step3 raw18100step3Labels := by
      have ha : raw18100step3 = raw18100step2 := by apply Matrix.ext; unfold raw18100step3 raw18100step2; decide +kernel
      have hl : raw18100step2Labels = labelEmbedding1 ∘ raw18100step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18100step2 raw18100step2Labels raw18100step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw18101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18101step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18101step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18101step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18101step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw18101step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18101 raw18101Labels = mixedMoment B node2680 node2680Labels := by
  calc
    mixedMoment B raw18101 raw18101Labels = mixedMoment B raw18101step0 raw18101step0Labels := by
      have hz : ∀ j, raw18101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18101step0 = (fun i j => raw18101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18101step0 raw18101; decide +kernel
      have hl : raw18101step0Labels = raw18101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18101 raw18101Labels permutation434 hz
    mixedMoment B raw18101step0 raw18101step0Labels = mixedMoment B raw18101step1 raw18101step1Labels := by
      have hz : ∀ j, raw18101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18101step1 = (fun i j => raw18101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18101step1 raw18101step0; decide +kernel
      have hl : raw18101step1Labels = raw18101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18101step0 raw18101step0Labels permutation80 hz
    mixedMoment B raw18101step1 raw18101step1Labels = mixedMoment B raw18101step2 raw18101step2Labels := by
      have ha : raw18101step2 = (fun i j => raw18101step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18101step2 raw18101step1; decide +kernel
      have hl : raw18101step2Labels = raw18101step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18101step1 raw18101step1Labels permutation24 permutation5
    mixedMoment B raw18101step2 raw18101step2Labels = mixedMoment B raw18101step3 raw18101step3Labels := by
      have ha : raw18101step3 = raw18101step2 := by apply Matrix.ext; unfold raw18101step3 raw18101step2; decide +kernel
      have hl : raw18101step2Labels = labelEmbedding1 ∘ raw18101step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18101step2 raw18101step2Labels raw18101step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2680 node2680Labels := by rfl

def raw18102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18102step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18102step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18102 raw18102Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw18102 raw18102Labels = mixedMoment B raw18102step0 raw18102step0Labels := by
      have hz : ∀ j, raw18102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18102step0 = (fun i j => raw18102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18102step0 raw18102; decide +kernel
      have hl : raw18102step0Labels = raw18102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18102 raw18102Labels permutation434 hz
    mixedMoment B raw18102step0 raw18102step0Labels = mixedMoment B raw18102step1 raw18102step1Labels := by
      have ha : raw18102step1 = (fun i j => raw18102step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18102step1 raw18102step0; decide +kernel
      have hl : raw18102step1Labels = raw18102step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18102step0 raw18102step0Labels permutation123 permutation5
    mixedMoment B raw18102step1 raw18102step1Labels = mixedMoment B raw18102step2 raw18102step2Labels := by
      have ha : raw18102step2 = raw18102step1 := by apply Matrix.ext; unfold raw18102step2 raw18102step1; decide +kernel
      have hl : raw18102step1Labels = labelEmbedding1 ∘ raw18102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18102step1 raw18102step1Labels raw18102step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw18103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw18103step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18103 raw18103Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw18103 raw18103Labels = mixedMoment B raw18103step0 raw18103step0Labels := by
      have hz : ∀ j, raw18103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18103step0 = (fun i j => raw18103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18103step0 raw18103; decide +kernel
      have hl : raw18103step0Labels = raw18103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18103 raw18103Labels permutation346 hz
    mixedMoment B raw18103step0 raw18103step0Labels = mixedMoment B raw18103step1 raw18103step1Labels := by
      have ha : raw18103step1 = (fun i j => raw18103step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18103step1 raw18103step0; decide +kernel
      have hl : raw18103step1Labels = raw18103step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18103step0 raw18103step0Labels permutation123 permutation5
    mixedMoment B raw18103step1 raw18103step1Labels = mixedMoment B raw18103step2 raw18103step2Labels := by
      have ha : raw18103step2 = raw18103step1 := by apply Matrix.ext; unfold raw18103step2 raw18103step1; decide +kernel
      have hl : raw18103step1Labels = labelEmbedding1 ∘ raw18103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18103step1 raw18103step1Labels raw18103step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw18104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw18104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -3, 1], ![1, 1, -2]]
def raw18104step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18104step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18104step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18104step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18104 raw18104Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw18104 raw18104Labels = mixedMoment B raw18104step0 raw18104step0Labels := by
      have hz : ∀ j, raw18104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18104step0 = (fun i j => raw18104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18104step0 raw18104; decide +kernel
      have hl : raw18104step0Labels = raw18104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18104 raw18104Labels permutation434 hz
    mixedMoment B raw18104step0 raw18104step0Labels = mixedMoment B raw18104step1 raw18104step1Labels := by
      have hz : ∀ j, raw18104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18104step1 = (fun i j => raw18104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18104step1 raw18104step0; decide +kernel
      have hl : raw18104step1Labels = raw18104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18104step0 raw18104step0Labels permutation80 hz
    mixedMoment B raw18104step1 raw18104step1Labels = mixedMoment B raw18104step2 raw18104step2Labels := by
      have ha : raw18104step2 = (fun i j => raw18104step1 (permutation21 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18104step2 raw18104step1; decide +kernel
      have hl : raw18104step2Labels = raw18104step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18104step1 raw18104step1Labels permutation21 permutation5
    mixedMoment B raw18104step2 raw18104step2Labels = mixedMoment B raw18104step3 raw18104step3Labels := by
      have ha : raw18104step3 = raw18104step2 := by apply Matrix.ext; unfold raw18104step3 raw18104step2; decide +kernel
      have hl : raw18104step2Labels = labelEmbedding1 ∘ raw18104step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18104step2 raw18104step2Labels raw18104step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw18105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18105step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![3, -1, -2]]
def raw18105step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -2, 3], ![-2, 1, 1]]
def raw18105step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw18105step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18105step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw18105step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18105 raw18105Labels = mixedMoment B node2687 node2687Labels := by
  calc
    mixedMoment B raw18105 raw18105Labels = mixedMoment B raw18105step0 raw18105step0Labels := by
      have hz : ∀ j, raw18105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18105step0 = (fun i j => raw18105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18105step0 raw18105; decide +kernel
      have hl : raw18105step0Labels = raw18105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18105 raw18105Labels permutation434 hz
    mixedMoment B raw18105step0 raw18105step0Labels = mixedMoment B raw18105step1 raw18105step1Labels := by
      have hz : ∀ j, raw18105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18105step1 = (fun i j => raw18105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18105step1 raw18105step0; decide +kernel
      have hl : raw18105step1Labels = raw18105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18105step0 raw18105step0Labels permutation80 hz
    mixedMoment B raw18105step1 raw18105step1Labels = mixedMoment B raw18105step2 raw18105step2Labels := by
      have ha : raw18105step2 = (fun i j => raw18105step1 (permutation15 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18105step2 raw18105step1; decide +kernel
      have hl : raw18105step2Labels = raw18105step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18105step1 raw18105step1Labels permutation15 permutation5
    mixedMoment B raw18105step2 raw18105step2Labels = mixedMoment B raw18105step3 raw18105step3Labels := by
      have ha : raw18105step3 = -raw18105step2 := by apply Matrix.ext; change ∀ i j, raw18105step3 i j = -(raw18105step2 i j); unfold raw18105step3 raw18105step2; decide +kernel
      have hl : raw18105step3Labels = raw18105step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18105step3 raw18105step3Labels = mixedMoment B raw18105step4 raw18105step4Labels := by
      have ha : raw18105step4 = raw18105step3 := by apply Matrix.ext; unfold raw18105step4 raw18105step3; decide +kernel
      have hl : raw18105step3Labels = labelEmbedding1 ∘ raw18105step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18105step3 raw18105step3Labels raw18105step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2687 node2687Labels := by rfl

def raw18106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18106 raw18106Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw18106 raw18106Labels = mixedMoment B raw18106step0 raw18106step0Labels := by
      have hz : ∀ j, raw18106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18106step0 = (fun i j => raw18106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18106step0 raw18106; decide +kernel
      have hl : raw18106step0Labels = raw18106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18106 raw18106Labels permutation434 hz
    mixedMoment B raw18106step0 raw18106step0Labels = mixedMoment B raw18106step1 raw18106step1Labels := by
      have ha : raw18106step1 = (fun i j => raw18106step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18106step1 raw18106step0; decide +kernel
      have hl : raw18106step1Labels = raw18106step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18106step0 raw18106step0Labels permutation137 permutation7
    mixedMoment B raw18106step1 raw18106step1Labels = mixedMoment B raw18106step2 raw18106step2Labels := by
      have ha : raw18106step2 = raw18106step1 := by apply Matrix.ext; unfold raw18106step2 raw18106step1; decide +kernel
      have hl : raw18106step1Labels = labelEmbedding1 ∘ raw18106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18106step1 raw18106step1Labels raw18106step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw18107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw18107step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18107step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18107 raw18107Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw18107 raw18107Labels = mixedMoment B raw18107step0 raw18107step0Labels := by
      have hz : ∀ j, raw18107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18107step0 = (fun i j => raw18107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18107step0 raw18107; decide +kernel
      have hl : raw18107step0Labels = raw18107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18107 raw18107Labels permutation346 hz
    mixedMoment B raw18107step0 raw18107step0Labels = mixedMoment B raw18107step1 raw18107step1Labels := by
      have ha : raw18107step1 = (fun i j => raw18107step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18107step1 raw18107step0; decide +kernel
      have hl : raw18107step1Labels = raw18107step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18107step0 raw18107step0Labels permutation137 permutation7
    mixedMoment B raw18107step1 raw18107step1Labels = mixedMoment B raw18107step2 raw18107step2Labels := by
      have ha : raw18107step2 = raw18107step1 := by apply Matrix.ext; unfold raw18107step2 raw18107step1; decide +kernel
      have hl : raw18107step1Labels = labelEmbedding1 ∘ raw18107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18107step1 raw18107step1Labels raw18107step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw18108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18108step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18108step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18108 raw18108Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw18108 raw18108Labels = mixedMoment B raw18108step0 raw18108step0Labels := by
      have hz : ∀ j, raw18108 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18108step0 = (fun i j => raw18108 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18108step0 raw18108; decide +kernel
      have hl : raw18108step0Labels = raw18108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18108 raw18108Labels permutation434 hz
    mixedMoment B raw18108step0 raw18108step0Labels = mixedMoment B raw18108step1 raw18108step1Labels := by
      have hz : ∀ j, raw18108step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18108step1 = (fun i j => raw18108step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18108step1 raw18108step0; decide +kernel
      have hl : raw18108step1Labels = raw18108step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18108step0 raw18108step0Labels permutation80 hz
    mixedMoment B raw18108step1 raw18108step1Labels = mixedMoment B raw18108step2 raw18108step2Labels := by
      have ha : raw18108step2 = (fun i j => raw18108step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18108step2 raw18108step1; decide +kernel
      have hl : raw18108step2Labels = raw18108step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18108step1 raw18108step1Labels permutation14 permutation2
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw18109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18109step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18109step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18109step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18109step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18109 raw18109Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw18109 raw18109Labels = mixedMoment B raw18109step0 raw18109step0Labels := by
      have hz : ∀ j, raw18109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18109step0 = (fun i j => raw18109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18109step0 raw18109; decide +kernel
      have hl : raw18109step0Labels = raw18109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18109 raw18109Labels permutation434 hz
    mixedMoment B raw18109step0 raw18109step0Labels = mixedMoment B raw18109step1 raw18109step1Labels := by
      have ha : raw18109step1 = (fun i j => raw18109step0 (permutation148 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18109step1 raw18109step0; decide +kernel
      have hl : raw18109step1Labels = raw18109step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18109step0 raw18109step0Labels permutation148 permutation3
    mixedMoment B raw18109step1 raw18109step1Labels = mixedMoment B raw18109step2 raw18109step2Labels := by
      have ha : raw18109step2 = -raw18109step1 := by apply Matrix.ext; change ∀ i j, raw18109step2 i j = -(raw18109step1 i j); unfold raw18109step2 raw18109step1; decide +kernel
      have hl : raw18109step2Labels = raw18109step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18109step2 raw18109step2Labels = mixedMoment B raw18109step3 raw18109step3Labels := by
      have ha : raw18109step3 = raw18109step2 := by apply Matrix.ext; unfold raw18109step3 raw18109step2; decide +kernel
      have hl : raw18109step2Labels = labelEmbedding6 ∘ raw18109step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18109step2 raw18109step2Labels raw18109step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw18110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18110step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18110step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18110step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18110step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18110 raw18110Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw18110 raw18110Labels = mixedMoment B raw18110step0 raw18110step0Labels := by
      have hz : ∀ j, raw18110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18110step0 = (fun i j => raw18110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18110step0 raw18110; decide +kernel
      have hl : raw18110step0Labels = raw18110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18110 raw18110Labels permutation346 hz
    mixedMoment B raw18110step0 raw18110step0Labels = mixedMoment B raw18110step1 raw18110step1Labels := by
      have ha : raw18110step1 = (fun i j => raw18110step0 (permutation148 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18110step1 raw18110step0; decide +kernel
      have hl : raw18110step1Labels = raw18110step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18110step0 raw18110step0Labels permutation148 permutation3
    mixedMoment B raw18110step1 raw18110step1Labels = mixedMoment B raw18110step2 raw18110step2Labels := by
      have ha : raw18110step2 = -raw18110step1 := by apply Matrix.ext; change ∀ i j, raw18110step2 i j = -(raw18110step1 i j); unfold raw18110step2 raw18110step1; decide +kernel
      have hl : raw18110step2Labels = raw18110step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18110step2 raw18110step2Labels = mixedMoment B raw18110step3 raw18110step3Labels := by
      have ha : raw18110step3 = raw18110step2 := by apply Matrix.ext; unfold raw18110step3 raw18110step2; decide +kernel
      have hl : raw18110step2Labels = labelEmbedding6 ∘ raw18110step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18110step2 raw18110step2Labels raw18110step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw18111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0]]
def raw18111step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw18111step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18111step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18111step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18111step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18111step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18111 raw18111Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw18111 raw18111Labels = mixedMoment B raw18111step0 raw18111step0Labels := by
      have hz : ∀ j, raw18111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18111step0 = (fun i j => raw18111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18111step0 raw18111; decide +kernel
      have hl : raw18111step0Labels = raw18111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18111 raw18111Labels permutation434 hz
    mixedMoment B raw18111step0 raw18111step0Labels = mixedMoment B raw18111step1 raw18111step1Labels := by
      have hz : ∀ j, raw18111step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18111step1 = (fun i j => raw18111step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18111step1 raw18111step0; decide +kernel
      have hl : raw18111step1Labels = raw18111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18111step0 raw18111step0Labels permutation80 hz
    mixedMoment B raw18111step1 raw18111step1Labels = mixedMoment B raw18111step2 raw18111step2Labels := by
      have ha : raw18111step2 = (fun i j => raw18111step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18111step2 raw18111step1; decide +kernel
      have hl : raw18111step2Labels = raw18111step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18111step1 raw18111step1Labels permutation20 permutation4
    mixedMoment B raw18111step2 raw18111step2Labels = mixedMoment B raw18111step3 raw18111step3Labels := by
      have ha : raw18111step3 = -raw18111step2 := by apply Matrix.ext; change ∀ i j, raw18111step3 i j = -(raw18111step2 i j); unfold raw18111step3 raw18111step2; decide +kernel
      have hl : raw18111step3Labels = raw18111step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18111step3 raw18111step3Labels = mixedMoment B raw18111step4 raw18111step4Labels := by
      have ha : raw18111step4 = raw18111step3 := by apply Matrix.ext; unfold raw18111step4 raw18111step3; decide +kernel
      have hl : raw18111step3Labels = labelEmbedding7 ∘ raw18111step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18111step3 raw18111step3Labels raw18111step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw18112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0]]
def raw18112step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18112step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18112step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18112step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18112 raw18112Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw18112 raw18112Labels = mixedMoment B raw18112step0 raw18112step0Labels := by
      have hz : ∀ j, raw18112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18112step0 = (fun i j => raw18112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18112step0 raw18112; decide +kernel
      have hl : raw18112step0Labels = raw18112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18112 raw18112Labels permutation434 hz
    mixedMoment B raw18112step0 raw18112step0Labels = mixedMoment B raw18112step1 raw18112step1Labels := by
      have hz : ∀ j, raw18112step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18112step1 = (fun i j => raw18112step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18112step1 raw18112step0; decide +kernel
      have hl : raw18112step1Labels = raw18112step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18112step0 raw18112step0Labels permutation80 hz
    mixedMoment B raw18112step1 raw18112step1Labels = mixedMoment B raw18112step2 raw18112step2Labels := by
      have ha : raw18112step2 = (fun i j => raw18112step1 (permutation21 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18112step2 raw18112step1; decide +kernel
      have hl : raw18112step2Labels = raw18112step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18112step1 raw18112step1Labels permutation21 permutation6
    mixedMoment B raw18112step2 raw18112step2Labels = mixedMoment B raw18112step3 raw18112step3Labels := by
      have ha : raw18112step3 = raw18112step2 := by apply Matrix.ext; unfold raw18112step3 raw18112step2; decide +kernel
      have hl : raw18112step2Labels = labelEmbedding9 ∘ raw18112step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18112step2 raw18112step2Labels raw18112step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw18113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 1, -2], ![2, -2, 0]]
def raw18113step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18113step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18113step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18113step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18113step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18113 raw18113Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw18113 raw18113Labels = mixedMoment B raw18113step0 raw18113step0Labels := by
      have hz : ∀ j, raw18113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18113step0 = (fun i j => raw18113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18113step0 raw18113; decide +kernel
      have hl : raw18113step0Labels = raw18113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18113 raw18113Labels permutation434 hz
    mixedMoment B raw18113step0 raw18113step0Labels = mixedMoment B raw18113step1 raw18113step1Labels := by
      have hz : ∀ j, raw18113step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18113step1 = (fun i j => raw18113step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18113step1 raw18113step0; decide +kernel
      have hl : raw18113step1Labels = raw18113step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18113step0 raw18113step0Labels permutation80 hz
    mixedMoment B raw18113step1 raw18113step1Labels = mixedMoment B raw18113step2 raw18113step2Labels := by
      have ha : raw18113step2 = (fun i j => raw18113step1 (permutation10 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18113step2 raw18113step1; decide +kernel
      have hl : raw18113step2Labels = raw18113step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18113step1 raw18113step1Labels permutation10 permutation5
    mixedMoment B raw18113step2 raw18113step2Labels = mixedMoment B raw18113step3 raw18113step3Labels := by
      have ha : raw18113step3 = -raw18113step2 := by apply Matrix.ext; change ∀ i j, raw18113step3 i j = -(raw18113step2 i j); unfold raw18113step3 raw18113step2; decide +kernel
      have hl : raw18113step3Labels = raw18113step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18113step3 raw18113step3Labels = mixedMoment B raw18113step4 raw18113step4Labels := by
      have ha : raw18113step4 = raw18113step3 := by apply Matrix.ext; unfold raw18113step4 raw18113step3; decide +kernel
      have hl : raw18113step3Labels = labelEmbedding8 ∘ raw18113step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18113step3 raw18113step3Labels raw18113step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw18114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18114step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18114step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18114 raw18114Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18114 raw18114Labels = mixedMoment B raw18114step0 raw18114step0Labels := by
      have hz : ∀ j, raw18114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18114step0 = (fun i j => raw18114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18114step0 raw18114; decide +kernel
      have hl : raw18114step0Labels = raw18114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18114 raw18114Labels permutation434 hz
    mixedMoment B raw18114step0 raw18114step0Labels = mixedMoment B raw18114step1 raw18114step1Labels := by
      have ha : raw18114step1 = (fun i j => raw18114step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18114step1 raw18114step0; decide +kernel
      have hl : raw18114step1Labels = raw18114step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18114step0 raw18114step0Labels permutation139 permutation5
    mixedMoment B raw18114step1 raw18114step1Labels = mixedMoment B raw18114step2 raw18114step2Labels := by
      have ha : raw18114step2 = raw18114step1 := by apply Matrix.ext; unfold raw18114step2 raw18114step1; decide +kernel
      have hl : raw18114step1Labels = labelEmbedding8 ∘ raw18114step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18114step1 raw18114step1Labels raw18114step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18115step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18115step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18115 raw18115Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18115 raw18115Labels = mixedMoment B raw18115step0 raw18115step0Labels := by
      have hz : ∀ j, raw18115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18115step0 = (fun i j => raw18115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18115step0 raw18115; decide +kernel
      have hl : raw18115step0Labels = raw18115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18115 raw18115Labels permutation346 hz
    mixedMoment B raw18115step0 raw18115step0Labels = mixedMoment B raw18115step1 raw18115step1Labels := by
      have ha : raw18115step1 = (fun i j => raw18115step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18115step1 raw18115step0; decide +kernel
      have hl : raw18115step1Labels = raw18115step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18115step0 raw18115step0Labels permutation139 permutation5
    mixedMoment B raw18115step1 raw18115step1Labels = mixedMoment B raw18115step2 raw18115step2Labels := by
      have ha : raw18115step2 = raw18115step1 := by apply Matrix.ext; unfold raw18115step2 raw18115step1; decide +kernel
      have hl : raw18115step1Labels = labelEmbedding8 ∘ raw18115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18115step1 raw18115step1Labels raw18115step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 2, -2], ![2, -2, 0]]
def raw18116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18116step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18116step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18116step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18116 raw18116Labels = mixedMoment B node5389 node5389Labels := by
  calc
    mixedMoment B raw18116 raw18116Labels = mixedMoment B raw18116step0 raw18116step0Labels := by
      have hz : ∀ j, raw18116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18116step0 = (fun i j => raw18116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18116step0 raw18116; decide +kernel
      have hl : raw18116step0Labels = raw18116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18116 raw18116Labels permutation434 hz
    mixedMoment B raw18116step0 raw18116step0Labels = mixedMoment B raw18116step1 raw18116step1Labels := by
      have hz : ∀ j, raw18116step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18116step1 = (fun i j => raw18116step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18116step1 raw18116step0; decide +kernel
      have hl : raw18116step1Labels = raw18116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18116step0 raw18116step0Labels permutation80 hz
    mixedMoment B raw18116step1 raw18116step1Labels = mixedMoment B raw18116step2 raw18116step2Labels := by
      have ha : raw18116step2 = (fun i j => raw18116step1 (permutation18 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18116step2 raw18116step1; decide +kernel
      have hl : raw18116step2Labels = raw18116step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18116step1 raw18116step1Labels permutation18 permutation4
    mixedMoment B raw18116step2 raw18116step2Labels = mixedMoment B raw18116step3 raw18116step3Labels := by
      have ha : raw18116step3 = raw18116step2 := by apply Matrix.ext; unfold raw18116step3 raw18116step2; decide +kernel
      have hl : raw18116step2Labels = labelEmbedding7 ∘ raw18116step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18116step2 raw18116step2Labels raw18116step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5389 node5389Labels := by rfl

def raw18117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 1, -2], ![1, -1, 0]]
def raw18117step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18117step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18117step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18117step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18117step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18117 raw18117Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw18117 raw18117Labels = mixedMoment B raw18117step0 raw18117step0Labels := by
      have hz : ∀ j, raw18117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18117step0 = (fun i j => raw18117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18117step0 raw18117; decide +kernel
      have hl : raw18117step0Labels = raw18117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18117 raw18117Labels permutation434 hz
    mixedMoment B raw18117step0 raw18117step0Labels = mixedMoment B raw18117step1 raw18117step1Labels := by
      have hz : ∀ j, raw18117step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18117step1 = (fun i j => raw18117step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18117step1 raw18117step0; decide +kernel
      have hl : raw18117step1Labels = raw18117step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18117step0 raw18117step0Labels permutation80 hz
    mixedMoment B raw18117step1 raw18117step1Labels = mixedMoment B raw18117step2 raw18117step2Labels := by
      have ha : raw18117step2 = (fun i j => raw18117step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18117step2 raw18117step1; decide +kernel
      have hl : raw18117step2Labels = raw18117step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18117step1 raw18117step1Labels permutation19 permutation4
    mixedMoment B raw18117step2 raw18117step2Labels = mixedMoment B raw18117step3 raw18117step3Labels := by
      have ha : raw18117step3 = raw18117step2 := by apply Matrix.ext; unfold raw18117step3 raw18117step2; decide +kernel
      have hl : raw18117step2Labels = labelEmbedding7 ∘ raw18117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18117step2 raw18117step2Labels raw18117step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw18118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18118step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18118step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18118 raw18118Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw18118 raw18118Labels = mixedMoment B raw18118step0 raw18118step0Labels := by
      have hz : ∀ j, raw18118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18118step0 = (fun i j => raw18118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18118step0 raw18118; decide +kernel
      have hl : raw18118step0Labels = raw18118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18118 raw18118Labels permutation434 hz
    mixedMoment B raw18118step0 raw18118step0Labels = mixedMoment B raw18118step1 raw18118step1Labels := by
      have ha : raw18118step1 = (fun i j => raw18118step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18118step1 raw18118step0; decide +kernel
      have hl : raw18118step1Labels = raw18118step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18118step0 raw18118step0Labels permutation34 permutation3
    mixedMoment B raw18118step1 raw18118step1Labels = mixedMoment B raw18118step2 raw18118step2Labels := by
      have ha : raw18118step2 = raw18118step1 := by apply Matrix.ext; unfold raw18118step2 raw18118step1; decide +kernel
      have hl : raw18118step1Labels = labelEmbedding6 ∘ raw18118step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18118step1 raw18118step1Labels raw18118step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

def raw18119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18119step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18119step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18119 raw18119Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18119 raw18119Labels = mixedMoment B raw18119step0 raw18119step0Labels := by
      have hz : ∀ j, raw18119 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18119step0 = (fun i j => raw18119 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18119step0 raw18119; decide +kernel
      have hl : raw18119step0Labels = raw18119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18119 raw18119Labels permutation434 hz
    mixedMoment B raw18119step0 raw18119step0Labels = mixedMoment B raw18119step1 raw18119step1Labels := by
      have ha : raw18119step1 = (fun i j => raw18119step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18119step1 raw18119step0; decide +kernel
      have hl : raw18119step1Labels = raw18119step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18119step0 raw18119step0Labels permutation34 permutation3
    mixedMoment B raw18119step1 raw18119step1Labels = mixedMoment B raw18119step2 raw18119step2Labels := by
      have ha : raw18119step2 = raw18119step1 := by apply Matrix.ext; unfold raw18119step2 raw18119step1; decide +kernel
      have hl : raw18119step1Labels = labelEmbedding6 ∘ raw18119step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18119step1 raw18119step1Labels raw18119step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18120step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18120step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18120step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18120 raw18120Labels = mixedMoment B node5398 node5398Labels := by
  calc
    mixedMoment B raw18120 raw18120Labels = mixedMoment B raw18120step0 raw18120step0Labels := by
      have ha : raw18120step0 = (fun i j => raw18120 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18120step0 raw18120; decide +kernel
      have hl : raw18120step0Labels = raw18120Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18120 raw18120Labels permutation202 permutation3
    mixedMoment B raw18120step0 raw18120step0Labels = mixedMoment B raw18120step1 raw18120step1Labels := by
      have ha : raw18120step1 = raw18120step0 := by apply Matrix.ext; unfold raw18120step1 raw18120step0; decide +kernel
      have hl : raw18120step0Labels = labelEmbedding6 ∘ raw18120step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18120step0 raw18120step0Labels raw18120step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5398 node5398Labels := by rfl

def raw18121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18121step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18121step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18121step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18121step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18121 raw18121Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18121 raw18121Labels = mixedMoment B raw18121step0 raw18121step0Labels := by
      have hz : ∀ j, raw18121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18121step0 = (fun i j => raw18121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18121step0 raw18121; decide +kernel
      have hl : raw18121step0Labels = raw18121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18121 raw18121Labels permutation434 hz
    mixedMoment B raw18121step0 raw18121step0Labels = mixedMoment B raw18121step1 raw18121step1Labels := by
      have ha : raw18121step1 = (fun i j => raw18121step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18121step1 raw18121step0; decide +kernel
      have hl : raw18121step1Labels = raw18121step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18121step0 raw18121step0Labels permutation44 permutation5
    mixedMoment B raw18121step1 raw18121step1Labels = mixedMoment B raw18121step2 raw18121step2Labels := by
      have ha : raw18121step2 = -raw18121step1 := by apply Matrix.ext; change ∀ i j, raw18121step2 i j = -(raw18121step1 i j); unfold raw18121step2 raw18121step1; decide +kernel
      have hl : raw18121step2Labels = raw18121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18121step2 raw18121step2Labels = mixedMoment B raw18121step3 raw18121step3Labels := by
      have ha : raw18121step3 = raw18121step2 := by apply Matrix.ext; unfold raw18121step3 raw18121step2; decide +kernel
      have hl : raw18121step2Labels = labelEmbedding8 ∘ raw18121step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18121step2 raw18121step2Labels raw18121step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18122step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18122 raw18122Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw18122 raw18122Labels = mixedMoment B raw18122step0 raw18122step0Labels := by
      have hz : ∀ j, raw18122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18122step0 = (fun i j => raw18122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18122step0 raw18122; decide +kernel
      have hl : raw18122step0Labels = raw18122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18122 raw18122Labels permutation434 hz
    mixedMoment B raw18122step0 raw18122step0Labels = mixedMoment B raw18122step1 raw18122step1Labels := by
      have ha : raw18122step1 = (fun i j => raw18122step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18122step1 raw18122step0; decide +kernel
      have hl : raw18122step1Labels = raw18122step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18122step0 raw18122step0Labels permutation34 permutation3
    mixedMoment B raw18122step1 raw18122step1Labels = mixedMoment B raw18122step2 raw18122step2Labels := by
      have ha : raw18122step2 = raw18122step1 := by apply Matrix.ext; unfold raw18122step2 raw18122step1; decide +kernel
      have hl : raw18122step1Labels = labelEmbedding6 ∘ raw18122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18122step1 raw18122step1Labels raw18122step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw18123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18123step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18123 raw18123Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw18123 raw18123Labels = mixedMoment B raw18123step0 raw18123step0Labels := by
      have hz : ∀ j, raw18123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18123step0 = (fun i j => raw18123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18123step0 raw18123; decide +kernel
      have hl : raw18123step0Labels = raw18123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18123 raw18123Labels permutation346 hz
    mixedMoment B raw18123step0 raw18123step0Labels = mixedMoment B raw18123step1 raw18123step1Labels := by
      have ha : raw18123step1 = (fun i j => raw18123step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18123step1 raw18123step0; decide +kernel
      have hl : raw18123step1Labels = raw18123step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18123step0 raw18123step0Labels permutation34 permutation3
    mixedMoment B raw18123step1 raw18123step1Labels = mixedMoment B raw18123step2 raw18123step2Labels := by
      have ha : raw18123step2 = raw18123step1 := by apply Matrix.ext; unfold raw18123step2 raw18123step1; decide +kernel
      have hl : raw18123step1Labels = labelEmbedding6 ∘ raw18123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18123step1 raw18123step1Labels raw18123step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

def raw18124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18124 raw18124Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18124 raw18124Labels = mixedMoment B raw18124step0 raw18124step0Labels := by
      have hz : ∀ j, raw18124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18124step0 = (fun i j => raw18124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18124step0 raw18124; decide +kernel
      have hl : raw18124step0Labels = raw18124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18124 raw18124Labels permutation346 hz
    mixedMoment B raw18124step0 raw18124step0Labels = mixedMoment B raw18124step1 raw18124step1Labels := by
      have ha : raw18124step1 = (fun i j => raw18124step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18124step1 raw18124step0; decide +kernel
      have hl : raw18124step1Labels = raw18124step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18124step0 raw18124step0Labels permutation34 permutation3
    mixedMoment B raw18124step1 raw18124step1Labels = mixedMoment B raw18124step2 raw18124step2Labels := by
      have ha : raw18124step2 = raw18124step1 := by apply Matrix.ext; unfold raw18124step2 raw18124step1; decide +kernel
      have hl : raw18124step1Labels = labelEmbedding6 ∘ raw18124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18124step1 raw18124step1Labels raw18124step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18125step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18125 raw18125Labels = mixedMoment B node5398 node5398Labels := by
  calc
    mixedMoment B raw18125 raw18125Labels = mixedMoment B raw18125step0 raw18125step0Labels := by
      have ha : raw18125step0 = (fun i j => raw18125 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18125step0 raw18125; decide +kernel
      have hl : raw18125step0Labels = raw18125Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18125 raw18125Labels permutation178 permutation3
    mixedMoment B raw18125step0 raw18125step0Labels = mixedMoment B raw18125step1 raw18125step1Labels := by
      have ha : raw18125step1 = raw18125step0 := by apply Matrix.ext; unfold raw18125step1 raw18125step0; decide +kernel
      have hl : raw18125step0Labels = labelEmbedding6 ∘ raw18125step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18125step0 raw18125step0Labels raw18125step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5398 node5398Labels := by rfl

def raw18126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw18126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18126step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18126step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18126step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18126 raw18126Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18126 raw18126Labels = mixedMoment B raw18126step0 raw18126step0Labels := by
      have hz : ∀ j, raw18126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18126step0 = (fun i j => raw18126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18126step0 raw18126; decide +kernel
      have hl : raw18126step0Labels = raw18126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18126 raw18126Labels permutation346 hz
    mixedMoment B raw18126step0 raw18126step0Labels = mixedMoment B raw18126step1 raw18126step1Labels := by
      have ha : raw18126step1 = (fun i j => raw18126step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18126step1 raw18126step0; decide +kernel
      have hl : raw18126step1Labels = raw18126step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18126step0 raw18126step0Labels permutation44 permutation5
    mixedMoment B raw18126step1 raw18126step1Labels = mixedMoment B raw18126step2 raw18126step2Labels := by
      have ha : raw18126step2 = -raw18126step1 := by apply Matrix.ext; change ∀ i j, raw18126step2 i j = -(raw18126step1 i j); unfold raw18126step2 raw18126step1; decide +kernel
      have hl : raw18126step2Labels = raw18126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18126step2 raw18126step2Labels = mixedMoment B raw18126step3 raw18126step3Labels := by
      have ha : raw18126step3 = raw18126step2 := by apply Matrix.ext; unfold raw18126step3 raw18126step2; decide +kernel
      have hl : raw18126step2Labels = labelEmbedding8 ∘ raw18126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18126step2 raw18126step2Labels raw18126step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw18127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18127step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18127 raw18127Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw18127 raw18127Labels = mixedMoment B raw18127step0 raw18127step0Labels := by
      have hz : ∀ j, raw18127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18127step0 = (fun i j => raw18127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18127step0 raw18127; decide +kernel
      have hl : raw18127step0Labels = raw18127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18127 raw18127Labels permutation346 hz
    mixedMoment B raw18127step0 raw18127step0Labels = mixedMoment B raw18127step1 raw18127step1Labels := by
      have ha : raw18127step1 = (fun i j => raw18127step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18127step1 raw18127step0; decide +kernel
      have hl : raw18127step1Labels = raw18127step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18127step0 raw18127step0Labels permutation34 permutation3
    mixedMoment B raw18127step1 raw18127step1Labels = mixedMoment B raw18127step2 raw18127step2Labels := by
      have ha : raw18127step2 = raw18127step1 := by apply Matrix.ext; unfold raw18127step2 raw18127step1; decide +kernel
      have hl : raw18127step1Labels = labelEmbedding6 ∘ raw18127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18127step1 raw18127step1Labels raw18127step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw18128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -2, 0]]
def raw18128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18128step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18128step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18128step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18128step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18128 raw18128Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw18128 raw18128Labels = mixedMoment B raw18128step0 raw18128step0Labels := by
      have hz : ∀ j, raw18128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18128step0 = (fun i j => raw18128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18128step0 raw18128; decide +kernel
      have hl : raw18128step0Labels = raw18128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18128 raw18128Labels permutation434 hz
    mixedMoment B raw18128step0 raw18128step0Labels = mixedMoment B raw18128step1 raw18128step1Labels := by
      have hz : ∀ j, raw18128step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18128step1 = (fun i j => raw18128step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18128step1 raw18128step0; decide +kernel
      have hl : raw18128step1Labels = raw18128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18128step0 raw18128step0Labels permutation80 hz
    mixedMoment B raw18128step1 raw18128step1Labels = mixedMoment B raw18128step2 raw18128step2Labels := by
      have ha : raw18128step2 = (fun i j => raw18128step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18128step2 raw18128step1; decide +kernel
      have hl : raw18128step2Labels = raw18128step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18128step1 raw18128step1Labels permutation8 permutation3
    mixedMoment B raw18128step2 raw18128step2Labels = mixedMoment B raw18128step3 raw18128step3Labels := by
      have ha : raw18128step3 = raw18128step2 := by apply Matrix.ext; unfold raw18128step3 raw18128step2; decide +kernel
      have hl : raw18128step2Labels = labelEmbedding6 ∘ raw18128step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18128step2 raw18128step2Labels raw18128step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw18129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, 0, -2], ![2, -2, 0]]
def raw18129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw18129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18129 raw18129Labels = mixedMoment B node5389 node5389Labels := by
  calc
    mixedMoment B raw18129 raw18129Labels = mixedMoment B raw18129step0 raw18129step0Labels := by
      have hz : ∀ j, raw18129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18129step0 = (fun i j => raw18129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18129step0 raw18129; decide +kernel
      have hl : raw18129step0Labels = raw18129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18129 raw18129Labels permutation434 hz
    mixedMoment B raw18129step0 raw18129step0Labels = mixedMoment B raw18129step1 raw18129step1Labels := by
      have hz : ∀ j, raw18129step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18129step1 = (fun i j => raw18129step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18129step1 raw18129step0; decide +kernel
      have hl : raw18129step1Labels = raw18129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18129step0 raw18129step0Labels permutation80 hz
    mixedMoment B raw18129step1 raw18129step1Labels = mixedMoment B raw18129step2 raw18129step2Labels := by
      have ha : raw18129step2 = (fun i j => raw18129step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18129step2 raw18129step1; decide +kernel
      have hl : raw18129step2Labels = raw18129step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18129step1 raw18129step1Labels permutation15 permutation2
    _ = mixedMoment B node5389 node5389Labels := by rfl

def raw18130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18130step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18130step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18130step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18130 raw18130Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18130 raw18130Labels = mixedMoment B raw18130step0 raw18130step0Labels := by
      have hz : ∀ j, raw18130 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18130step0 = (fun i j => raw18130 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18130step0 raw18130; decide +kernel
      have hl : raw18130step0Labels = raw18130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18130 raw18130Labels permutation434 hz
    mixedMoment B raw18130step0 raw18130step0Labels = mixedMoment B raw18130step1 raw18130step1Labels := by
      have ha : raw18130step1 = (fun i j => raw18130step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18130step1 raw18130step0; decide +kernel
      have hl : raw18130step1Labels = raw18130step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18130step0 raw18130step0Labels permutation149 permutation3
    mixedMoment B raw18130step1 raw18130step1Labels = mixedMoment B raw18130step2 raw18130step2Labels := by
      have ha : raw18130step2 = -raw18130step1 := by apply Matrix.ext; change ∀ i j, raw18130step2 i j = -(raw18130step1 i j); unfold raw18130step2 raw18130step1; decide +kernel
      have hl : raw18130step2Labels = raw18130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18130step2 raw18130step2Labels = mixedMoment B raw18130step3 raw18130step3Labels := by
      have ha : raw18130step3 = raw18130step2 := by apply Matrix.ext; unfold raw18130step3 raw18130step2; decide +kernel
      have hl : raw18130step2Labels = labelEmbedding6 ∘ raw18130step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18130step2 raw18130step2Labels raw18130step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw18131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18131step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18131step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18131step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18131 raw18131Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18131 raw18131Labels = mixedMoment B raw18131step0 raw18131step0Labels := by
      have hz : ∀ j, raw18131 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18131step0 = (fun i j => raw18131 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18131step0 raw18131; decide +kernel
      have hl : raw18131step0Labels = raw18131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18131 raw18131Labels permutation346 hz
    mixedMoment B raw18131step0 raw18131step0Labels = mixedMoment B raw18131step1 raw18131step1Labels := by
      have ha : raw18131step1 = (fun i j => raw18131step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18131step1 raw18131step0; decide +kernel
      have hl : raw18131step1Labels = raw18131step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18131step0 raw18131step0Labels permutation149 permutation3
    mixedMoment B raw18131step1 raw18131step1Labels = mixedMoment B raw18131step2 raw18131step2Labels := by
      have ha : raw18131step2 = -raw18131step1 := by apply Matrix.ext; change ∀ i j, raw18131step2 i j = -(raw18131step1 i j); unfold raw18131step2 raw18131step1; decide +kernel
      have hl : raw18131step2Labels = raw18131step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18131step2 raw18131step2Labels = mixedMoment B raw18131step3 raw18131step3Labels := by
      have ha : raw18131step3 = raw18131step2 := by apply Matrix.ext; unfold raw18131step3 raw18131step2; decide +kernel
      have hl : raw18131step2Labels = labelEmbedding6 ∘ raw18131step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18131step2 raw18131step2Labels raw18131step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw18132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw18132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, 0, -2], ![1, -1, 0]]
def raw18132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw18132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18132step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18132 raw18132Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw18132 raw18132Labels = mixedMoment B raw18132step0 raw18132step0Labels := by
      have hz : ∀ j, raw18132 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18132step0 = (fun i j => raw18132 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18132step0 raw18132; decide +kernel
      have hl : raw18132step0Labels = raw18132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18132 raw18132Labels permutation434 hz
    mixedMoment B raw18132step0 raw18132step0Labels = mixedMoment B raw18132step1 raw18132step1Labels := by
      have hz : ∀ j, raw18132step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18132step1 = (fun i j => raw18132step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18132step1 raw18132step0; decide +kernel
      have hl : raw18132step1Labels = raw18132step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18132step0 raw18132step0Labels permutation80 hz
    mixedMoment B raw18132step1 raw18132step1Labels = mixedMoment B raw18132step2 raw18132step2Labels := by
      have ha : raw18132step2 = (fun i j => raw18132step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18132step2 raw18132step1; decide +kernel
      have hl : raw18132step2Labels = raw18132step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18132step1 raw18132step1Labels permutation25 permutation2
    mixedMoment B raw18132step2 raw18132step2Labels = mixedMoment B raw18132step3 raw18132step3Labels := by
      have ha : raw18132step3 = -raw18132step2 := by apply Matrix.ext; change ∀ i j, raw18132step3 i j = -(raw18132step2 i j); unfold raw18132step3 raw18132step2; decide +kernel
      have hl : raw18132step3Labels = raw18132step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw18133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -3, 0]]
def raw18133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18133step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18133 raw18133Labels = mixedMoment B node4862 node4862Labels := by
  calc
    mixedMoment B raw18133 raw18133Labels = mixedMoment B raw18133step0 raw18133step0Labels := by
      have hz : ∀ j, raw18133 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18133step0 = (fun i j => raw18133 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18133step0 raw18133; decide +kernel
      have hl : raw18133step0Labels = raw18133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18133 raw18133Labels permutation434 hz
    mixedMoment B raw18133step0 raw18133step0Labels = mixedMoment B raw18133step1 raw18133step1Labels := by
      have hz : ∀ j, raw18133step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18133step1 = (fun i j => raw18133step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18133step1 raw18133step0; decide +kernel
      have hl : raw18133step1Labels = raw18133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18133step0 raw18133step0Labels permutation80 hz
    mixedMoment B raw18133step1 raw18133step1Labels = mixedMoment B raw18133step2 raw18133step2Labels := by
      have ha : raw18133step2 = (fun i j => raw18133step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18133step2 raw18133step1; decide +kernel
      have hl : raw18133step2Labels = raw18133step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18133step1 raw18133step1Labels permutation8 permutation3
    mixedMoment B raw18133step2 raw18133step2Labels = mixedMoment B raw18133step3 raw18133step3Labels := by
      have ha : raw18133step3 = raw18133step2 := by apply Matrix.ext; unfold raw18133step3 raw18133step2; decide +kernel
      have hl : raw18133step2Labels = labelEmbedding6 ∘ raw18133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18133step2 raw18133step2Labels raw18133step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4862 node4862Labels := by rfl

def raw18134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 1, -2], ![3, -3, 0]]
def raw18134step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18134step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18134step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18134step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18134step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18134step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18134 raw18134Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw18134 raw18134Labels = mixedMoment B raw18134step0 raw18134step0Labels := by
      have hz : ∀ j, raw18134 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18134step0 = (fun i j => raw18134 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18134step0 raw18134; decide +kernel
      have hl : raw18134step0Labels = raw18134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18134 raw18134Labels permutation434 hz
    mixedMoment B raw18134step0 raw18134step0Labels = mixedMoment B raw18134step1 raw18134step1Labels := by
      have hz : ∀ j, raw18134step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18134step1 = (fun i j => raw18134step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18134step1 raw18134step0; decide +kernel
      have hl : raw18134step1Labels = raw18134step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18134step0 raw18134step0Labels permutation80 hz
    mixedMoment B raw18134step1 raw18134step1Labels = mixedMoment B raw18134step2 raw18134step2Labels := by
      have ha : raw18134step2 = (fun i j => raw18134step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18134step2 raw18134step1; decide +kernel
      have hl : raw18134step2Labels = raw18134step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18134step1 raw18134step1Labels permutation31 permutation3
    mixedMoment B raw18134step2 raw18134step2Labels = mixedMoment B raw18134step3 raw18134step3Labels := by
      have ha : raw18134step3 = -raw18134step2 := by apply Matrix.ext; change ∀ i j, raw18134step3 i j = -(raw18134step2 i j); unfold raw18134step3 raw18134step2; decide +kernel
      have hl : raw18134step3Labels = raw18134step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18134step3 raw18134step3Labels = mixedMoment B raw18134step4 raw18134step4Labels := by
      have ha : raw18134step4 = raw18134step3 := by apply Matrix.ext; unfold raw18134step4 raw18134step3; decide +kernel
      have hl : raw18134step3Labels = labelEmbedding6 ∘ raw18134step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18134step3 raw18134step3Labels raw18134step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw18135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18135step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18135step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18135 raw18135Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw18135 raw18135Labels = mixedMoment B raw18135step0 raw18135step0Labels := by
      have hz : ∀ j, raw18135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18135step0 = (fun i j => raw18135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18135step0 raw18135; decide +kernel
      have hl : raw18135step0Labels = raw18135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18135 raw18135Labels permutation434 hz
    mixedMoment B raw18135step0 raw18135step0Labels = mixedMoment B raw18135step1 raw18135step1Labels := by
      have ha : raw18135step1 = (fun i j => raw18135step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18135step1 raw18135step0; decide +kernel
      have hl : raw18135step1Labels = raw18135step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18135step0 raw18135step0Labels permutation149 permutation3
    mixedMoment B raw18135step1 raw18135step1Labels = mixedMoment B raw18135step2 raw18135step2Labels := by
      have ha : raw18135step2 = -raw18135step1 := by apply Matrix.ext; change ∀ i j, raw18135step2 i j = -(raw18135step1 i j); unfold raw18135step2 raw18135step1; decide +kernel
      have hl : raw18135step2Labels = raw18135step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18135step2 raw18135step2Labels = mixedMoment B raw18135step3 raw18135step3Labels := by
      have ha : raw18135step3 = raw18135step2 := by apply Matrix.ext; unfold raw18135step3 raw18135step2; decide +kernel
      have hl : raw18135step2Labels = labelEmbedding6 ∘ raw18135step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18135step2 raw18135step2Labels raw18135step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

def raw18136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw18136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18136step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18136step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18136step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18136step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18136 raw18136Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw18136 raw18136Labels = mixedMoment B raw18136step0 raw18136step0Labels := by
      have hz : ∀ j, raw18136 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18136step0 = (fun i j => raw18136 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18136step0 raw18136; decide +kernel
      have hl : raw18136step0Labels = raw18136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18136 raw18136Labels permutation346 hz
    mixedMoment B raw18136step0 raw18136step0Labels = mixedMoment B raw18136step1 raw18136step1Labels := by
      have ha : raw18136step1 = (fun i j => raw18136step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18136step1 raw18136step0; decide +kernel
      have hl : raw18136step1Labels = raw18136step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18136step0 raw18136step0Labels permutation149 permutation3
    mixedMoment B raw18136step1 raw18136step1Labels = mixedMoment B raw18136step2 raw18136step2Labels := by
      have ha : raw18136step2 = -raw18136step1 := by apply Matrix.ext; change ∀ i j, raw18136step2 i j = -(raw18136step1 i j); unfold raw18136step2 raw18136step1; decide +kernel
      have hl : raw18136step2Labels = raw18136step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18136step2 raw18136step2Labels = mixedMoment B raw18136step3 raw18136step3Labels := by
      have ha : raw18136step3 = raw18136step2 := by apply Matrix.ext; unfold raw18136step3 raw18136step2; decide +kernel
      have hl : raw18136step2Labels = labelEmbedding6 ∘ raw18136step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18136step2 raw18136step2Labels raw18136step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

def raw18137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw18137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw18137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw18137step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18137step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18137step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18137step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18137step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18137 raw18137Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw18137 raw18137Labels = mixedMoment B raw18137step0 raw18137step0Labels := by
      have hz : ∀ j, raw18137 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18137step0 = (fun i j => raw18137 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18137step0 raw18137; decide +kernel
      have hl : raw18137step0Labels = raw18137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18137 raw18137Labels permutation434 hz
    mixedMoment B raw18137step0 raw18137step0Labels = mixedMoment B raw18137step1 raw18137step1Labels := by
      have hz : ∀ j, raw18137step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18137step1 = (fun i j => raw18137step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18137step1 raw18137step0; decide +kernel
      have hl : raw18137step1Labels = raw18137step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18137step0 raw18137step0Labels permutation80 hz
    mixedMoment B raw18137step1 raw18137step1Labels = mixedMoment B raw18137step2 raw18137step2Labels := by
      have ha : raw18137step2 = (fun i j => raw18137step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18137step2 raw18137step1; decide +kernel
      have hl : raw18137step2Labels = raw18137step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18137step1 raw18137step1Labels permutation29 permutation5
    mixedMoment B raw18137step2 raw18137step2Labels = mixedMoment B raw18137step3 raw18137step3Labels := by
      have ha : raw18137step3 = raw18137step2 := by apply Matrix.ext; unfold raw18137step3 raw18137step2; decide +kernel
      have hl : raw18137step2Labels = labelEmbedding8 ∘ raw18137step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18137step2 raw18137step2Labels raw18137step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw18138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18138step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18138step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18138step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18138 raw18138Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw18138 raw18138Labels = mixedMoment B raw18138step0 raw18138step0Labels := by
      have hz : ∀ j, raw18138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18138step0 = (fun i j => raw18138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18138step0 raw18138; decide +kernel
      have hl : raw18138step0Labels = raw18138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18138 raw18138Labels permutation346 hz
    mixedMoment B raw18138step0 raw18138step0Labels = mixedMoment B raw18138step1 raw18138step1Labels := by
      have ha : raw18138step1 = (fun i j => raw18138step0 (permutation74 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18138step1 raw18138step0; decide +kernel
      have hl : raw18138step1Labels = raw18138step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18138step0 raw18138step0Labels permutation74 permutation5
    mixedMoment B raw18138step1 raw18138step1Labels = mixedMoment B raw18138step2 raw18138step2Labels := by
      have ha : raw18138step2 = -raw18138step1 := by apply Matrix.ext; change ∀ i j, raw18138step2 i j = -(raw18138step1 i j); unfold raw18138step2 raw18138step1; decide +kernel
      have hl : raw18138step2Labels = raw18138step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18138step2 raw18138step2Labels = mixedMoment B raw18138step3 raw18138step3Labels := by
      have ha : raw18138step3 = raw18138step2 := by apply Matrix.ext; unfold raw18138step3 raw18138step2; decide +kernel
      have hl : raw18138step2Labels = labelEmbedding8 ∘ raw18138step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18138step2 raw18138step2Labels raw18138step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw18139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18139step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18139 raw18139Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18139 raw18139Labels = mixedMoment B raw18139step0 raw18139step0Labels := by
      have ha : raw18139step0 = (fun i j => raw18139 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18139step0 raw18139; decide +kernel
      have hl : raw18139step0Labels = raw18139Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18139 raw18139Labels permutation686 permutation2
    mixedMoment B raw18139step0 raw18139step0Labels = mixedMoment B raw18139step1 raw18139step1Labels := by
      have ha : raw18139step1 = -raw18139step0 := by apply Matrix.ext; change ∀ i j, raw18139step1 i j = -(raw18139step0 i j); unfold raw18139step1 raw18139step0; decide +kernel
      have hl : raw18139step1Labels = raw18139step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18140step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18140 raw18140Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18140 raw18140Labels = mixedMoment B raw18140step0 raw18140step0Labels := by
      have hz : ∀ j, raw18140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18140step0 = (fun i j => raw18140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18140step0 raw18140; decide +kernel
      have hl : raw18140step0Labels = raw18140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18140 raw18140Labels permutation346 hz
    mixedMoment B raw18140step0 raw18140step0Labels = mixedMoment B raw18140step1 raw18140step1Labels := by
      have ha : raw18140step1 = (fun i j => raw18140step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18140step1 raw18140step0; decide +kernel
      have hl : raw18140step1Labels = raw18140step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18140step0 raw18140step0Labels permutation149 permutation2
    mixedMoment B raw18140step1 raw18140step1Labels = mixedMoment B raw18140step2 raw18140step2Labels := by
      have ha : raw18140step2 = -raw18140step1 := by apply Matrix.ext; change ∀ i j, raw18140step2 i j = -(raw18140step1 i j); unfold raw18140step2 raw18140step1; decide +kernel
      have hl : raw18140step2Labels = raw18140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw18141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18141step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18141step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18141step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18141 raw18141Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw18141 raw18141Labels = mixedMoment B raw18141step0 raw18141step0Labels := by
      have hz : ∀ j, raw18141 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18141step0 = (fun i j => raw18141 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18141step0 raw18141; decide +kernel
      have hl : raw18141step0Labels = raw18141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18141 raw18141Labels permutation520 hz
    mixedMoment B raw18141step0 raw18141step0Labels = mixedMoment B raw18141step1 raw18141step1Labels := by
      have hz : ∀ j, raw18141step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18141step1 = (fun i j => raw18141step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18141step1 raw18141step0; decide +kernel
      have hl : raw18141step1Labels = raw18141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18141step0 raw18141step0Labels permutation80 hz
    mixedMoment B raw18141step1 raw18141step1Labels = mixedMoment B raw18141step2 raw18141step2Labels := by
      have ha : raw18141step2 = (fun i j => raw18141step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18141step2 raw18141step1; decide +kernel
      have hl : raw18141step2Labels = raw18141step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18141step1 raw18141step1Labels permutation29 permutation7
    mixedMoment B raw18141step2 raw18141step2Labels = mixedMoment B raw18141step3 raw18141step3Labels := by
      have ha : raw18141step3 = raw18141step2 := by apply Matrix.ext; unfold raw18141step3 raw18141step2; decide +kernel
      have hl : raw18141step2Labels = labelEmbedding10 ∘ raw18141step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18141step2 raw18141step2Labels raw18141step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw18142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18142step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18142step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18142 raw18142Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18142 raw18142Labels = mixedMoment B raw18142step0 raw18142step0Labels := by
      have hz : ∀ j, raw18142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18142step0 = (fun i j => raw18142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18142step0 raw18142; decide +kernel
      have hl : raw18142step0Labels = raw18142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18142 raw18142Labels permutation346 hz
    mixedMoment B raw18142step0 raw18142step0Labels = mixedMoment B raw18142step1 raw18142step1Labels := by
      have ha : raw18142step1 = (fun i j => raw18142step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18142step1 raw18142step0; decide +kernel
      have hl : raw18142step1Labels = raw18142step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18142step0 raw18142step0Labels permutation139 permutation6
    mixedMoment B raw18142step1 raw18142step1Labels = mixedMoment B raw18142step2 raw18142step2Labels := by
      have ha : raw18142step2 = raw18142step1 := by apply Matrix.ext; unfold raw18142step2 raw18142step1; decide +kernel
      have hl : raw18142step1Labels = labelEmbedding9 ∘ raw18142step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18142step1 raw18142step1Labels raw18142step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18143step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18143 raw18143Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw18143 raw18143Labels = mixedMoment B raw18143step0 raw18143step0Labels := by
      have hz : ∀ j, raw18143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18143step0 = (fun i j => raw18143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18143step0 raw18143; decide +kernel
      have hl : raw18143step0Labels = raw18143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18143 raw18143Labels permutation346 hz
    mixedMoment B raw18143step0 raw18143step0Labels = mixedMoment B raw18143step1 raw18143step1Labels := by
      have ha : raw18143step1 = (fun i j => raw18143step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18143step1 raw18143step0; decide +kernel
      have hl : raw18143step1Labels = raw18143step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18143step0 raw18143step0Labels permutation38 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw18144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18144step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18144step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18144 raw18144Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw18144 raw18144Labels = mixedMoment B raw18144step0 raw18144step0Labels := by
      have ha : raw18144step0 = (fun i j => raw18144 (permutation285 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18144step0 raw18144; decide +kernel
      have hl : raw18144step0Labels = raw18144Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18144 raw18144Labels permutation285 permutation5
    mixedMoment B raw18144step0 raw18144step0Labels = mixedMoment B raw18144step1 raw18144step1Labels := by
      have ha : raw18144step1 = -raw18144step0 := by apply Matrix.ext; change ∀ i j, raw18144step1 i j = -(raw18144step0 i j); unfold raw18144step1 raw18144step0; decide +kernel
      have hl : raw18144step1Labels = raw18144step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18144step1 raw18144step1Labels = mixedMoment B raw18144step2 raw18144step2Labels := by
      have ha : raw18144step2 = raw18144step1 := by apply Matrix.ext; unfold raw18144step2 raw18144step1; decide +kernel
      have hl : raw18144step1Labels = labelEmbedding8 ∘ raw18144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18144step1 raw18144step1Labels raw18144step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw18145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18145 raw18145Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw18145 raw18145Labels = mixedMoment B raw18145step0 raw18145step0Labels := by
      have ha : raw18145step0 = (fun i j => raw18145 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18145step0 raw18145; decide +kernel
      have hl : raw18145step0Labels = raw18145Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18145 raw18145Labels permutation200 permutation2
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw18146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18146 raw18146Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18146 raw18146Labels = mixedMoment B raw18146step0 raw18146step0Labels := by
      have hz : ∀ j, raw18146 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18146step0 = (fun i j => raw18146 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18146step0 raw18146; decide +kernel
      have hl : raw18146step0Labels = raw18146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18146 raw18146Labels permutation520 hz
    mixedMoment B raw18146step0 raw18146step0Labels = mixedMoment B raw18146step1 raw18146step1Labels := by
      have ha : raw18146step1 = (fun i j => raw18146step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18146step1 raw18146step0; decide +kernel
      have hl : raw18146step1Labels = raw18146step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18146step0 raw18146step0Labels permutation145 permutation2
    mixedMoment B raw18146step1 raw18146step1Labels = mixedMoment B raw18146step2 raw18146step2Labels := by
      have ha : raw18146step2 = -raw18146step1 := by apply Matrix.ext; change ∀ i j, raw18146step2 i j = -(raw18146step1 i j); unfold raw18146step2 raw18146step1; decide +kernel
      have hl : raw18146step2Labels = raw18146step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw18147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18147step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18147step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18147step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18147step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18147 raw18147Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw18147 raw18147Labels = mixedMoment B raw18147step0 raw18147step0Labels := by
      have ha : raw18147step0 = (fun i j => raw18147 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18147step0 raw18147; decide +kernel
      have hl : raw18147step0Labels = raw18147Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18147 raw18147Labels permutation208 permutation7
    mixedMoment B raw18147step0 raw18147step0Labels = mixedMoment B raw18147step1 raw18147step1Labels := by
      have ha : raw18147step1 = -raw18147step0 := by apply Matrix.ext; change ∀ i j, raw18147step1 i j = -(raw18147step0 i j); unfold raw18147step1 raw18147step0; decide +kernel
      have hl : raw18147step1Labels = raw18147step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18147step1 raw18147step1Labels = mixedMoment B raw18147step2 raw18147step2Labels := by
      have ha : raw18147step2 = raw18147step1 := by apply Matrix.ext; unfold raw18147step2 raw18147step1; decide +kernel
      have hl : raw18147step1Labels = labelEmbedding10 ∘ raw18147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18147step1 raw18147step1Labels raw18147step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw18148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18148step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18148step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18148step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18148step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18148 raw18148Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw18148 raw18148Labels = mixedMoment B raw18148step0 raw18148step0Labels := by
      have hz : ∀ j, raw18148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18148step0 = (fun i j => raw18148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18148step0 raw18148; decide +kernel
      have hl : raw18148step0Labels = raw18148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18148 raw18148Labels permutation346 hz
    mixedMoment B raw18148step0 raw18148step0Labels = mixedMoment B raw18148step1 raw18148step1Labels := by
      have ha : raw18148step1 = (fun i j => raw18148step0 (permutation61 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18148step1 raw18148step0; decide +kernel
      have hl : raw18148step1Labels = raw18148step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18148step0 raw18148step0Labels permutation61 permutation5
    mixedMoment B raw18148step1 raw18148step1Labels = mixedMoment B raw18148step2 raw18148step2Labels := by
      have ha : raw18148step2 = -raw18148step1 := by apply Matrix.ext; change ∀ i j, raw18148step2 i j = -(raw18148step1 i j); unfold raw18148step2 raw18148step1; decide +kernel
      have hl : raw18148step2Labels = raw18148step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18148step2 raw18148step2Labels = mixedMoment B raw18148step3 raw18148step3Labels := by
      have ha : raw18148step3 = raw18148step2 := by apply Matrix.ext; unfold raw18148step3 raw18148step2; decide +kernel
      have hl : raw18148step2Labels = labelEmbedding8 ∘ raw18148step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18148step2 raw18148step2Labels raw18148step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw18149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18149 raw18149Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw18149 raw18149Labels = mixedMoment B raw18149step0 raw18149step0Labels := by
      have ha : raw18149step0 = (fun i j => raw18149 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18149step0 raw18149; decide +kernel
      have hl : raw18149step0Labels = raw18149Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18149 raw18149Labels permutation176 permutation2
    _ = mixedMoment B node5420 node5420Labels := by rfl

def raw18150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18150step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18150 raw18150Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw18150 raw18150Labels = mixedMoment B raw18150step0 raw18150step0Labels := by
      have hz : ∀ j, raw18150 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18150step0 = (fun i j => raw18150 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18150step0 raw18150; decide +kernel
      have hl : raw18150step0Labels = raw18150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18150 raw18150Labels permutation520 hz
    mixedMoment B raw18150step0 raw18150step0Labels = mixedMoment B raw18150step1 raw18150step1Labels := by
      have hz : ∀ j, raw18150step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18150step1 = (fun i j => raw18150step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18150step1 raw18150step0; decide +kernel
      have hl : raw18150step1Labels = raw18150step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18150step0 raw18150step0Labels permutation80 hz
    _ = mixedMoment B node5449 node5449Labels := by rfl

def raw18151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18151step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18151step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18151step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18151 raw18151Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw18151 raw18151Labels = mixedMoment B raw18151step0 raw18151step0Labels := by
      have hz : ∀ j, raw18151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18151step0 = (fun i j => raw18151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18151step0 raw18151; decide +kernel
      have hl : raw18151step0Labels = raw18151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18151 raw18151Labels permutation346 hz
    mixedMoment B raw18151step0 raw18151step0Labels = mixedMoment B raw18151step1 raw18151step1Labels := by
      have ha : raw18151step1 = (fun i j => raw18151step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18151step1 raw18151step0; decide +kernel
      have hl : raw18151step1Labels = raw18151step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18151step0 raw18151step0Labels permutation40 permutation7
    mixedMoment B raw18151step1 raw18151step1Labels = mixedMoment B raw18151step2 raw18151step2Labels := by
      have ha : raw18151step2 = -raw18151step1 := by apply Matrix.ext; change ∀ i j, raw18151step2 i j = -(raw18151step1 i j); unfold raw18151step2 raw18151step1; decide +kernel
      have hl : raw18151step2Labels = raw18151step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18151step2 raw18151step2Labels = mixedMoment B raw18151step3 raw18151step3Labels := by
      have ha : raw18151step3 = raw18151step2 := by apply Matrix.ext; unfold raw18151step3 raw18151step2; decide +kernel
      have hl : raw18151step2Labels = labelEmbedding10 ∘ raw18151step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18151step2 raw18151step2Labels raw18151step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw18152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18152step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18152step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18152step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18152step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18152 raw18152Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw18152 raw18152Labels = mixedMoment B raw18152step0 raw18152step0Labels := by
      have hz : ∀ j, raw18152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18152step0 = (fun i j => raw18152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18152step0 raw18152; decide +kernel
      have hl : raw18152step0Labels = raw18152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18152 raw18152Labels permutation346 hz
    mixedMoment B raw18152step0 raw18152step0Labels = mixedMoment B raw18152step1 raw18152step1Labels := by
      have ha : raw18152step1 = (fun i j => raw18152step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18152step1 raw18152step0; decide +kernel
      have hl : raw18152step1Labels = raw18152step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18152step0 raw18152step0Labels permutation60 permutation5
    mixedMoment B raw18152step1 raw18152step1Labels = mixedMoment B raw18152step2 raw18152step2Labels := by
      have ha : raw18152step2 = -raw18152step1 := by apply Matrix.ext; change ∀ i j, raw18152step2 i j = -(raw18152step1 i j); unfold raw18152step2 raw18152step1; decide +kernel
      have hl : raw18152step2Labels = raw18152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18152step2 raw18152step2Labels = mixedMoment B raw18152step3 raw18152step3Labels := by
      have ha : raw18152step3 = raw18152step2 := by apply Matrix.ext; unfold raw18152step3 raw18152step2; decide +kernel
      have hl : raw18152step2Labels = labelEmbedding8 ∘ raw18152step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18152step2 raw18152step2Labels raw18152step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw18153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18153step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18153step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18153 raw18153Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw18153 raw18153Labels = mixedMoment B raw18153step0 raw18153step0Labels := by
      have ha : raw18153step0 = (fun i j => raw18153 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18153step0 raw18153; decide +kernel
      have hl : raw18153step0Labels = raw18153Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18153 raw18153Labels permutation589 permutation3
    mixedMoment B raw18153step0 raw18153step0Labels = mixedMoment B raw18153step1 raw18153step1Labels := by
      have ha : raw18153step1 = -raw18153step0 := by apply Matrix.ext; change ∀ i j, raw18153step1 i j = -(raw18153step0 i j); unfold raw18153step1 raw18153step0; decide +kernel
      have hl : raw18153step1Labels = raw18153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18153step1 raw18153step1Labels = mixedMoment B raw18153step2 raw18153step2Labels := by
      have ha : raw18153step2 = raw18153step1 := by apply Matrix.ext; unfold raw18153step2 raw18153step1; decide +kernel
      have hl : raw18153step1Labels = labelEmbedding6 ∘ raw18153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18153step1 raw18153step1Labels raw18153step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw18154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18154 raw18154Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw18154 raw18154Labels = mixedMoment B raw18154step0 raw18154step0Labels := by
      have hz : ∀ j, raw18154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18154step0 = (fun i j => raw18154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18154step0 raw18154; decide +kernel
      have hl : raw18154step0Labels = raw18154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18154 raw18154Labels permutation346 hz
    mixedMoment B raw18154step0 raw18154step0Labels = mixedMoment B raw18154step1 raw18154step1Labels := by
      have ha : raw18154step1 = (fun i j => raw18154step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18154step1 raw18154step0; decide +kernel
      have hl : raw18154step1Labels = raw18154step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18154step0 raw18154step0Labels permutation149 permutation2
    mixedMoment B raw18154step1 raw18154step1Labels = mixedMoment B raw18154step2 raw18154step2Labels := by
      have ha : raw18154step2 = -raw18154step1 := by apply Matrix.ext; change ∀ i j, raw18154step2 i j = -(raw18154step1 i j); unfold raw18154step2 raw18154step1; decide +kernel
      have hl : raw18154step2Labels = raw18154step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw18155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18155step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18155 raw18155Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw18155 raw18155Labels = mixedMoment B raw18155step0 raw18155step0Labels := by
      have hz : ∀ j, raw18155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18155step0 = (fun i j => raw18155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18155step0 raw18155; decide +kernel
      have hl : raw18155step0Labels = raw18155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18155 raw18155Labels permutation346 hz
    mixedMoment B raw18155step0 raw18155step0Labels = mixedMoment B raw18155step1 raw18155step1Labels := by
      have ha : raw18155step1 = (fun i j => raw18155step0 (permutation117 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18155step1 raw18155step0; decide +kernel
      have hl : raw18155step1Labels = raw18155step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18155step0 raw18155step0Labels permutation117 permutation5
    mixedMoment B raw18155step1 raw18155step1Labels = mixedMoment B raw18155step2 raw18155step2Labels := by
      have ha : raw18155step2 = raw18155step1 := by apply Matrix.ext; unfold raw18155step2 raw18155step1; decide +kernel
      have hl : raw18155step1Labels = labelEmbedding8 ∘ raw18155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18155step1 raw18155step1Labels raw18155step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw18156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw18156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw18156step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18156 raw18156Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw18156 raw18156Labels = mixedMoment B raw18156step0 raw18156step0Labels := by
      have hz : ∀ j, raw18156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18156step0 = (fun i j => raw18156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18156step0 raw18156; decide +kernel
      have hl : raw18156step0Labels = raw18156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18156 raw18156Labels permutation346 hz
    mixedMoment B raw18156step0 raw18156step0Labels = mixedMoment B raw18156step1 raw18156step1Labels := by
      have ha : raw18156step1 = (fun i j => raw18156step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18156step1 raw18156step0; decide +kernel
      have hl : raw18156step1Labels = raw18156step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18156step0 raw18156step0Labels permutation151 permutation2
    mixedMoment B raw18156step1 raw18156step1Labels = mixedMoment B raw18156step2 raw18156step2Labels := by
      have ha : raw18156step2 = -raw18156step1 := by apply Matrix.ext; change ∀ i j, raw18156step2 i j = -(raw18156step1 i j); unfold raw18156step2 raw18156step1; decide +kernel
      have hl : raw18156step2Labels = raw18156step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw18157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18157step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18157 raw18157Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw18157 raw18157Labels = mixedMoment B raw18157step0 raw18157step0Labels := by
      have ha : raw18157step0 = (fun i j => raw18157 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18157step0 raw18157; decide +kernel
      have hl : raw18157step0Labels = raw18157Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18157 raw18157Labels permutation686 permutation2
    mixedMoment B raw18157step0 raw18157step0Labels = mixedMoment B raw18157step1 raw18157step1Labels := by
      have ha : raw18157step1 = -raw18157step0 := by apply Matrix.ext; change ∀ i j, raw18157step1 i j = -(raw18157step0 i j); unfold raw18157step1 raw18157step0; decide +kernel
      have hl : raw18157step1Labels = raw18157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw18158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18158step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18158 raw18158Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw18158 raw18158Labels = mixedMoment B raw18158step0 raw18158step0Labels := by
      have hz : ∀ j, raw18158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18158step0 = (fun i j => raw18158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18158step0 raw18158; decide +kernel
      have hl : raw18158step0Labels = raw18158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18158 raw18158Labels permutation346 hz
    mixedMoment B raw18158step0 raw18158step0Labels = mixedMoment B raw18158step1 raw18158step1Labels := by
      have ha : raw18158step1 = (fun i j => raw18158step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18158step1 raw18158step0; decide +kernel
      have hl : raw18158step1Labels = raw18158step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18158step0 raw18158step0Labels permutation149 permutation2
    mixedMoment B raw18158step1 raw18158step1Labels = mixedMoment B raw18158step2 raw18158step2Labels := by
      have ha : raw18158step2 = -raw18158step1 := by apply Matrix.ext; change ∀ i j, raw18158step2 i j = -(raw18158step1 i j); unfold raw18158step2 raw18158step1; decide +kernel
      have hl : raw18158step2Labels = raw18158step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw18159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw18159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18159step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18159step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18159step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18159 raw18159Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw18159 raw18159Labels = mixedMoment B raw18159step0 raw18159step0Labels := by
      have hz : ∀ j, raw18159 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18159step0 = (fun i j => raw18159 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18159step0 raw18159; decide +kernel
      have hl : raw18159step0Labels = raw18159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18159 raw18159Labels permutation520 hz
    mixedMoment B raw18159step0 raw18159step0Labels = mixedMoment B raw18159step1 raw18159step1Labels := by
      have hz : ∀ j, raw18159step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18159step1 = (fun i j => raw18159step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18159step1 raw18159step0; decide +kernel
      have hl : raw18159step1Labels = raw18159step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18159step0 raw18159step0Labels permutation80 hz
    mixedMoment B raw18159step1 raw18159step1Labels = mixedMoment B raw18159step2 raw18159step2Labels := by
      have ha : raw18159step2 = (fun i j => raw18159step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18159step2 raw18159step1; decide +kernel
      have hl : raw18159step2Labels = raw18159step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18159step1 raw18159step1Labels permutation31 permutation2
    mixedMoment B raw18159step2 raw18159step2Labels = mixedMoment B raw18159step3 raw18159step3Labels := by
      have ha : raw18159step3 = -raw18159step2 := by apply Matrix.ext; change ∀ i j, raw18159step3 i j = -(raw18159step2 i j); unfold raw18159step3 raw18159step2; decide +kernel
      have hl : raw18159step3Labels = raw18159step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw18160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18160step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18160step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18160step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw18160step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18160 raw18160Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw18160 raw18160Labels = mixedMoment B raw18160step0 raw18160step0Labels := by
      have hz : ∀ j, raw18160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18160step0 = (fun i j => raw18160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18160step0 raw18160; decide +kernel
      have hl : raw18160step0Labels = raw18160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18160 raw18160Labels permutation346 hz
    mixedMoment B raw18160step0 raw18160step0Labels = mixedMoment B raw18160step1 raw18160step1Labels := by
      have ha : raw18160step1 = (fun i j => raw18160step0 (permutation74 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18160step1 raw18160step0; decide +kernel
      have hl : raw18160step1Labels = raw18160step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18160step0 raw18160step0Labels permutation74 permutation5
    mixedMoment B raw18160step1 raw18160step1Labels = mixedMoment B raw18160step2 raw18160step2Labels := by
      have ha : raw18160step2 = -raw18160step1 := by apply Matrix.ext; change ∀ i j, raw18160step2 i j = -(raw18160step1 i j); unfold raw18160step2 raw18160step1; decide +kernel
      have hl : raw18160step2Labels = raw18160step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18160step2 raw18160step2Labels = mixedMoment B raw18160step3 raw18160step3Labels := by
      have ha : raw18160step3 = raw18160step2 := by apply Matrix.ext; unfold raw18160step3 raw18160step2; decide +kernel
      have hl : raw18160step2Labels = labelEmbedding1 ∘ raw18160step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18160step2 raw18160step2Labels raw18160step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw18161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18161step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18161 raw18161Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw18161 raw18161Labels = mixedMoment B raw18161step0 raw18161step0Labels := by
      have ha : raw18161step0 = (fun i j => raw18161 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18161step0 raw18161; decide +kernel
      have hl : raw18161step0Labels = raw18161Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18161 raw18161Labels permutation620 permutation7
    mixedMoment B raw18161step0 raw18161step0Labels = mixedMoment B raw18161step1 raw18161step1Labels := by
      have ha : raw18161step1 = raw18161step0 := by apply Matrix.ext; unfold raw18161step1 raw18161step0; decide +kernel
      have hl : raw18161step0Labels = labelEmbedding1 ∘ raw18161step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18161step0 raw18161step0Labels raw18161step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw18162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw18162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18162 raw18162Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw18162 raw18162Labels = mixedMoment B raw18162step0 raw18162step0Labels := by
      have hz : ∀ j, raw18162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18162step0 = (fun i j => raw18162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18162step0 raw18162; decide +kernel
      have hl : raw18162step0Labels = raw18162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18162 raw18162Labels permutation346 hz
    mixedMoment B raw18162step0 raw18162step0Labels = mixedMoment B raw18162step1 raw18162step1Labels := by
      have ha : raw18162step1 = (fun i j => raw18162step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18162step1 raw18162step0; decide +kernel
      have hl : raw18162step1Labels = raw18162step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18162step0 raw18162step0Labels permutation139 permutation7
    mixedMoment B raw18162step1 raw18162step1Labels = mixedMoment B raw18162step2 raw18162step2Labels := by
      have ha : raw18162step2 = raw18162step1 := by apply Matrix.ext; unfold raw18162step2 raw18162step1; decide +kernel
      have hl : raw18162step1Labels = labelEmbedding1 ∘ raw18162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18162step1 raw18162step1Labels raw18162step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw18163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18163step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18163step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18163step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18163step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18163step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18163 raw18163Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw18163 raw18163Labels = mixedMoment B raw18163step0 raw18163step0Labels := by
      have hz : ∀ j, raw18163 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18163step0 = (fun i j => raw18163 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18163step0 raw18163; decide +kernel
      have hl : raw18163step0Labels = raw18163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18163 raw18163Labels permutation520 hz
    mixedMoment B raw18163step0 raw18163step0Labels = mixedMoment B raw18163step1 raw18163step1Labels := by
      have hz : ∀ j, raw18163step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18163step1 = (fun i j => raw18163step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18163step1 raw18163step0; decide +kernel
      have hl : raw18163step1Labels = raw18163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18163step0 raw18163step0Labels permutation80 hz
    mixedMoment B raw18163step1 raw18163step1Labels = mixedMoment B raw18163step2 raw18163step2Labels := by
      have ha : raw18163step2 = (fun i j => raw18163step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18163step2 raw18163step1; decide +kernel
      have hl : raw18163step2Labels = raw18163step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18163step1 raw18163step1Labels permutation29 permutation7
    mixedMoment B raw18163step2 raw18163step2Labels = mixedMoment B raw18163step3 raw18163step3Labels := by
      have ha : raw18163step3 = raw18163step2 := by apply Matrix.ext; unfold raw18163step3 raw18163step2; decide +kernel
      have hl : raw18163step2Labels = labelEmbedding1 ∘ raw18163step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18163step2 raw18163step2Labels raw18163step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw18164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18164step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18164step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18164step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18164step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18164 raw18164Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw18164 raw18164Labels = mixedMoment B raw18164step0 raw18164step0Labels := by
      have hz : ∀ j, raw18164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18164step0 = (fun i j => raw18164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18164step0 raw18164; decide +kernel
      have hl : raw18164step0Labels = raw18164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18164 raw18164Labels permutation346 hz
    mixedMoment B raw18164step0 raw18164step0Labels = mixedMoment B raw18164step1 raw18164step1Labels := by
      have ha : raw18164step1 = (fun i j => raw18164step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18164step1 raw18164step0; decide +kernel
      have hl : raw18164step1Labels = raw18164step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18164step0 raw18164step0Labels permutation40 permutation7
    mixedMoment B raw18164step1 raw18164step1Labels = mixedMoment B raw18164step2 raw18164step2Labels := by
      have ha : raw18164step2 = -raw18164step1 := by apply Matrix.ext; change ∀ i j, raw18164step2 i j = -(raw18164step1 i j); unfold raw18164step2 raw18164step1; decide +kernel
      have hl : raw18164step2Labels = raw18164step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18164step2 raw18164step2Labels = mixedMoment B raw18164step3 raw18164step3Labels := by
      have ha : raw18164step3 = raw18164step2 := by apply Matrix.ext; unfold raw18164step3 raw18164step2; decide +kernel
      have hl : raw18164step2Labels = labelEmbedding1 ∘ raw18164step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18164step2 raw18164step2Labels raw18164step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw18165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18165step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18165step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18165step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18165step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18165 raw18165Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw18165 raw18165Labels = mixedMoment B raw18165step0 raw18165step0Labels := by
      have hz : ∀ j, raw18165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18165step0 = (fun i j => raw18165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18165step0 raw18165; decide +kernel
      have hl : raw18165step0Labels = raw18165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18165 raw18165Labels permutation346 hz
    mixedMoment B raw18165step0 raw18165step0Labels = mixedMoment B raw18165step1 raw18165step1Labels := by
      have ha : raw18165step1 = (fun i j => raw18165step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18165step1 raw18165step0; decide +kernel
      have hl : raw18165step1Labels = raw18165step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18165step0 raw18165step0Labels permutation40 permutation7
    mixedMoment B raw18165step1 raw18165step1Labels = mixedMoment B raw18165step2 raw18165step2Labels := by
      have ha : raw18165step2 = -raw18165step1 := by apply Matrix.ext; change ∀ i j, raw18165step2 i j = -(raw18165step1 i j); unfold raw18165step2 raw18165step1; decide +kernel
      have hl : raw18165step2Labels = raw18165step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18165step2 raw18165step2Labels = mixedMoment B raw18165step3 raw18165step3Labels := by
      have ha : raw18165step3 = raw18165step2 := by apply Matrix.ext; unfold raw18165step3 raw18165step2; decide +kernel
      have hl : raw18165step2Labels = labelEmbedding1 ∘ raw18165step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18165step2 raw18165step2Labels raw18165step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw18166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18166 raw18166Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw18166 raw18166Labels = mixedMoment B raw18166step0 raw18166step0Labels := by
      have ha : raw18166step0 = (fun i j => raw18166 (permutation285 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18166step0 raw18166; decide +kernel
      have hl : raw18166step0Labels = raw18166Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18166 raw18166Labels permutation285 permutation5
    mixedMoment B raw18166step0 raw18166step0Labels = mixedMoment B raw18166step1 raw18166step1Labels := by
      have ha : raw18166step1 = -raw18166step0 := by apply Matrix.ext; change ∀ i j, raw18166step1 i j = -(raw18166step0 i j); unfold raw18166step1 raw18166step0; decide +kernel
      have hl : raw18166step1Labels = raw18166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18166step1 raw18166step1Labels = mixedMoment B raw18166step2 raw18166step2Labels := by
      have ha : raw18166step2 = raw18166step1 := by apply Matrix.ext; unfold raw18166step2 raw18166step1; decide +kernel
      have hl : raw18166step1Labels = labelEmbedding1 ∘ raw18166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18166step1 raw18166step1Labels raw18166step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw18167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18167step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18167 raw18167Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw18167 raw18167Labels = mixedMoment B raw18167step0 raw18167step0Labels := by
      have ha : raw18167step0 = (fun i j => raw18167 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18167step0 raw18167; decide +kernel
      have hl : raw18167step0Labels = raw18167Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18167 raw18167Labels permutation208 permutation7
    mixedMoment B raw18167step0 raw18167step0Labels = mixedMoment B raw18167step1 raw18167step1Labels := by
      have ha : raw18167step1 = -raw18167step0 := by apply Matrix.ext; change ∀ i j, raw18167step1 i j = -(raw18167step0 i j); unfold raw18167step1 raw18167step0; decide +kernel
      have hl : raw18167step1Labels = raw18167step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18167step1 raw18167step1Labels = mixedMoment B raw18167step2 raw18167step2Labels := by
      have ha : raw18167step2 = raw18167step1 := by apply Matrix.ext; unfold raw18167step2 raw18167step1; decide +kernel
      have hl : raw18167step1Labels = labelEmbedding1 ∘ raw18167step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18167step1 raw18167step1Labels raw18167step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw18168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw18168step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18168step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18168step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18168step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18168 raw18168Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw18168 raw18168Labels = mixedMoment B raw18168step0 raw18168step0Labels := by
      have hz : ∀ j, raw18168 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18168step0 = (fun i j => raw18168 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18168step0 raw18168; decide +kernel
      have hl : raw18168step0Labels = raw18168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18168 raw18168Labels permutation520 hz
    mixedMoment B raw18168step0 raw18168step0Labels = mixedMoment B raw18168step1 raw18168step1Labels := by
      have ha : raw18168step1 = (fun i j => raw18168step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18168step1 raw18168step0; decide +kernel
      have hl : raw18168step1Labels = raw18168step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18168step0 raw18168step0Labels permutation46 permutation7
    mixedMoment B raw18168step1 raw18168step1Labels = mixedMoment B raw18168step2 raw18168step2Labels := by
      have ha : raw18168step2 = -raw18168step1 := by apply Matrix.ext; change ∀ i j, raw18168step2 i j = -(raw18168step1 i j); unfold raw18168step2 raw18168step1; decide +kernel
      have hl : raw18168step2Labels = raw18168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18168step2 raw18168step2Labels = mixedMoment B raw18168step3 raw18168step3Labels := by
      have ha : raw18168step3 = raw18168step2 := by apply Matrix.ext; unfold raw18168step3 raw18168step2; decide +kernel
      have hl : raw18168step2Labels = labelEmbedding1 ∘ raw18168step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18168step2 raw18168step2Labels raw18168step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw18169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18169step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18169step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18169 raw18169Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw18169 raw18169Labels = mixedMoment B raw18169step0 raw18169step0Labels := by
      have ha : raw18169step0 = (fun i j => raw18169 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18169step0 raw18169; decide +kernel
      have hl : raw18169step0Labels = raw18169Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18169 raw18169Labels permutation208 permutation7
    mixedMoment B raw18169step0 raw18169step0Labels = mixedMoment B raw18169step1 raw18169step1Labels := by
      have ha : raw18169step1 = -raw18169step0 := by apply Matrix.ext; change ∀ i j, raw18169step1 i j = -(raw18169step0 i j); unfold raw18169step1 raw18169step0; decide +kernel
      have hl : raw18169step1Labels = raw18169step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18169step1 raw18169step1Labels = mixedMoment B raw18169step2 raw18169step2Labels := by
      have ha : raw18169step2 = raw18169step1 := by apply Matrix.ext; unfold raw18169step2 raw18169step1; decide +kernel
      have hl : raw18169step1Labels = labelEmbedding1 ∘ raw18169step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18169step1 raw18169step1Labels raw18169step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw18170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18170step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18170step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18170 raw18170Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw18170 raw18170Labels = mixedMoment B raw18170step0 raw18170step0Labels := by
      have hz : ∀ j, raw18170 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18170step0 = (fun i j => raw18170 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18170step0 raw18170; decide +kernel
      have hl : raw18170step0Labels = raw18170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18170 raw18170Labels permutation346 hz
    mixedMoment B raw18170step0 raw18170step0Labels = mixedMoment B raw18170step1 raw18170step1Labels := by
      have ha : raw18170step1 = (fun i j => raw18170step0 (permutation61 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18170step1 raw18170step0; decide +kernel
      have hl : raw18170step1Labels = raw18170step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18170step0 raw18170step0Labels permutation61 permutation5
    mixedMoment B raw18170step1 raw18170step1Labels = mixedMoment B raw18170step2 raw18170step2Labels := by
      have ha : raw18170step2 = -raw18170step1 := by apply Matrix.ext; change ∀ i j, raw18170step2 i j = -(raw18170step1 i j); unfold raw18170step2 raw18170step1; decide +kernel
      have hl : raw18170step2Labels = raw18170step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18170step2 raw18170step2Labels = mixedMoment B raw18170step3 raw18170step3Labels := by
      have ha : raw18170step3 = raw18170step2 := by apply Matrix.ext; unfold raw18170step3 raw18170step2; decide +kernel
      have hl : raw18170step2Labels = labelEmbedding1 ∘ raw18170step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18170step2 raw18170step2Labels raw18170step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw18171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18171 raw18171Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw18171 raw18171Labels = mixedMoment B raw18171step0 raw18171step0Labels := by
      have ha : raw18171step0 = (fun i j => raw18171 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18171step0 raw18171; decide +kernel
      have hl : raw18171step0Labels = raw18171Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18171 raw18171Labels permutation620 permutation7
    mixedMoment B raw18171step0 raw18171step0Labels = mixedMoment B raw18171step1 raw18171step1Labels := by
      have ha : raw18171step1 = raw18171step0 := by apply Matrix.ext; unfold raw18171step1 raw18171step0; decide +kernel
      have hl : raw18171step0Labels = labelEmbedding1 ∘ raw18171step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18171step0 raw18171step0Labels raw18171step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3870 node3870Labels := by rfl

def raw18172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw18172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18172step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18172step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18172step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18172step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18172step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18172 raw18172Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw18172 raw18172Labels = mixedMoment B raw18172step0 raw18172step0Labels := by
      have hz : ∀ j, raw18172 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18172step0 = (fun i j => raw18172 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18172step0 raw18172; decide +kernel
      have hl : raw18172step0Labels = raw18172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18172 raw18172Labels permutation520 hz
    mixedMoment B raw18172step0 raw18172step0Labels = mixedMoment B raw18172step1 raw18172step1Labels := by
      have hz : ∀ j, raw18172step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18172step1 = (fun i j => raw18172step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18172step1 raw18172step0; decide +kernel
      have hl : raw18172step1Labels = raw18172step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18172step0 raw18172step0Labels permutation80 hz
    mixedMoment B raw18172step1 raw18172step1Labels = mixedMoment B raw18172step2 raw18172step2Labels := by
      have ha : raw18172step2 = (fun i j => raw18172step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18172step2 raw18172step1; decide +kernel
      have hl : raw18172step2Labels = raw18172step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18172step1 raw18172step1Labels permutation29 permutation7
    mixedMoment B raw18172step2 raw18172step2Labels = mixedMoment B raw18172step3 raw18172step3Labels := by
      have ha : raw18172step3 = raw18172step2 := by apply Matrix.ext; unfold raw18172step3 raw18172step2; decide +kernel
      have hl : raw18172step2Labels = labelEmbedding1 ∘ raw18172step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18172step2 raw18172step2Labels raw18172step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw18173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18173step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18173step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18173step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18173step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18173 raw18173Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw18173 raw18173Labels = mixedMoment B raw18173step0 raw18173step0Labels := by
      have hz : ∀ j, raw18173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18173step0 = (fun i j => raw18173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18173step0 raw18173; decide +kernel
      have hl : raw18173step0Labels = raw18173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18173 raw18173Labels permutation346 hz
    mixedMoment B raw18173step0 raw18173step0Labels = mixedMoment B raw18173step1 raw18173step1Labels := by
      have ha : raw18173step1 = (fun i j => raw18173step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18173step1 raw18173step0; decide +kernel
      have hl : raw18173step1Labels = raw18173step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18173step0 raw18173step0Labels permutation40 permutation7
    mixedMoment B raw18173step1 raw18173step1Labels = mixedMoment B raw18173step2 raw18173step2Labels := by
      have ha : raw18173step2 = -raw18173step1 := by apply Matrix.ext; change ∀ i j, raw18173step2 i j = -(raw18173step1 i j); unfold raw18173step2 raw18173step1; decide +kernel
      have hl : raw18173step2Labels = raw18173step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18173step2 raw18173step2Labels = mixedMoment B raw18173step3 raw18173step3Labels := by
      have ha : raw18173step3 = raw18173step2 := by apply Matrix.ext; unfold raw18173step3 raw18173step2; decide +kernel
      have hl : raw18173step2Labels = labelEmbedding1 ∘ raw18173step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18173step2 raw18173step2Labels raw18173step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw18174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18174step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18174step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18174step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18174step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18174 raw18174Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw18174 raw18174Labels = mixedMoment B raw18174step0 raw18174step0Labels := by
      have hz : ∀ j, raw18174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18174step0 = (fun i j => raw18174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18174step0 raw18174; decide +kernel
      have hl : raw18174step0Labels = raw18174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18174 raw18174Labels permutation346 hz
    mixedMoment B raw18174step0 raw18174step0Labels = mixedMoment B raw18174step1 raw18174step1Labels := by
      have ha : raw18174step1 = (fun i j => raw18174step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18174step1 raw18174step0; decide +kernel
      have hl : raw18174step1Labels = raw18174step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18174step0 raw18174step0Labels permutation60 permutation5
    mixedMoment B raw18174step1 raw18174step1Labels = mixedMoment B raw18174step2 raw18174step2Labels := by
      have ha : raw18174step2 = -raw18174step1 := by apply Matrix.ext; change ∀ i j, raw18174step2 i j = -(raw18174step1 i j); unfold raw18174step2 raw18174step1; decide +kernel
      have hl : raw18174step2Labels = raw18174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18174step2 raw18174step2Labels = mixedMoment B raw18174step3 raw18174step3Labels := by
      have ha : raw18174step3 = raw18174step2 := by apply Matrix.ext; unfold raw18174step3 raw18174step2; decide +kernel
      have hl : raw18174step2Labels = labelEmbedding1 ∘ raw18174step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18174step2 raw18174step2Labels raw18174step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw18175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18175step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18175 raw18175Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw18175 raw18175Labels = mixedMoment B raw18175step0 raw18175step0Labels := by
      have ha : raw18175step0 = (fun i j => raw18175 (permutation564 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18175step0 raw18175; decide +kernel
      have hl : raw18175step0Labels = raw18175Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18175 raw18175Labels permutation564 permutation5
    mixedMoment B raw18175step0 raw18175step0Labels = mixedMoment B raw18175step1 raw18175step1Labels := by
      have ha : raw18175step1 = raw18175step0 := by apply Matrix.ext; unfold raw18175step1 raw18175step0; decide +kernel
      have hl : raw18175step0Labels = labelEmbedding1 ∘ raw18175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18175step0 raw18175step0Labels raw18175step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
