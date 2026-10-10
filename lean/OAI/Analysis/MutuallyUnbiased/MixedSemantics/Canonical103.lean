import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw13184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13184 raw13184Labels = mixedMoment B node3282 node3282Labels := by
  calc
    mixedMoment B raw13184 raw13184Labels = mixedMoment B raw13184step0 raw13184step0Labels := by
      have ha : raw13184step0 = (fun i j => raw13184 (permutation155 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13184step0 raw13184; decide +kernel
      have hl : raw13184step0Labels = raw13184Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13184 raw13184Labels permutation155 permutation5
    mixedMoment B raw13184step0 raw13184step0Labels = mixedMoment B raw13184step1 raw13184step1Labels := by
      have ha : raw13184step1 = -raw13184step0 := by apply Matrix.ext; change ∀ i j, raw13184step1 i j = -(raw13184step0 i j); unfold raw13184step1 raw13184step0; decide +kernel
      have hl : raw13184step1Labels = raw13184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13184step1 raw13184step1Labels = mixedMoment B raw13184step2 raw13184step2Labels := by
      have ha : raw13184step2 = raw13184step1 := by apply Matrix.ext; unfold raw13184step2 raw13184step1; decide +kernel
      have hl : raw13184step1Labels = labelEmbedding1 ∘ raw13184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13184step1 raw13184step1Labels raw13184step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3282 node3282Labels := by rfl

def raw13185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw13185step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13185step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13185 raw13185Labels = mixedMoment B node3568 node3568Labels := by
  calc
    mixedMoment B raw13185 raw13185Labels = mixedMoment B raw13185step0 raw13185step0Labels := by
      have ha : raw13185step0 = (fun i j => raw13185 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13185step0 raw13185; decide +kernel
      have hl : raw13185step0Labels = raw13185Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13185 raw13185Labels permutation212 permutation7
    mixedMoment B raw13185step0 raw13185step0Labels = mixedMoment B raw13185step1 raw13185step1Labels := by
      have ha : raw13185step1 = -raw13185step0 := by apply Matrix.ext; change ∀ i j, raw13185step1 i j = -(raw13185step0 i j); unfold raw13185step1 raw13185step0; decide +kernel
      have hl : raw13185step1Labels = raw13185step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13185step1 raw13185step1Labels = mixedMoment B raw13185step2 raw13185step2Labels := by
      have ha : raw13185step2 = raw13185step1 := by apply Matrix.ext; unfold raw13185step2 raw13185step1; decide +kernel
      have hl : raw13185step1Labels = labelEmbedding1 ∘ raw13185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13185step1 raw13185step1Labels raw13185step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3568 node3568Labels := by rfl

def raw13186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw13186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13186step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13186step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13186 raw13186Labels = mixedMoment B node3568 node3568Labels := by
  calc
    mixedMoment B raw13186 raw13186Labels = mixedMoment B raw13186step0 raw13186step0Labels := by
      have ha : raw13186step0 = (fun i j => raw13186 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13186step0 raw13186; decide +kernel
      have hl : raw13186step0Labels = raw13186Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13186 raw13186Labels permutation214 permutation7
    mixedMoment B raw13186step0 raw13186step0Labels = mixedMoment B raw13186step1 raw13186step1Labels := by
      have ha : raw13186step1 = -raw13186step0 := by apply Matrix.ext; change ∀ i j, raw13186step1 i j = -(raw13186step0 i j); unfold raw13186step1 raw13186step0; decide +kernel
      have hl : raw13186step1Labels = raw13186step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13186step1 raw13186step1Labels = mixedMoment B raw13186step2 raw13186step2Labels := by
      have ha : raw13186step2 = raw13186step1 := by apply Matrix.ext; unfold raw13186step2 raw13186step1; decide +kernel
      have hl : raw13186step1Labels = labelEmbedding1 ∘ raw13186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13186step1 raw13186step1Labels raw13186step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3568 node3568Labels := by rfl

def raw13187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13187 raw13187Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw13187 raw13187Labels = mixedMoment B raw13187step0 raw13187step0Labels := by
      have ha : raw13187step0 = (fun i j => raw13187 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13187step0 raw13187; decide +kernel
      have hl : raw13187step0Labels = raw13187Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13187 raw13187Labels permutation212 permutation7
    mixedMoment B raw13187step0 raw13187step0Labels = mixedMoment B raw13187step1 raw13187step1Labels := by
      have ha : raw13187step1 = -raw13187step0 := by apply Matrix.ext; change ∀ i j, raw13187step1 i j = -(raw13187step0 i j); unfold raw13187step1 raw13187step0; decide +kernel
      have hl : raw13187step1Labels = raw13187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13187step1 raw13187step1Labels = mixedMoment B raw13187step2 raw13187step2Labels := by
      have ha : raw13187step2 = raw13187step1 := by apply Matrix.ext; unfold raw13187step2 raw13187step1; decide +kernel
      have hl : raw13187step1Labels = labelEmbedding1 ∘ raw13187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13187step1 raw13187step1Labels raw13187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

def raw13188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw13188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13188 raw13188Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw13188 raw13188Labels = mixedMoment B raw13188step0 raw13188step0Labels := by
      have hz : ∀ j, raw13188 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13188step0 = (fun i j => raw13188 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13188step0 raw13188; decide +kernel
      have hl : raw13188step0Labels = raw13188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13188 raw13188Labels permutation520 hz
    mixedMoment B raw13188step0 raw13188step0Labels = mixedMoment B raw13188step1 raw13188step1Labels := by
      have ha : raw13188step1 = (fun i j => raw13188step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13188step1 raw13188step0; decide +kernel
      have hl : raw13188step1Labels = raw13188step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13188step0 raw13188step0Labels permutation44 permutation7
    mixedMoment B raw13188step1 raw13188step1Labels = mixedMoment B raw13188step2 raw13188step2Labels := by
      have ha : raw13188step2 = -raw13188step1 := by apply Matrix.ext; change ∀ i j, raw13188step2 i j = -(raw13188step1 i j); unfold raw13188step2 raw13188step1; decide +kernel
      have hl : raw13188step2Labels = raw13188step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13188step2 raw13188step2Labels = mixedMoment B raw13188step3 raw13188step3Labels := by
      have ha : raw13188step3 = raw13188step2 := by apply Matrix.ext; unfold raw13188step3 raw13188step2; decide +kernel
      have hl : raw13188step2Labels = labelEmbedding1 ∘ raw13188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13188step2 raw13188step2Labels raw13188step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw13189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13189Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13189 raw13189Labels = mixedMoment B node2750 node2750Labels := by
  calc
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw13190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13190 raw13190Labels = mixedMoment B node3880 node3880Labels := by
  calc
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw13191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13191 raw13191Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw13191 raw13191Labels = mixedMoment B raw13191step0 raw13191step0Labels := by
      have ha : raw13191step0 = (fun i j => raw13191 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13191step0 raw13191; decide +kernel
      have hl : raw13191step0Labels = raw13191Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13191 raw13191Labels permutation176 permutation2
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw13192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13192Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw13192step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13192 raw13192Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw13192 raw13192Labels = mixedMoment B raw13192step0 raw13192step0Labels := by
      have ha : raw13192step0 = (fun i j => raw13192 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13192step0 raw13192; decide +kernel
      have hl : raw13192step0Labels = raw13192Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13192 raw13192Labels permutation200 permutation2
    _ = mixedMoment B node3901 node3901Labels := by rfl

def raw13193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13193 raw13193Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13193 raw13193Labels = mixedMoment B raw13193step0 raw13193step0Labels := by
      have hz : ∀ j, raw13193 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13193step0 = (fun i j => raw13193 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13193step0 raw13193; decide +kernel
      have hl : raw13193step0Labels = raw13193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13193 raw13193Labels permutation520 hz
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw13194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw13194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13194 raw13194Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw13194 raw13194Labels = mixedMoment B raw13194step0 raw13194step0Labels := by
      have ha : raw13194step0 = (fun i j => raw13194 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13194step0 raw13194; decide +kernel
      have hl : raw13194step0Labels = raw13194Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13194 raw13194Labels permutation156 permutation2
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw13195 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![0, 0], ![1, -1]]
def raw13195Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13195step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]
def raw13195step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13195step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw13195step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical13195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13195 raw13195Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13195 raw13195Labels = mixedMoment B raw13195step0 raw13195step0Labels := by
      have hz : ∀ j, raw13195 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13195step0 = (fun i j => raw13195 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13195step0 raw13195; decide +kernel
      have hl : raw13195step0Labels = raw13195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13195 raw13195Labels permutation520 hz
    mixedMoment B raw13195step0 raw13195step0Labels = mixedMoment B raw13195step1 raw13195step1Labels := by
      have ha : raw13195step1 = (fun i j => raw13195step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13195step1 raw13195step0; decide +kernel
      have hl : raw13195step1Labels = raw13195step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13195step0 raw13195step0Labels permutation44 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw13196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13196 raw13196Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw13196 raw13196Labels = mixedMoment B raw13196step0 raw13196step0Labels := by
      have ha : raw13196step0 = (fun i j => raw13196 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13196step0 raw13196; decide +kernel
      have hl : raw13196step0Labels = raw13196Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13196 raw13196Labels permutation184 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw13197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13197 raw13197Labels = mixedMoment B node1260 node1260Labels := by
  calc
    mixedMoment B raw13197 raw13197Labels = mixedMoment B raw13197step0 raw13197step0Labels := by
      have ha : raw13197step0 = (fun i j => raw13197 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13197step0 raw13197; decide +kernel
      have hl : raw13197step0Labels = raw13197Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13197 raw13197Labels permutation160 permutation2
    _ = mixedMoment B node1260 node1260Labels := by rfl

def raw13198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw13198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13198 raw13198Labels = mixedMoment B node1250 node1250Labels := by
  calc
    mixedMoment B raw13198 raw13198Labels = mixedMoment B raw13198step0 raw13198step0Labels := by
      have ha : raw13198step0 = (fun i j => raw13198 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13198step0 raw13198; decide +kernel
      have hl : raw13198step0Labels = raw13198Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13198 raw13198Labels permutation155 permutation2
    _ = mixedMoment B node1250 node1250Labels := by rfl

def raw13199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw13199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13199 raw13199Labels = mixedMoment B node1248 node1248Labels := by
  calc
    mixedMoment B raw13199 raw13199Labels = mixedMoment B raw13199step0 raw13199step0Labels := by
      have ha : raw13199step0 = (fun i j => raw13199 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13199step0 raw13199; decide +kernel
      have hl : raw13199step0Labels = raw13199Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13199 raw13199Labels permutation153 permutation2
    _ = mixedMoment B node1248 node1248Labels := by rfl

def raw13200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13200 raw13200Labels = mixedMoment B node1247 node1247Labels := by
  calc
    _ = mixedMoment B node1247 node1247Labels := by rfl

def raw13201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13201 raw13201Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw13201 raw13201Labels = mixedMoment B raw13201step0 raw13201step0Labels := by
      have ha : raw13201step0 = (fun i j => raw13201 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13201step0 raw13201; decide +kernel
      have hl : raw13201step0Labels = raw13201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13201 raw13201Labels permutation184 permutation2
    _ = mixedMoment B node2631 node2631Labels := by rfl

def raw13202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13202 raw13202Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw13202 raw13202Labels = mixedMoment B raw13202step0 raw13202step0Labels := by
      have ha : raw13202step0 = (fun i j => raw13202 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13202step0 raw13202; decide +kernel
      have hl : raw13202step0Labels = raw13202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13202 raw13202Labels permutation208 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw13203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13203 raw13203Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw13203 raw13203Labels = mixedMoment B raw13203step0 raw13203step0Labels := by
      have hz : ∀ j, raw13203 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13203step0 = (fun i j => raw13203 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13203step0 raw13203; decide +kernel
      have hl : raw13203step0Labels = raw13203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13203 raw13203Labels permutation520 hz
    mixedMoment B raw13203step0 raw13203step0Labels = mixedMoment B raw13203step1 raw13203step1Labels := by
      have ha : raw13203step1 = (fun i j => raw13203step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13203step1 raw13203step0; decide +kernel
      have hl : raw13203step1Labels = raw13203step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13203step0 raw13203step0Labels permutation40 permutation2
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw13204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13204 raw13204Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw13204 raw13204Labels = mixedMoment B raw13204step0 raw13204step0Labels := by
      have ha : raw13204step0 = (fun i j => raw13204 (permutation197 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13204step0 raw13204; decide +kernel
      have hl : raw13204step0Labels = raw13204Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13204 raw13204Labels permutation197 permutation2
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw13205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13205 raw13205Labels = mixedMoment B node2631 node2631Labels := by
  calc
    mixedMoment B raw13205 raw13205Labels = mixedMoment B raw13205step0 raw13205step0Labels := by
      have ha : raw13205step0 = (fun i j => raw13205 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13205step0 raw13205; decide +kernel
      have hl : raw13205step0Labels = raw13205Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13205 raw13205Labels permutation160 permutation2
    _ = mixedMoment B node2631 node2631Labels := by rfl

def raw13206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw13206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13206 raw13206Labels = mixedMoment B node2625 node2625Labels := by
  calc
    mixedMoment B raw13206 raw13206Labels = mixedMoment B raw13206step0 raw13206step0Labels := by
      have ha : raw13206step0 = (fun i j => raw13206 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13206step0 raw13206; decide +kernel
      have hl : raw13206step0Labels = raw13206Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13206 raw13206Labels permutation155 permutation2
    _ = mixedMoment B node2625 node2625Labels := by rfl

def raw13207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw13207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13207 raw13207Labels = mixedMoment B node2623 node2623Labels := by
  calc
    mixedMoment B raw13207 raw13207Labels = mixedMoment B raw13207step0 raw13207step0Labels := by
      have ha : raw13207step0 = (fun i j => raw13207 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13207step0 raw13207; decide +kernel
      have hl : raw13207step0Labels = raw13207Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13207 raw13207Labels permutation153 permutation2
    _ = mixedMoment B node2623 node2623Labels := by rfl

def raw13208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13208 raw13208Labels = mixedMoment B node2622 node2622Labels := by
  calc
    _ = mixedMoment B node2622 node2622Labels := by rfl

def raw13209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13209 raw13209Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw13209 raw13209Labels = mixedMoment B raw13209step0 raw13209step0Labels := by
      have ha : raw13209step0 = (fun i j => raw13209 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13209step0 raw13209; decide +kernel
      have hl : raw13209step0Labels = raw13209Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13209 raw13209Labels permutation157 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw13210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13210 raw13210Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw13210 raw13210Labels = mixedMoment B raw13210step0 raw13210step0Labels := by
      have ha : raw13210step0 = (fun i j => raw13210 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13210step0 raw13210; decide +kernel
      have hl : raw13210step0Labels = raw13210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13210 raw13210Labels permutation181 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw13211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13211step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13211 raw13211Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw13211 raw13211Labels = mixedMoment B raw13211step0 raw13211step0Labels := by
      have ha : raw13211step0 = (fun i j => raw13211 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13211step0 raw13211; decide +kernel
      have hl : raw13211step0Labels = raw13211Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13211 raw13211Labels permutation499 permutation6
    mixedMoment B raw13211step0 raw13211step0Labels = mixedMoment B raw13211step1 raw13211step1Labels := by
      have ha : raw13211step1 = raw13211step0 := by apply Matrix.ext; unfold raw13211step1 raw13211step0; decide +kernel
      have hl : raw13211step0Labels = labelEmbedding9 ∘ raw13211step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13211step0 raw13211step0Labels raw13211step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw13212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13212step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13212 raw13212Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw13212 raw13212Labels = mixedMoment B raw13212step0 raw13212step0Labels := by
      have ha : raw13212step0 = (fun i j => raw13212 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13212step0 raw13212; decide +kernel
      have hl : raw13212step0Labels = raw13212Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13212 raw13212Labels permutation499 permutation6
    mixedMoment B raw13212step0 raw13212step0Labels = mixedMoment B raw13212step1 raw13212step1Labels := by
      have ha : raw13212step1 = raw13212step0 := by apply Matrix.ext; unfold raw13212step1 raw13212step0; decide +kernel
      have hl : raw13212step0Labels = labelEmbedding9 ∘ raw13212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13212step0 raw13212step0Labels raw13212step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw13213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13213step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13213step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13213 raw13213Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw13213 raw13213Labels = mixedMoment B raw13213step0 raw13213step0Labels := by
      have hz : ∀ j, raw13213 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13213step0 = (fun i j => raw13213 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13213step0 raw13213; decide +kernel
      have hl : raw13213step0Labels = raw13213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13213 raw13213Labels permutation590 hz
    mixedMoment B raw13213step0 raw13213step0Labels = mixedMoment B raw13213step1 raw13213step1Labels := by
      have ha : raw13213step1 = (fun i j => raw13213step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13213step1 raw13213step0; decide +kernel
      have hl : raw13213step1Labels = raw13213step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13213step0 raw13213step0Labels permutation125 permutation7
    mixedMoment B raw13213step1 raw13213step1Labels = mixedMoment B raw13213step2 raw13213step2Labels := by
      have ha : raw13213step2 = raw13213step1 := by apply Matrix.ext; unfold raw13213step2 raw13213step1; decide +kernel
      have hl : raw13213step1Labels = labelEmbedding10 ∘ raw13213step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13213step1 raw13213step1Labels raw13213step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw13214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13214step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13214 raw13214Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw13214 raw13214Labels = mixedMoment B raw13214step0 raw13214step0Labels := by
      have ha : raw13214step0 = (fun i j => raw13214 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13214step0 raw13214; decide +kernel
      have hl : raw13214step0Labels = raw13214Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13214 raw13214Labels permutation185 permutation3
    mixedMoment B raw13214step0 raw13214step0Labels = mixedMoment B raw13214step1 raw13214step1Labels := by
      have ha : raw13214step1 = raw13214step0 := by apply Matrix.ext; unfold raw13214step1 raw13214step0; decide +kernel
      have hl : raw13214step0Labels = labelEmbedding6 ∘ raw13214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13214step0 raw13214step0Labels raw13214step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

def raw13215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13215step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13215 raw13215Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw13215 raw13215Labels = mixedMoment B raw13215step0 raw13215step0Labels := by
      have ha : raw13215step0 = (fun i j => raw13215 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13215step0 raw13215; decide +kernel
      have hl : raw13215step0Labels = raw13215Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13215 raw13215Labels permutation185 permutation3
    mixedMoment B raw13215step0 raw13215step0Labels = mixedMoment B raw13215step1 raw13215step1Labels := by
      have ha : raw13215step1 = raw13215step0 := by apply Matrix.ext; unfold raw13215step1 raw13215step0; decide +kernel
      have hl : raw13215step0Labels = labelEmbedding6 ∘ raw13215step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13215step0 raw13215step0Labels raw13215step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw13216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13216step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13216 raw13216Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw13216 raw13216Labels = mixedMoment B raw13216step0 raw13216step0Labels := by
      have ha : raw13216step0 = (fun i j => raw13216 (permutation209 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13216step0 raw13216; decide +kernel
      have hl : raw13216step0Labels = raw13216Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13216 raw13216Labels permutation209 permutation3
    mixedMoment B raw13216step0 raw13216step0Labels = mixedMoment B raw13216step1 raw13216step1Labels := by
      have ha : raw13216step1 = raw13216step0 := by apply Matrix.ext; unfold raw13216step1 raw13216step0; decide +kernel
      have hl : raw13216step0Labels = labelEmbedding6 ∘ raw13216step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13216step0 raw13216step0Labels raw13216step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw13217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13217step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13217 raw13217Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw13217 raw13217Labels = mixedMoment B raw13217step0 raw13217step0Labels := by
      have ha : raw13217step0 = (fun i j => raw13217 (permutation233 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13217step0 raw13217; decide +kernel
      have hl : raw13217step0Labels = raw13217Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13217 raw13217Labels permutation233 permutation3
    mixedMoment B raw13217step0 raw13217step0Labels = mixedMoment B raw13217step1 raw13217step1Labels := by
      have ha : raw13217step1 = raw13217step0 := by apply Matrix.ext; unfold raw13217step1 raw13217step0; decide +kernel
      have hl : raw13217step0Labels = labelEmbedding6 ∘ raw13217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13217step0 raw13217step0Labels raw13217step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw13218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13218step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13218step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13218 raw13218Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw13218 raw13218Labels = mixedMoment B raw13218step0 raw13218step0Labels := by
      have hz : ∀ j, raw13218 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13218step0 = (fun i j => raw13218 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13218step0 raw13218; decide +kernel
      have hl : raw13218step0Labels = raw13218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13218 raw13218Labels permutation590 hz
    mixedMoment B raw13218step0 raw13218step0Labels = mixedMoment B raw13218step1 raw13218step1Labels := by
      have ha : raw13218step1 = (fun i j => raw13218step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13218step1 raw13218step0; decide +kernel
      have hl : raw13218step1Labels = raw13218step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13218step0 raw13218step0Labels permutation41 permutation3
    mixedMoment B raw13218step1 raw13218step1Labels = mixedMoment B raw13218step2 raw13218step2Labels := by
      have ha : raw13218step2 = raw13218step1 := by apply Matrix.ext; unfold raw13218step2 raw13218step1; decide +kernel
      have hl : raw13218step1Labels = labelEmbedding6 ∘ raw13218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13218step1 raw13218step1Labels raw13218step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw13219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13219step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13219 raw13219Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw13219 raw13219Labels = mixedMoment B raw13219step0 raw13219step0Labels := by
      have ha : raw13219step0 = (fun i j => raw13219 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13219step0 raw13219; decide +kernel
      have hl : raw13219step0Labels = raw13219Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13219 raw13219Labels permutation161 permutation3
    mixedMoment B raw13219step0 raw13219step0Labels = mixedMoment B raw13219step1 raw13219step1Labels := by
      have ha : raw13219step1 = raw13219step0 := by apply Matrix.ext; unfold raw13219step1 raw13219step0; decide +kernel
      have hl : raw13219step0Labels = labelEmbedding6 ∘ raw13219step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13219step0 raw13219step0Labels raw13219step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

def raw13220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13220step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13220 raw13220Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw13220 raw13220Labels = mixedMoment B raw13220step0 raw13220step0Labels := by
      have ha : raw13220step0 = (fun i j => raw13220 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13220step0 raw13220; decide +kernel
      have hl : raw13220step0Labels = raw13220Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13220 raw13220Labels permutation161 permutation3
    mixedMoment B raw13220step0 raw13220step0Labels = mixedMoment B raw13220step1 raw13220step1Labels := by
      have ha : raw13220step1 = raw13220step0 := by apply Matrix.ext; unfold raw13220step1 raw13220step0; decide +kernel
      have hl : raw13220step0Labels = labelEmbedding6 ∘ raw13220step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13220step0 raw13220step0Labels raw13220step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw13221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13221step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13221step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13221 raw13221Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw13221 raw13221Labels = mixedMoment B raw13221step0 raw13221step0Labels := by
      have ha : raw13221step0 = (fun i j => raw13221 (permutation203 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13221step0 raw13221; decide +kernel
      have hl : raw13221step0Labels = raw13221Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13221 raw13221Labels permutation203 permutation3
    mixedMoment B raw13221step0 raw13221step0Labels = mixedMoment B raw13221step1 raw13221step1Labels := by
      have ha : raw13221step1 = raw13221step0 := by apply Matrix.ext; unfold raw13221step1 raw13221step0; decide +kernel
      have hl : raw13221step0Labels = labelEmbedding6 ∘ raw13221step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13221step0 raw13221step0Labels raw13221step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw13222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13222step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13222 raw13222Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw13222 raw13222Labels = mixedMoment B raw13222step0 raw13222step0Labels := by
      have ha : raw13222step0 = (fun i j => raw13222 (permutation227 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13222step0 raw13222; decide +kernel
      have hl : raw13222step0Labels = raw13222Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13222 raw13222Labels permutation227 permutation3
    mixedMoment B raw13222step0 raw13222step0Labels = mixedMoment B raw13222step1 raw13222step1Labels := by
      have ha : raw13222step1 = raw13222step0 := by apply Matrix.ext; unfold raw13222step1 raw13222step0; decide +kernel
      have hl : raw13222step0Labels = labelEmbedding6 ∘ raw13222step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13222step0 raw13222step0Labels raw13222step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw13223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13223step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13223 raw13223Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw13223 raw13223Labels = mixedMoment B raw13223step0 raw13223step0Labels := by
      have hz : ∀ j, raw13223 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13223step0 = (fun i j => raw13223 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13223step0 raw13223; decide +kernel
      have hl : raw13223step0Labels = raw13223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13223 raw13223Labels permutation590 hz
    mixedMoment B raw13223step0 raw13223step0Labels = mixedMoment B raw13223step1 raw13223step1Labels := by
      have ha : raw13223step1 = (fun i j => raw13223step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13223step1 raw13223step0; decide +kernel
      have hl : raw13223step1Labels = raw13223step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13223step0 raw13223step0Labels permutation35 permutation3
    mixedMoment B raw13223step1 raw13223step1Labels = mixedMoment B raw13223step2 raw13223step2Labels := by
      have ha : raw13223step2 = raw13223step1 := by apply Matrix.ext; unfold raw13223step2 raw13223step1; decide +kernel
      have hl : raw13223step1Labels = labelEmbedding6 ∘ raw13223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13223step1 raw13223step1Labels raw13223step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw13224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13224step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13224 raw13224Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw13224 raw13224Labels = mixedMoment B raw13224step0 raw13224step0Labels := by
      have ha : raw13224step0 = (fun i j => raw13224 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13224step0 raw13224; decide +kernel
      have hl : raw13224step0Labels = raw13224Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13224 raw13224Labels permutation155 permutation3
    mixedMoment B raw13224step0 raw13224step0Labels = mixedMoment B raw13224step1 raw13224step1Labels := by
      have ha : raw13224step1 = raw13224step0 := by apply Matrix.ext; unfold raw13224step1 raw13224step0; decide +kernel
      have hl : raw13224step0Labels = labelEmbedding6 ∘ raw13224step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13224step0 raw13224step0Labels raw13224step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw13225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13225step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13225 raw13225Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw13225 raw13225Labels = mixedMoment B raw13225step0 raw13225step0Labels := by
      have ha : raw13225step0 = (fun i j => raw13225 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13225step0 raw13225; decide +kernel
      have hl : raw13225step0Labels = raw13225Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13225 raw13225Labels permutation155 permutation3
    mixedMoment B raw13225step0 raw13225step0Labels = mixedMoment B raw13225step1 raw13225step1Labels := by
      have ha : raw13225step1 = raw13225step0 := by apply Matrix.ext; unfold raw13225step1 raw13225step0; decide +kernel
      have hl : raw13225step0Labels = labelEmbedding6 ∘ raw13225step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13225step0 raw13225step0Labels raw13225step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw13226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13226step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13226 raw13226Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw13226 raw13226Labels = mixedMoment B raw13226step0 raw13226step0Labels := by
      have ha : raw13226step0 = (fun i j => raw13226 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13226step0 raw13226; decide +kernel
      have hl : raw13226step0Labels = raw13226Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13226 raw13226Labels permutation179 permutation3
    mixedMoment B raw13226step0 raw13226step0Labels = mixedMoment B raw13226step1 raw13226step1Labels := by
      have ha : raw13226step1 = raw13226step0 := by apply Matrix.ext; unfold raw13226step1 raw13226step0; decide +kernel
      have hl : raw13226step0Labels = labelEmbedding6 ∘ raw13226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13226step0 raw13226step0Labels raw13226step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw13227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13227step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13227 raw13227Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw13227 raw13227Labels = mixedMoment B raw13227step0 raw13227step0Labels := by
      have ha : raw13227step0 = (fun i j => raw13227 (permutation225 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13227step0 raw13227; decide +kernel
      have hl : raw13227step0Labels = raw13227Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13227 raw13227Labels permutation225 permutation3
    mixedMoment B raw13227step0 raw13227step0Labels = mixedMoment B raw13227step1 raw13227step1Labels := by
      have ha : raw13227step1 = raw13227step0 := by apply Matrix.ext; unfold raw13227step1 raw13227step0; decide +kernel
      have hl : raw13227step0Labels = labelEmbedding6 ∘ raw13227step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13227step0 raw13227step0Labels raw13227step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw13228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw13228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13228step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13228step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13228step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13228step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13228 raw13228Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw13228 raw13228Labels = mixedMoment B raw13228step0 raw13228step0Labels := by
      have hz : ∀ j, raw13228 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13228step0 = (fun i j => raw13228 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13228step0 raw13228; decide +kernel
      have hl : raw13228step0Labels = raw13228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13228 raw13228Labels permutation590 hz
    mixedMoment B raw13228step0 raw13228step0Labels = mixedMoment B raw13228step1 raw13228step1Labels := by
      have ha : raw13228step1 = (fun i j => raw13228step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13228step1 raw13228step0; decide +kernel
      have hl : raw13228step1Labels = raw13228step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13228step0 raw13228step0Labels permutation33 permutation3
    mixedMoment B raw13228step1 raw13228step1Labels = mixedMoment B raw13228step2 raw13228step2Labels := by
      have ha : raw13228step2 = raw13228step1 := by apply Matrix.ext; unfold raw13228step2 raw13228step1; decide +kernel
      have hl : raw13228step1Labels = labelEmbedding6 ∘ raw13228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13228step1 raw13228step1Labels raw13228step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw13229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13229step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13229step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13229 raw13229Labels = mixedMoment B node4436 node4436Labels := by
  calc
    mixedMoment B raw13229 raw13229Labels = mixedMoment B raw13229step0 raw13229step0Labels := by
      have ha : raw13229step0 = (fun i j => raw13229 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13229step0 raw13229; decide +kernel
      have hl : raw13229step0Labels = raw13229Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13229 raw13229Labels permutation153 permutation3
    mixedMoment B raw13229step0 raw13229step0Labels = mixedMoment B raw13229step1 raw13229step1Labels := by
      have ha : raw13229step1 = raw13229step0 := by apply Matrix.ext; unfold raw13229step1 raw13229step0; decide +kernel
      have hl : raw13229step0Labels = labelEmbedding6 ∘ raw13229step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13229step0 raw13229step0Labels raw13229step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4436 node4436Labels := by rfl

def raw13230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13230step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13230 raw13230Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw13230 raw13230Labels = mixedMoment B raw13230step0 raw13230step0Labels := by
      have ha : raw13230step0 = (fun i j => raw13230 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13230step0 raw13230; decide +kernel
      have hl : raw13230step0Labels = raw13230Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13230 raw13230Labels permutation153 permutation3
    mixedMoment B raw13230step0 raw13230step0Labels = mixedMoment B raw13230step1 raw13230step1Labels := by
      have ha : raw13230step1 = raw13230step0 := by apply Matrix.ext; unfold raw13230step1 raw13230step0; decide +kernel
      have hl : raw13230step0Labels = labelEmbedding6 ∘ raw13230step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13230step0 raw13230step0Labels raw13230step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw13231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13231step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13231 raw13231Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw13231 raw13231Labels = mixedMoment B raw13231step0 raw13231step0Labels := by
      have ha : raw13231step0 = (fun i j => raw13231 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13231step0 raw13231; decide +kernel
      have hl : raw13231step0Labels = raw13231Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13231 raw13231Labels permutation177 permutation3
    mixedMoment B raw13231step0 raw13231step0Labels = mixedMoment B raw13231step1 raw13231step1Labels := by
      have ha : raw13231step1 = raw13231step0 := by apply Matrix.ext; unfold raw13231step1 raw13231step0; decide +kernel
      have hl : raw13231step0Labels = labelEmbedding6 ∘ raw13231step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13231step0 raw13231step0Labels raw13231step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw13232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13232step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13232 raw13232Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw13232 raw13232Labels = mixedMoment B raw13232step0 raw13232step0Labels := by
      have ha : raw13232step0 = (fun i j => raw13232 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13232step0 raw13232; decide +kernel
      have hl : raw13232step0Labels = raw13232Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13232 raw13232Labels permutation201 permutation3
    mixedMoment B raw13232step0 raw13232step0Labels = mixedMoment B raw13232step1 raw13232step1Labels := by
      have ha : raw13232step1 = raw13232step0 := by apply Matrix.ext; unfold raw13232step1 raw13232step0; decide +kernel
      have hl : raw13232step0Labels = labelEmbedding6 ∘ raw13232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13232step0 raw13232step0Labels raw13232step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

def raw13233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw13233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13233step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13233step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13233 raw13233Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw13233 raw13233Labels = mixedMoment B raw13233step0 raw13233step0Labels := by
      have hz : ∀ j, raw13233 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13233step0 = (fun i j => raw13233 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13233step0 raw13233; decide +kernel
      have hl : raw13233step0Labels = raw13233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13233 raw13233Labels permutation590 hz
    mixedMoment B raw13233step0 raw13233step0Labels = mixedMoment B raw13233step1 raw13233step1Labels := by
      have ha : raw13233step1 = (fun i j => raw13233step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13233step1 raw13233step0; decide +kernel
      have hl : raw13233step1Labels = raw13233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13233step0 raw13233step0Labels permutation32 permutation3
    mixedMoment B raw13233step1 raw13233step1Labels = mixedMoment B raw13233step2 raw13233step2Labels := by
      have ha : raw13233step2 = raw13233step1 := by apply Matrix.ext; unfold raw13233step2 raw13233step1; decide +kernel
      have hl : raw13233step1Labels = labelEmbedding6 ∘ raw13233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13233step1 raw13233step1Labels raw13233step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw13234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13234step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13234step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13234 raw13234Labels = mixedMoment B node4435 node4435Labels := by
  calc
    mixedMoment B raw13234 raw13234Labels = mixedMoment B raw13234step0 raw13234step0Labels := by
      have ha : raw13234step0 = (fun i j => raw13234 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13234step0 raw13234; decide +kernel
      have hl : raw13234step0Labels = raw13234Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13234 raw13234Labels permutation152 permutation3
    mixedMoment B raw13234step0 raw13234step0Labels = mixedMoment B raw13234step1 raw13234step1Labels := by
      have ha : raw13234step1 = raw13234step0 := by apply Matrix.ext; unfold raw13234step1 raw13234step0; decide +kernel
      have hl : raw13234step0Labels = labelEmbedding6 ∘ raw13234step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13234step0 raw13234step0Labels raw13234step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4435 node4435Labels := by rfl

def raw13235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13235step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13235 raw13235Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw13235 raw13235Labels = mixedMoment B raw13235step0 raw13235step0Labels := by
      have ha : raw13235step0 = (fun i j => raw13235 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13235step0 raw13235; decide +kernel
      have hl : raw13235step0Labels = raw13235Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13235 raw13235Labels permutation152 permutation3
    mixedMoment B raw13235step0 raw13235step0Labels = mixedMoment B raw13235step1 raw13235step1Labels := by
      have ha : raw13235step1 = raw13235step0 := by apply Matrix.ext; unfold raw13235step1 raw13235step0; decide +kernel
      have hl : raw13235step0Labels = labelEmbedding6 ∘ raw13235step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13235step0 raw13235step0Labels raw13235step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw13236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13236step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13236 raw13236Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw13236 raw13236Labels = mixedMoment B raw13236step0 raw13236step0Labels := by
      have ha : raw13236step0 = (fun i j => raw13236 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13236step0 raw13236; decide +kernel
      have hl : raw13236step0Labels = raw13236Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13236 raw13236Labels permutation176 permutation3
    mixedMoment B raw13236step0 raw13236step0Labels = mixedMoment B raw13236step1 raw13236step1Labels := by
      have ha : raw13236step1 = raw13236step0 := by apply Matrix.ext; unfold raw13236step1 raw13236step0; decide +kernel
      have hl : raw13236step0Labels = labelEmbedding6 ∘ raw13236step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13236step0 raw13236step0Labels raw13236step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw13237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13237step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13237 raw13237Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw13237 raw13237Labels = mixedMoment B raw13237step0 raw13237step0Labels := by
      have ha : raw13237step0 = (fun i j => raw13237 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13237step0 raw13237; decide +kernel
      have hl : raw13237step0Labels = raw13237Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13237 raw13237Labels permutation200 permutation3
    mixedMoment B raw13237step0 raw13237step0Labels = mixedMoment B raw13237step1 raw13237step1Labels := by
      have ha : raw13237step1 = raw13237step0 := by apply Matrix.ext; unfold raw13237step1 raw13237step0; decide +kernel
      have hl : raw13237step0Labels = labelEmbedding6 ∘ raw13237step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13237step0 raw13237step0Labels raw13237step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw13238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw13238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13238step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13238 raw13238Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw13238 raw13238Labels = mixedMoment B raw13238step0 raw13238step0Labels := by
      have ha : raw13238step0 = (fun i j => raw13238 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13238step0 raw13238; decide +kernel
      have hl : raw13238step0Labels = raw13238Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13238 raw13238Labels permutation224 permutation3
    mixedMoment B raw13238step0 raw13238step0Labels = mixedMoment B raw13238step1 raw13238step1Labels := by
      have ha : raw13238step1 = raw13238step0 := by apply Matrix.ext; unfold raw13238step1 raw13238step0; decide +kernel
      have hl : raw13238step0Labels = labelEmbedding6 ∘ raw13238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13238step0 raw13238step0Labels raw13238step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw13239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13239 raw13239Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw13239 raw13239Labels = mixedMoment B raw13239step0 raw13239step0Labels := by
      have ha : raw13239step0 = (fun i j => raw13239 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13239step0 raw13239; decide +kernel
      have hl : raw13239step0Labels = raw13239Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13239 raw13239Labels permutation152 permutation3
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw13240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13240 raw13240Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw13240 raw13240Labels = mixedMoment B raw13240step0 raw13240step0Labels := by
      have ha : raw13240step0 = (fun i j => raw13240 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13240step0 raw13240; decide +kernel
      have hl : raw13240step0Labels = raw13240Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13240 raw13240Labels permutation176 permutation3
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw13241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13241 raw13241Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw13241 raw13241Labels = mixedMoment B raw13241step0 raw13241step0Labels := by
      have ha : raw13241step0 = (fun i j => raw13241 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13241step0 raw13241; decide +kernel
      have hl : raw13241step0Labels = raw13241Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13241 raw13241Labels permutation499 permutation6
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw13242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13242 raw13242Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw13242 raw13242Labels = mixedMoment B raw13242step0 raw13242step0Labels := by
      have ha : raw13242step0 = (fun i j => raw13242 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13242step0 raw13242; decide +kernel
      have hl : raw13242step0Labels = raw13242Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13242 raw13242Labels permutation499 permutation6
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw13243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13243step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13243 raw13243Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw13243 raw13243Labels = mixedMoment B raw13243step0 raw13243step0Labels := by
      have hz : ∀ j, raw13243 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13243step0 = (fun i j => raw13243 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13243step0 raw13243; decide +kernel
      have hl : raw13243step0Labels = raw13243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13243 raw13243Labels permutation590 hz
    mixedMoment B raw13243step0 raw13243step0Labels = mixedMoment B raw13243step1 raw13243step1Labels := by
      have ha : raw13243step1 = (fun i j => raw13243step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13243step1 raw13243step0; decide +kernel
      have hl : raw13243step1Labels = raw13243step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13243step0 raw13243step0Labels permutation122 permutation6
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw13244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13244Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13244 raw13244Labels = mixedMoment B node1032 node1032Labels := by
  calc
    mixedMoment B raw13244 raw13244Labels = mixedMoment B raw13244step0 raw13244step0Labels := by
      have ha : raw13244step0 = (fun i j => raw13244 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13244step0 raw13244; decide +kernel
      have hl : raw13244step0Labels = raw13244Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13244 raw13244Labels permutation185 permutation3
    _ = mixedMoment B node1032 node1032Labels := by rfl

def raw13245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13245 raw13245Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw13245 raw13245Labels = mixedMoment B raw13245step0 raw13245step0Labels := by
      have ha : raw13245step0 = (fun i j => raw13245 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13245step0 raw13245; decide +kernel
      have hl : raw13245step0Labels = raw13245Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13245 raw13245Labels permutation185 permutation3
    _ = mixedMoment B node2587 node2587Labels := by rfl

def raw13246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13246 raw13246Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw13246 raw13246Labels = mixedMoment B raw13246step0 raw13246step0Labels := by
      have ha : raw13246step0 = (fun i j => raw13246 (permutation209 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13246step0 raw13246; decide +kernel
      have hl : raw13246step0Labels = raw13246Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13246 raw13246Labels permutation209 permutation3
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw13247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13247 raw13247Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw13247 raw13247Labels = mixedMoment B raw13247step0 raw13247step0Labels := by
      have ha : raw13247step0 = (fun i j => raw13247 (permutation233 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13247step0 raw13247; decide +kernel
      have hl : raw13247step0Labels = raw13247Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13247 raw13247Labels permutation233 permutation3
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw13248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13248step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13248 raw13248Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw13248 raw13248Labels = mixedMoment B raw13248step0 raw13248step0Labels := by
      have hz : ∀ j, raw13248 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13248step0 = (fun i j => raw13248 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13248step0 raw13248; decide +kernel
      have hl : raw13248step0Labels = raw13248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13248 raw13248Labels permutation590 hz
    mixedMoment B raw13248step0 raw13248step0Labels = mixedMoment B raw13248step1 raw13248step1Labels := by
      have ha : raw13248step1 = (fun i j => raw13248step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13248step1 raw13248step0; decide +kernel
      have hl : raw13248step1Labels = raw13248step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13248step0 raw13248step0Labels permutation41 permutation3
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw13249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13249 raw13249Labels = mixedMoment B node1032 node1032Labels := by
  calc
    mixedMoment B raw13249 raw13249Labels = mixedMoment B raw13249step0 raw13249step0Labels := by
      have ha : raw13249step0 = (fun i j => raw13249 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13249step0 raw13249; decide +kernel
      have hl : raw13249step0Labels = raw13249Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13249 raw13249Labels permutation161 permutation3
    _ = mixedMoment B node1032 node1032Labels := by rfl

def raw13250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13250step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13250 raw13250Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw13250 raw13250Labels = mixedMoment B raw13250step0 raw13250step0Labels := by
      have ha : raw13250step0 = (fun i j => raw13250 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13250step0 raw13250; decide +kernel
      have hl : raw13250step0Labels = raw13250Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13250 raw13250Labels permutation161 permutation3
    _ = mixedMoment B node2587 node2587Labels := by rfl

def raw13251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13251 raw13251Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw13251 raw13251Labels = mixedMoment B raw13251step0 raw13251step0Labels := by
      have ha : raw13251step0 = (fun i j => raw13251 (permutation203 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13251step0 raw13251; decide +kernel
      have hl : raw13251step0Labels = raw13251Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13251 raw13251Labels permutation203 permutation3
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw13252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13252step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13252 raw13252Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw13252 raw13252Labels = mixedMoment B raw13252step0 raw13252step0Labels := by
      have ha : raw13252step0 = (fun i j => raw13252 (permutation227 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13252step0 raw13252; decide +kernel
      have hl : raw13252step0Labels = raw13252Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13252 raw13252Labels permutation227 permutation3
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw13253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13253step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw13253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13253 raw13253Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw13253 raw13253Labels = mixedMoment B raw13253step0 raw13253step0Labels := by
      have hz : ∀ j, raw13253 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13253step0 = (fun i j => raw13253 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13253step0 raw13253; decide +kernel
      have hl : raw13253step0Labels = raw13253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13253 raw13253Labels permutation590 hz
    mixedMoment B raw13253step0 raw13253step0Labels = mixedMoment B raw13253step1 raw13253step1Labels := by
      have ha : raw13253step1 = (fun i j => raw13253step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13253step1 raw13253step0; decide +kernel
      have hl : raw13253step1Labels = raw13253step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13253step0 raw13253step0Labels permutation35 permutation3
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw13254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13254 raw13254Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw13254 raw13254Labels = mixedMoment B raw13254step0 raw13254step0Labels := by
      have ha : raw13254step0 = (fun i j => raw13254 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13254step0 raw13254; decide +kernel
      have hl : raw13254step0Labels = raw13254Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13254 raw13254Labels permutation155 permutation3
    _ = mixedMoment B node1021 node1021Labels := by rfl

def raw13255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13255 raw13255Labels = mixedMoment B node2570 node2570Labels := by
  calc
    mixedMoment B raw13255 raw13255Labels = mixedMoment B raw13255step0 raw13255step0Labels := by
      have ha : raw13255step0 = (fun i j => raw13255 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13255step0 raw13255; decide +kernel
      have hl : raw13255step0Labels = raw13255Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13255 raw13255Labels permutation155 permutation3
    _ = mixedMoment B node2570 node2570Labels := by rfl

def raw13256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw13256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13256 raw13256Labels = mixedMoment B node2570 node2570Labels := by
  calc
    mixedMoment B raw13256 raw13256Labels = mixedMoment B raw13256step0 raw13256step0Labels := by
      have ha : raw13256step0 = (fun i j => raw13256 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13256step0 raw13256; decide +kernel
      have hl : raw13256step0Labels = raw13256Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13256 raw13256Labels permutation179 permutation3
    _ = mixedMoment B node2570 node2570Labels := by rfl

def raw13257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13257 raw13257Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw13257 raw13257Labels = mixedMoment B raw13257step0 raw13257step0Labels := by
      have ha : raw13257step0 = (fun i j => raw13257 (permutation225 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13257step0 raw13257; decide +kernel
      have hl : raw13257step0Labels = raw13257Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13257 raw13257Labels permutation225 permutation3
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw13258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw13258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13258 raw13258Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw13258 raw13258Labels = mixedMoment B raw13258step0 raw13258step0Labels := by
      have hz : ∀ j, raw13258 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13258step0 = (fun i j => raw13258 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13258step0 raw13258; decide +kernel
      have hl : raw13258step0Labels = raw13258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13258 raw13258Labels permutation590 hz
    mixedMoment B raw13258step0 raw13258step0Labels = mixedMoment B raw13258step1 raw13258step1Labels := by
      have ha : raw13258step1 = (fun i j => raw13258step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13258step1 raw13258step0; decide +kernel
      have hl : raw13258step1Labels = raw13258step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13258step0 raw13258step0Labels permutation33 permutation3
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw13259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13259 raw13259Labels = mixedMoment B node1018 node1018Labels := by
  calc
    mixedMoment B raw13259 raw13259Labels = mixedMoment B raw13259step0 raw13259step0Labels := by
      have ha : raw13259step0 = (fun i j => raw13259 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13259step0 raw13259; decide +kernel
      have hl : raw13259step0Labels = raw13259Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13259 raw13259Labels permutation153 permutation3
    _ = mixedMoment B node1018 node1018Labels := by rfl

def raw13260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13260 raw13260Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw13260 raw13260Labels = mixedMoment B raw13260step0 raw13260step0Labels := by
      have ha : raw13260step0 = (fun i j => raw13260 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13260step0 raw13260; decide +kernel
      have hl : raw13260step0Labels = raw13260Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13260 raw13260Labels permutation153 permutation3
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw13261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw13261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13261 raw13261Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw13261 raw13261Labels = mixedMoment B raw13261step0 raw13261step0Labels := by
      have ha : raw13261step0 = (fun i j => raw13261 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13261step0 raw13261; decide +kernel
      have hl : raw13261step0Labels = raw13261Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13261 raw13261Labels permutation177 permutation3
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw13262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13262 raw13262Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw13262 raw13262Labels = mixedMoment B raw13262step0 raw13262step0Labels := by
      have ha : raw13262step0 = (fun i j => raw13262 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13262step0 raw13262; decide +kernel
      have hl : raw13262step0Labels = raw13262Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13262 raw13262Labels permutation201 permutation3
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw13263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw13263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13263 raw13263Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw13263 raw13263Labels = mixedMoment B raw13263step0 raw13263step0Labels := by
      have hz : ∀ j, raw13263 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13263step0 = (fun i j => raw13263 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13263step0 raw13263; decide +kernel
      have hl : raw13263step0Labels = raw13263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13263 raw13263Labels permutation590 hz
    mixedMoment B raw13263step0 raw13263step0Labels = mixedMoment B raw13263step1 raw13263step1Labels := by
      have ha : raw13263step1 = (fun i j => raw13263step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13263step1 raw13263step0; decide +kernel
      have hl : raw13263step1Labels = raw13263step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13263step0 raw13263step0Labels permutation32 permutation3
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw13264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13264 raw13264Labels = mixedMoment B node1017 node1017Labels := by
  calc
    mixedMoment B raw13264 raw13264Labels = mixedMoment B raw13264step0 raw13264step0Labels := by
      have ha : raw13264step0 = (fun i j => raw13264 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13264step0 raw13264; decide +kernel
      have hl : raw13264step0Labels = raw13264Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13264 raw13264Labels permutation152 permutation3
    _ = mixedMoment B node1017 node1017Labels := by rfl

def raw13265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13265 raw13265Labels = mixedMoment B node2566 node2566Labels := by
  calc
    mixedMoment B raw13265 raw13265Labels = mixedMoment B raw13265step0 raw13265step0Labels := by
      have ha : raw13265step0 = (fun i j => raw13265 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13265step0 raw13265; decide +kernel
      have hl : raw13265step0Labels = raw13265Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13265 raw13265Labels permutation152 permutation3
    _ = mixedMoment B node2566 node2566Labels := by rfl

def raw13266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw13266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13266 raw13266Labels = mixedMoment B node2566 node2566Labels := by
  calc
    mixedMoment B raw13266 raw13266Labels = mixedMoment B raw13266step0 raw13266step0Labels := by
      have ha : raw13266step0 = (fun i j => raw13266 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13266step0 raw13266; decide +kernel
      have hl : raw13266step0Labels = raw13266Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13266 raw13266Labels permutation176 permutation3
    _ = mixedMoment B node2566 node2566Labels := by rfl

def raw13267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13267 raw13267Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw13267 raw13267Labels = mixedMoment B raw13267step0 raw13267step0Labels := by
      have ha : raw13267step0 = (fun i j => raw13267 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13267step0 raw13267; decide +kernel
      have hl : raw13267step0Labels = raw13267Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13267 raw13267Labels permutation200 permutation3
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw13268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw13268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw13268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13268 raw13268Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw13268 raw13268Labels = mixedMoment B raw13268step0 raw13268step0Labels := by
      have ha : raw13268step0 = (fun i j => raw13268 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13268step0 raw13268; decide +kernel
      have hl : raw13268step0Labels = raw13268Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13268 raw13268Labels permutation224 permutation3
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw13269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13269Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13269step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13269 raw13269Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw13269 raw13269Labels = mixedMoment B raw13269step0 raw13269step0Labels := by
      have ha : raw13269step0 = (fun i j => raw13269 (permutation504 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13269step0 raw13269; decide +kernel
      have hl : raw13269step0Labels = raw13269Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13269 raw13269Labels permutation504 permutation7
    mixedMoment B raw13269step0 raw13269step0Labels = mixedMoment B raw13269step1 raw13269step1Labels := by
      have ha : raw13269step1 = raw13269step0 := by apply Matrix.ext; unfold raw13269step1 raw13269step0; decide +kernel
      have hl : raw13269step0Labels = labelEmbedding1 ∘ raw13269step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13269step0 raw13269step0Labels raw13269step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw13270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13270step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13270 raw13270Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw13270 raw13270Labels = mixedMoment B raw13270step0 raw13270step0Labels := by
      have ha : raw13270step0 = (fun i j => raw13270 (permutation502 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13270step0 raw13270; decide +kernel
      have hl : raw13270step0Labels = raw13270Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13270 raw13270Labels permutation502 permutation7
    mixedMoment B raw13270step0 raw13270step0Labels = mixedMoment B raw13270step1 raw13270step1Labels := by
      have ha : raw13270step1 = raw13270step0 := by apply Matrix.ext; unfold raw13270step1 raw13270step0; decide +kernel
      have hl : raw13270step0Labels = labelEmbedding1 ∘ raw13270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13270step0 raw13270step0Labels raw13270step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw13271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13271Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13271step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13271 raw13271Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw13271 raw13271Labels = mixedMoment B raw13271step0 raw13271step0Labels := by
      have ha : raw13271step0 = (fun i j => raw13271 (permutation443 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13271step0 raw13271; decide +kernel
      have hl : raw13271step0Labels = raw13271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13271 raw13271Labels permutation443 permutation5
    mixedMoment B raw13271step0 raw13271step0Labels = mixedMoment B raw13271step1 raw13271step1Labels := by
      have ha : raw13271step1 = -raw13271step0 := by apply Matrix.ext; change ∀ i j, raw13271step1 i j = -(raw13271step0 i j); unfold raw13271step1 raw13271step0; decide +kernel
      have hl : raw13271step1Labels = raw13271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13271step1 raw13271step1Labels = mixedMoment B raw13271step2 raw13271step2Labels := by
      have ha : raw13271step2 = raw13271step1 := by apply Matrix.ext; unfold raw13271step2 raw13271step1; decide +kernel
      have hl : raw13271step1Labels = labelEmbedding1 ∘ raw13271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13271step1 raw13271step1Labels raw13271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw13272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13272step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13272 raw13272Labels = mixedMoment B node3991 node3991Labels := by
  calc
    mixedMoment B raw13272 raw13272Labels = mixedMoment B raw13272step0 raw13272step0Labels := by
      have ha : raw13272step0 = (fun i j => raw13272 (permutation502 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13272step0 raw13272; decide +kernel
      have hl : raw13272step0Labels = raw13272Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13272 raw13272Labels permutation502 permutation7
    mixedMoment B raw13272step0 raw13272step0Labels = mixedMoment B raw13272step1 raw13272step1Labels := by
      have ha : raw13272step1 = raw13272step0 := by apply Matrix.ext; unfold raw13272step1 raw13272step0; decide +kernel
      have hl : raw13272step0Labels = labelEmbedding1 ∘ raw13272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13272step0 raw13272step0Labels raw13272step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3991 node3991Labels := by rfl

def raw13273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13273Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13273step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13273 raw13273Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw13273 raw13273Labels = mixedMoment B raw13273step0 raw13273step0Labels := by
      have hz : ∀ j, raw13273 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13273step0 = (fun i j => raw13273 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13273step0 raw13273; decide +kernel
      have hl : raw13273step0Labels = raw13273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13273 raw13273Labels permutation590 hz
    mixedMoment B raw13273step0 raw13273step0Labels = mixedMoment B raw13273step1 raw13273step1Labels := by
      have ha : raw13273step1 = (fun i j => raw13273step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13273step1 raw13273step0; decide +kernel
      have hl : raw13273step1Labels = raw13273step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13273step0 raw13273step0Labels permutation125 permutation7
    mixedMoment B raw13273step1 raw13273step1Labels = mixedMoment B raw13273step2 raw13273step2Labels := by
      have ha : raw13273step2 = raw13273step1 := by apply Matrix.ext; unfold raw13273step2 raw13273step1; decide +kernel
      have hl : raw13273step1Labels = labelEmbedding1 ∘ raw13273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13273step1 raw13273step1Labels raw13273step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw13274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13274Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13274step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13274step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13274 raw13274Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw13274 raw13274Labels = mixedMoment B raw13274step0 raw13274step0Labels := by
      have ha : raw13274step0 = (fun i j => raw13274 (permutation215 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13274step0 raw13274; decide +kernel
      have hl : raw13274step0Labels = raw13274Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13274 raw13274Labels permutation215 permutation5
    mixedMoment B raw13274step0 raw13274step0Labels = mixedMoment B raw13274step1 raw13274step1Labels := by
      have ha : raw13274step1 = -raw13274step0 := by apply Matrix.ext; change ∀ i j, raw13274step1 i j = -(raw13274step0 i j); unfold raw13274step1 raw13274step0; decide +kernel
      have hl : raw13274step1Labels = raw13274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13274step1 raw13274step1Labels = mixedMoment B raw13274step2 raw13274step2Labels := by
      have ha : raw13274step2 = raw13274step1 := by apply Matrix.ext; unfold raw13274step2 raw13274step1; decide +kernel
      have hl : raw13274step1Labels = labelEmbedding1 ∘ raw13274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13274step1 raw13274step1Labels raw13274step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1636 node1636Labels := by rfl

def raw13275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13275Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13275step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13275step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13275step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13275 raw13275Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw13275 raw13275Labels = mixedMoment B raw13275step0 raw13275step0Labels := by
      have ha : raw13275step0 = (fun i j => raw13275 (permutation209 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13275step0 raw13275; decide +kernel
      have hl : raw13275step0Labels = raw13275Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13275 raw13275Labels permutation209 permutation5
    mixedMoment B raw13275step0 raw13275step0Labels = mixedMoment B raw13275step1 raw13275step1Labels := by
      have ha : raw13275step1 = -raw13275step0 := by apply Matrix.ext; change ∀ i j, raw13275step1 i j = -(raw13275step0 i j); unfold raw13275step1 raw13275step0; decide +kernel
      have hl : raw13275step1Labels = raw13275step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13275step1 raw13275step1Labels = mixedMoment B raw13275step2 raw13275step2Labels := by
      have ha : raw13275step2 = raw13275step1 := by apply Matrix.ext; unfold raw13275step2 raw13275step1; decide +kernel
      have hl : raw13275step1Labels = labelEmbedding1 ∘ raw13275step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13275step1 raw13275step1Labels raw13275step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw13276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13276Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13276step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13276 raw13276Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw13276 raw13276Labels = mixedMoment B raw13276step0 raw13276step0Labels := by
      have ha : raw13276step0 = (fun i j => raw13276 (permutation215 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13276step0 raw13276; decide +kernel
      have hl : raw13276step0Labels = raw13276Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13276 raw13276Labels permutation215 permutation5
    mixedMoment B raw13276step0 raw13276step0Labels = mixedMoment B raw13276step1 raw13276step1Labels := by
      have ha : raw13276step1 = -raw13276step0 := by apply Matrix.ext; change ∀ i j, raw13276step1 i j = -(raw13276step0 i j); unfold raw13276step1 raw13276step0; decide +kernel
      have hl : raw13276step1Labels = raw13276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13276step1 raw13276step1Labels = mixedMoment B raw13276step2 raw13276step2Labels := by
      have ha : raw13276step2 = raw13276step1 := by apply Matrix.ext; unfold raw13276step2 raw13276step1; decide +kernel
      have hl : raw13276step1Labels = labelEmbedding1 ∘ raw13276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13276step1 raw13276step1Labels raw13276step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3376 node3376Labels := by rfl

def raw13277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13277Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13277step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13277step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13277step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13277 raw13277Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw13277 raw13277Labels = mixedMoment B raw13277step0 raw13277step0Labels := by
      have ha : raw13277step0 = (fun i j => raw13277 (permutation237 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13277step0 raw13277; decide +kernel
      have hl : raw13277step0Labels = raw13277Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13277 raw13277Labels permutation237 permutation5
    mixedMoment B raw13277step0 raw13277step0Labels = mixedMoment B raw13277step1 raw13277step1Labels := by
      have ha : raw13277step1 = -raw13277step0 := by apply Matrix.ext; change ∀ i j, raw13277step1 i j = -(raw13277step0 i j); unfold raw13277step1 raw13277step0; decide +kernel
      have hl : raw13277step1Labels = raw13277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13277step1 raw13277step1Labels = mixedMoment B raw13277step2 raw13277step2Labels := by
      have ha : raw13277step2 = raw13277step1 := by apply Matrix.ext; unfold raw13277step2 raw13277step1; decide +kernel
      have hl : raw13277step1Labels = labelEmbedding1 ∘ raw13277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13277step1 raw13277step1Labels raw13277step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3503 node3503Labels := by rfl

def raw13278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13278step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13278step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13278step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13278step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13278 raw13278Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw13278 raw13278Labels = mixedMoment B raw13278step0 raw13278step0Labels := by
      have hz : ∀ j, raw13278 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13278step0 = (fun i j => raw13278 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13278step0 raw13278; decide +kernel
      have hl : raw13278step0Labels = raw13278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13278 raw13278Labels permutation590 hz
    mixedMoment B raw13278step0 raw13278step0Labels = mixedMoment B raw13278step1 raw13278step1Labels := by
      have ha : raw13278step1 = (fun i j => raw13278step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13278step1 raw13278step0; decide +kernel
      have hl : raw13278step1Labels = raw13278step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13278step0 raw13278step0Labels permutation49 permutation5
    mixedMoment B raw13278step1 raw13278step1Labels = mixedMoment B raw13278step2 raw13278step2Labels := by
      have ha : raw13278step2 = -raw13278step1 := by apply Matrix.ext; change ∀ i j, raw13278step2 i j = -(raw13278step1 i j); unfold raw13278step2 raw13278step1; decide +kernel
      have hl : raw13278step2Labels = raw13278step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13278step2 raw13278step2Labels = mixedMoment B raw13278step3 raw13278step3Labels := by
      have ha : raw13278step3 = raw13278step2 := by apply Matrix.ext; unfold raw13278step3 raw13278step2; decide +kernel
      have hl : raw13278step2Labels = labelEmbedding1 ∘ raw13278step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13278step2 raw13278step2Labels raw13278step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw13279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13279Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13279step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13279step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13279step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13279step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13279 raw13279Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw13279 raw13279Labels = mixedMoment B raw13279step0 raw13279step0Labels := by
      have ha : raw13279step0 = (fun i j => raw13279 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13279step0 raw13279; decide +kernel
      have hl : raw13279step0Labels = raw13279Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13279 raw13279Labels permutation213 permutation5
    mixedMoment B raw13279step0 raw13279step0Labels = mixedMoment B raw13279step1 raw13279step1Labels := by
      have ha : raw13279step1 = -raw13279step0 := by apply Matrix.ext; change ∀ i j, raw13279step1 i j = -(raw13279step0 i j); unfold raw13279step1 raw13279step0; decide +kernel
      have hl : raw13279step1Labels = raw13279step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13279step1 raw13279step1Labels = mixedMoment B raw13279step2 raw13279step2Labels := by
      have ha : raw13279step2 = raw13279step1 := by apply Matrix.ext; unfold raw13279step2 raw13279step1; decide +kernel
      have hl : raw13279step1Labels = labelEmbedding1 ∘ raw13279step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13279step1 raw13279step1Labels raw13279step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1636 node1636Labels := by rfl

def raw13280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13280step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13280step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13280step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13280 raw13280Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw13280 raw13280Labels = mixedMoment B raw13280step0 raw13280step0Labels := by
      have ha : raw13280step0 = (fun i j => raw13280 (permutation203 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13280step0 raw13280; decide +kernel
      have hl : raw13280step0Labels = raw13280Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13280 raw13280Labels permutation203 permutation5
    mixedMoment B raw13280step0 raw13280step0Labels = mixedMoment B raw13280step1 raw13280step1Labels := by
      have ha : raw13280step1 = -raw13280step0 := by apply Matrix.ext; change ∀ i j, raw13280step1 i j = -(raw13280step0 i j); unfold raw13280step1 raw13280step0; decide +kernel
      have hl : raw13280step1Labels = raw13280step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13280step1 raw13280step1Labels = mixedMoment B raw13280step2 raw13280step2Labels := by
      have ha : raw13280step2 = raw13280step1 := by apply Matrix.ext; unfold raw13280step2 raw13280step1; decide +kernel
      have hl : raw13280step1Labels = labelEmbedding1 ∘ raw13280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13280step1 raw13280step1Labels raw13280step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw13281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13281Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13281step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13281step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13281step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13281 raw13281Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw13281 raw13281Labels = mixedMoment B raw13281step0 raw13281step0Labels := by
      have ha : raw13281step0 = (fun i j => raw13281 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13281step0 raw13281; decide +kernel
      have hl : raw13281step0Labels = raw13281Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13281 raw13281Labels permutation213 permutation5
    mixedMoment B raw13281step0 raw13281step0Labels = mixedMoment B raw13281step1 raw13281step1Labels := by
      have ha : raw13281step1 = -raw13281step0 := by apply Matrix.ext; change ∀ i j, raw13281step1 i j = -(raw13281step0 i j); unfold raw13281step1 raw13281step0; decide +kernel
      have hl : raw13281step1Labels = raw13281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13281step1 raw13281step1Labels = mixedMoment B raw13281step2 raw13281step2Labels := by
      have ha : raw13281step2 = raw13281step1 := by apply Matrix.ext; unfold raw13281step2 raw13281step1; decide +kernel
      have hl : raw13281step1Labels = labelEmbedding1 ∘ raw13281step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13281step1 raw13281step1Labels raw13281step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3376 node3376Labels := by rfl

def raw13282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw13282step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13282step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw13282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13282 raw13282Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw13282 raw13282Labels = mixedMoment B raw13282step0 raw13282step0Labels := by
      have ha : raw13282step0 = (fun i j => raw13282 (permutation235 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13282step0 raw13282; decide +kernel
      have hl : raw13282step0Labels = raw13282Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13282 raw13282Labels permutation235 permutation5
    mixedMoment B raw13282step0 raw13282step0Labels = mixedMoment B raw13282step1 raw13282step1Labels := by
      have ha : raw13282step1 = -raw13282step0 := by apply Matrix.ext; change ∀ i j, raw13282step1 i j = -(raw13282step0 i j); unfold raw13282step1 raw13282step0; decide +kernel
      have hl : raw13282step1Labels = raw13282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13282step1 raw13282step1Labels = mixedMoment B raw13282step2 raw13282step2Labels := by
      have ha : raw13282step2 = raw13282step1 := by apply Matrix.ext; unfold raw13282step2 raw13282step1; decide +kernel
      have hl : raw13282step1Labels = labelEmbedding1 ∘ raw13282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13282step1 raw13282step1Labels raw13282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3503 node3503Labels := by rfl

def raw13283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13283Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13283step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw13283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13283step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13283step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13283step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13283 raw13283Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw13283 raw13283Labels = mixedMoment B raw13283step0 raw13283step0Labels := by
      have hz : ∀ j, raw13283 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13283step0 = (fun i j => raw13283 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13283step0 raw13283; decide +kernel
      have hl : raw13283step0Labels = raw13283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13283 raw13283Labels permutation590 hz
    mixedMoment B raw13283step0 raw13283step0Labels = mixedMoment B raw13283step1 raw13283step1Labels := by
      have ha : raw13283step1 = (fun i j => raw13283step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13283step1 raw13283step0; decide +kernel
      have hl : raw13283step1Labels = raw13283step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13283step0 raw13283step0Labels permutation48 permutation5
    mixedMoment B raw13283step1 raw13283step1Labels = mixedMoment B raw13283step2 raw13283step2Labels := by
      have ha : raw13283step2 = -raw13283step1 := by apply Matrix.ext; change ∀ i j, raw13283step2 i j = -(raw13283step1 i j); unfold raw13283step2 raw13283step1; decide +kernel
      have hl : raw13283step2Labels = raw13283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13283step2 raw13283step2Labels = mixedMoment B raw13283step3 raw13283step3Labels := by
      have ha : raw13283step3 = raw13283step2 := by apply Matrix.ext; unfold raw13283step3 raw13283step2; decide +kernel
      have hl : raw13283step2Labels = labelEmbedding1 ∘ raw13283step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13283step2 raw13283step2Labels raw13283step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw13284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13284step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13284 raw13284Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw13284 raw13284Labels = mixedMoment B raw13284step0 raw13284step0Labels := by
      have ha : raw13284step0 = (fun i j => raw13284 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13284step0 raw13284; decide +kernel
      have hl : raw13284step0Labels = raw13284Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13284 raw13284Labels permutation234 permutation5
    mixedMoment B raw13284step0 raw13284step0Labels = mixedMoment B raw13284step1 raw13284step1Labels := by
      have ha : raw13284step1 = -raw13284step0 := by apply Matrix.ext; change ∀ i j, raw13284step1 i j = -(raw13284step0 i j); unfold raw13284step1 raw13284step0; decide +kernel
      have hl : raw13284step1Labels = raw13284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13284step1 raw13284step1Labels = mixedMoment B raw13284step2 raw13284step2Labels := by
      have ha : raw13284step2 = raw13284step1 := by apply Matrix.ext; unfold raw13284step2 raw13284step1; decide +kernel
      have hl : raw13284step1Labels = labelEmbedding1 ∘ raw13284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13284step1 raw13284step1Labels raw13284step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw13285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13285Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw13285step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw13285step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13285step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw13285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13285 raw13285Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw13285 raw13285Labels = mixedMoment B raw13285step0 raw13285step0Labels := by
      have ha : raw13285step0 = (fun i j => raw13285 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13285step0 raw13285; decide +kernel
      have hl : raw13285step0Labels = raw13285Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13285 raw13285Labels permutation166 permutation5
    mixedMoment B raw13285step0 raw13285step0Labels = mixedMoment B raw13285step1 raw13285step1Labels := by
      have ha : raw13285step1 = -raw13285step0 := by apply Matrix.ext; change ∀ i j, raw13285step1 i j = -(raw13285step0 i j); unfold raw13285step1 raw13285step0; decide +kernel
      have hl : raw13285step1Labels = raw13285step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13285step1 raw13285step1Labels = mixedMoment B raw13285step2 raw13285step2Labels := by
      have ha : raw13285step2 = raw13285step1 := by apply Matrix.ext; unfold raw13285step2 raw13285step1; decide +kernel
      have hl : raw13285step1Labels = labelEmbedding1 ∘ raw13285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13285step1 raw13285step1Labels raw13285step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw13286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw13286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw13286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw13286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13286 raw13286Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw13286 raw13286Labels = mixedMoment B raw13286step0 raw13286step0Labels := by
      have ha : raw13286step0 = (fun i j => raw13286 (permutation190 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13286step0 raw13286; decide +kernel
      have hl : raw13286step0Labels = raw13286Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13286 raw13286Labels permutation190 permutation5
    mixedMoment B raw13286step0 raw13286step0Labels = mixedMoment B raw13286step1 raw13286step1Labels := by
      have ha : raw13286step1 = -raw13286step0 := by apply Matrix.ext; change ∀ i j, raw13286step1 i j = -(raw13286step0 i j); unfold raw13286step1 raw13286step0; decide +kernel
      have hl : raw13286step1Labels = raw13286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13286step1 raw13286step1Labels = mixedMoment B raw13286step2 raw13286step2Labels := by
      have ha : raw13286step2 = raw13286step1 := by apply Matrix.ext; unfold raw13286step2 raw13286step1; decide +kernel
      have hl : raw13286step1Labels = labelEmbedding1 ∘ raw13286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13286step1 raw13286step1Labels raw13286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw13287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13287step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13287step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13287 raw13287Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw13287 raw13287Labels = mixedMoment B raw13287step0 raw13287step0Labels := by
      have ha : raw13287step0 = (fun i j => raw13287 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13287step0 raw13287; decide +kernel
      have hl : raw13287step0Labels = raw13287Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13287 raw13287Labels permutation234 permutation5
    mixedMoment B raw13287step0 raw13287step0Labels = mixedMoment B raw13287step1 raw13287step1Labels := by
      have ha : raw13287step1 = -raw13287step0 := by apply Matrix.ext; change ∀ i j, raw13287step1 i j = -(raw13287step0 i j); unfold raw13287step1 raw13287step0; decide +kernel
      have hl : raw13287step1Labels = raw13287step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13287step1 raw13287step1Labels = mixedMoment B raw13287step2 raw13287step2Labels := by
      have ha : raw13287step2 = raw13287step1 := by apply Matrix.ext; unfold raw13287step2 raw13287step1; decide +kernel
      have hl : raw13287step1Labels = labelEmbedding1 ∘ raw13287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13287step1 raw13287step1Labels raw13287step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw13288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw13288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw13288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw13288step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13288step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw13288step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13288 raw13288Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw13288 raw13288Labels = mixedMoment B raw13288step0 raw13288step0Labels := by
      have hz : ∀ j, raw13288 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13288step0 = (fun i j => raw13288 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13288step0 raw13288; decide +kernel
      have hl : raw13288step0Labels = raw13288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13288 raw13288Labels permutation590 hz
    mixedMoment B raw13288step0 raw13288step0Labels = mixedMoment B raw13288step1 raw13288step1Labels := by
      have ha : raw13288step1 = (fun i j => raw13288step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13288step1 raw13288step0; decide +kernel
      have hl : raw13288step1Labels = raw13288step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13288step0 raw13288step0Labels permutation54 permutation5
    mixedMoment B raw13288step1 raw13288step1Labels = mixedMoment B raw13288step2 raw13288step2Labels := by
      have ha : raw13288step2 = -raw13288step1 := by apply Matrix.ext; change ∀ i j, raw13288step2 i j = -(raw13288step1 i j); unfold raw13288step2 raw13288step1; decide +kernel
      have hl : raw13288step2Labels = raw13288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13288step2 raw13288step2Labels = mixedMoment B raw13288step3 raw13288step3Labels := by
      have ha : raw13288step3 = raw13288step2 := by apply Matrix.ext; unfold raw13288step3 raw13288step2; decide +kernel
      have hl : raw13288step2Labels = labelEmbedding1 ∘ raw13288step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13288step2 raw13288step2Labels raw13288step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw13289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13289step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13289step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13289step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13289 raw13289Labels = mixedMoment B node1642 node1642Labels := by
  calc
    mixedMoment B raw13289 raw13289Labels = mixedMoment B raw13289step0 raw13289step0Labels := by
      have ha : raw13289step0 = (fun i j => raw13289 (permutation201 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13289step0 raw13289; decide +kernel
      have hl : raw13289step0Labels = raw13289Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13289 raw13289Labels permutation201 permutation5
    mixedMoment B raw13289step0 raw13289step0Labels = mixedMoment B raw13289step1 raw13289step1Labels := by
      have ha : raw13289step1 = -raw13289step0 := by apply Matrix.ext; change ∀ i j, raw13289step1 i j = -(raw13289step0 i j); unfold raw13289step1 raw13289step0; decide +kernel
      have hl : raw13289step1Labels = raw13289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13289step1 raw13289step1Labels = mixedMoment B raw13289step2 raw13289step2Labels := by
      have ha : raw13289step2 = raw13289step1 := by apply Matrix.ext; unfold raw13289step2 raw13289step1; decide +kernel
      have hl : raw13289step1Labels = labelEmbedding1 ∘ raw13289step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13289step1 raw13289step1Labels raw13289step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1642 node1642Labels := by rfl

def raw13290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13290step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13290 raw13290Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw13290 raw13290Labels = mixedMoment B raw13290step0 raw13290step0Labels := by
      have ha : raw13290step0 = (fun i j => raw13290 (permutation201 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13290step0 raw13290; decide +kernel
      have hl : raw13290step0Labels = raw13290Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13290 raw13290Labels permutation201 permutation5
    mixedMoment B raw13290step0 raw13290step0Labels = mixedMoment B raw13290step1 raw13290step1Labels := by
      have ha : raw13290step1 = -raw13290step0 := by apply Matrix.ext; change ∀ i j, raw13290step1 i j = -(raw13290step0 i j); unfold raw13290step1 raw13290step0; decide +kernel
      have hl : raw13290step1Labels = raw13290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13290step1 raw13290step1Labels = mixedMoment B raw13290step2 raw13290step2Labels := by
      have ha : raw13290step2 = raw13290step1 := by apply Matrix.ext; unfold raw13290step2 raw13290step1; decide +kernel
      have hl : raw13290step1Labels = labelEmbedding1 ∘ raw13290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13290step1 raw13290step1Labels raw13290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw13291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13291step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13291step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13291 raw13291Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw13291 raw13291Labels = mixedMoment B raw13291step0 raw13291step0Labels := by
      have ha : raw13291step0 = (fun i j => raw13291 (permutation207 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13291step0 raw13291; decide +kernel
      have hl : raw13291step0Labels = raw13291Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13291 raw13291Labels permutation207 permutation5
    mixedMoment B raw13291step0 raw13291step0Labels = mixedMoment B raw13291step1 raw13291step1Labels := by
      have ha : raw13291step1 = -raw13291step0 := by apply Matrix.ext; change ∀ i j, raw13291step1 i j = -(raw13291step0 i j); unfold raw13291step1 raw13291step0; decide +kernel
      have hl : raw13291step1Labels = raw13291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13291step1 raw13291step1Labels = mixedMoment B raw13291step2 raw13291step2Labels := by
      have ha : raw13291step2 = raw13291step1 := by apply Matrix.ext; unfold raw13291step2 raw13291step1; decide +kernel
      have hl : raw13291step1Labels = labelEmbedding1 ∘ raw13291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13291step1 raw13291step1Labels raw13291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw13292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw13292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13292step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13292 raw13292Labels = mixedMoment B node3388 node3388Labels := by
  calc
    mixedMoment B raw13292 raw13292Labels = mixedMoment B raw13292step0 raw13292step0Labels := by
      have ha : raw13292step0 = (fun i j => raw13292 (permutation201 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13292step0 raw13292; decide +kernel
      have hl : raw13292step0Labels = raw13292Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13292 raw13292Labels permutation201 permutation5
    mixedMoment B raw13292step0 raw13292step0Labels = mixedMoment B raw13292step1 raw13292step1Labels := by
      have ha : raw13292step1 = -raw13292step0 := by apply Matrix.ext; change ∀ i j, raw13292step1 i j = -(raw13292step0 i j); unfold raw13292step1 raw13292step0; decide +kernel
      have hl : raw13292step1Labels = raw13292step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13292step1 raw13292step1Labels = mixedMoment B raw13292step2 raw13292step2Labels := by
      have ha : raw13292step2 = raw13292step1 := by apply Matrix.ext; unfold raw13292step2 raw13292step1; decide +kernel
      have hl : raw13292step1Labels = labelEmbedding1 ∘ raw13292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13292step1 raw13292step1Labels raw13292step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3388 node3388Labels := by rfl

def raw13293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0]]
def raw13293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw13293step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13293step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13293 raw13293Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw13293 raw13293Labels = mixedMoment B raw13293step0 raw13293step0Labels := by
      have hz : ∀ j, raw13293 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13293step0 = (fun i j => raw13293 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13293step0 raw13293; decide +kernel
      have hl : raw13293step0Labels = raw13293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13293 raw13293Labels permutation590 hz
    mixedMoment B raw13293step0 raw13293step0Labels = mixedMoment B raw13293step1 raw13293step1Labels := by
      have ha : raw13293step1 = (fun i j => raw13293step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13293step1 raw13293step0; decide +kernel
      have hl : raw13293step1Labels = raw13293step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13293step0 raw13293step0Labels permutation44 permutation5
    mixedMoment B raw13293step1 raw13293step1Labels = mixedMoment B raw13293step2 raw13293step2Labels := by
      have ha : raw13293step2 = -raw13293step1 := by apply Matrix.ext; change ∀ i j, raw13293step2 i j = -(raw13293step1 i j); unfold raw13293step2 raw13293step1; decide +kernel
      have hl : raw13293step2Labels = raw13293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13293step2 raw13293step2Labels = mixedMoment B raw13293step3 raw13293step3Labels := by
      have ha : raw13293step3 = raw13293step2 := by apply Matrix.ext; unfold raw13293step3 raw13293step2; decide +kernel
      have hl : raw13293step2Labels = labelEmbedding1 ∘ raw13293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13293step2 raw13293step2Labels raw13293step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw13294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw13294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13294step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13294 raw13294Labels = mixedMoment B node1635 node1635Labels := by
  calc
    mixedMoment B raw13294 raw13294Labels = mixedMoment B raw13294step0 raw13294step0Labels := by
      have ha : raw13294step0 = (fun i j => raw13294 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13294step0 raw13294; decide +kernel
      have hl : raw13294step0Labels = raw13294Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13294 raw13294Labels permutation212 permutation5
    mixedMoment B raw13294step0 raw13294step0Labels = mixedMoment B raw13294step1 raw13294step1Labels := by
      have ha : raw13294step1 = -raw13294step0 := by apply Matrix.ext; change ∀ i j, raw13294step1 i j = -(raw13294step0 i j); unfold raw13294step1 raw13294step0; decide +kernel
      have hl : raw13294step1Labels = raw13294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13294step1 raw13294step1Labels = mixedMoment B raw13294step2 raw13294step2Labels := by
      have ha : raw13294step2 = raw13294step1 := by apply Matrix.ext; unfold raw13294step2 raw13294step1; decide +kernel
      have hl : raw13294step1Labels = labelEmbedding1 ∘ raw13294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13294step1 raw13294step1Labels raw13294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1635 node1635Labels := by rfl

def raw13295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw13295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13295step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13295 raw13295Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw13295 raw13295Labels = mixedMoment B raw13295step0 raw13295step0Labels := by
      have ha : raw13295step0 = (fun i j => raw13295 (permutation202 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13295step0 raw13295; decide +kernel
      have hl : raw13295step0Labels = raw13295Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13295 raw13295Labels permutation202 permutation5
    mixedMoment B raw13295step0 raw13295step0Labels = mixedMoment B raw13295step1 raw13295step1Labels := by
      have ha : raw13295step1 = -raw13295step0 := by apply Matrix.ext; change ∀ i j, raw13295step1 i j = -(raw13295step0 i j); unfold raw13295step1 raw13295step0; decide +kernel
      have hl : raw13295step1Labels = raw13295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13295step1 raw13295step1Labels = mixedMoment B raw13295step2 raw13295step2Labels := by
      have ha : raw13295step2 = raw13295step1 := by apply Matrix.ext; unfold raw13295step2 raw13295step1; decide +kernel
      have hl : raw13295step1Labels = labelEmbedding1 ∘ raw13295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13295step1 raw13295step1Labels raw13295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw13296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw13296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13296step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13296step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13296 raw13296Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw13296 raw13296Labels = mixedMoment B raw13296step0 raw13296step0Labels := by
      have ha : raw13296step0 = (fun i j => raw13296 (permutation208 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13296step0 raw13296; decide +kernel
      have hl : raw13296step0Labels = raw13296Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13296 raw13296Labels permutation208 permutation5
    mixedMoment B raw13296step0 raw13296step0Labels = mixedMoment B raw13296step1 raw13296step1Labels := by
      have ha : raw13296step1 = -raw13296step0 := by apply Matrix.ext; change ∀ i j, raw13296step1 i j = -(raw13296step0 i j); unfold raw13296step1 raw13296step0; decide +kernel
      have hl : raw13296step1Labels = raw13296step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13296step1 raw13296step1Labels = mixedMoment B raw13296step2 raw13296step2Labels := by
      have ha : raw13296step2 = raw13296step1 := by apply Matrix.ext; unfold raw13296step2 raw13296step1; decide +kernel
      have hl : raw13296step1Labels = labelEmbedding1 ∘ raw13296step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13296step1 raw13296step1Labels raw13296step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw13297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw13297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13297step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13297 raw13297Labels = mixedMoment B node3375 node3375Labels := by
  calc
    mixedMoment B raw13297 raw13297Labels = mixedMoment B raw13297step0 raw13297step0Labels := by
      have ha : raw13297step0 = (fun i j => raw13297 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13297step0 raw13297; decide +kernel
      have hl : raw13297step0Labels = raw13297Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13297 raw13297Labels permutation212 permutation5
    mixedMoment B raw13297step0 raw13297step0Labels = mixedMoment B raw13297step1 raw13297step1Labels := by
      have ha : raw13297step1 = -raw13297step0 := by apply Matrix.ext; change ∀ i j, raw13297step1 i j = -(raw13297step0 i j); unfold raw13297step1 raw13297step0; decide +kernel
      have hl : raw13297step1Labels = raw13297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13297step1 raw13297step1Labels = mixedMoment B raw13297step2 raw13297step2Labels := by
      have ha : raw13297step2 = raw13297step1 := by apply Matrix.ext; unfold raw13297step2 raw13297step1; decide +kernel
      have hl : raw13297step1Labels = labelEmbedding1 ∘ raw13297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13297step1 raw13297step1Labels raw13297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3375 node3375Labels := by rfl

def raw13298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw13298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw13298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13298step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13298step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw13298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13298 raw13298Labels = mixedMoment B node3502 node3502Labels := by
  calc
    mixedMoment B raw13298 raw13298Labels = mixedMoment B raw13298step0 raw13298step0Labels := by
      have ha : raw13298step0 = (fun i j => raw13298 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13298step0 raw13298; decide +kernel
      have hl : raw13298step0Labels = raw13298Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13298 raw13298Labels permutation234 permutation5
    mixedMoment B raw13298step0 raw13298step0Labels = mixedMoment B raw13298step1 raw13298step1Labels := by
      have ha : raw13298step1 = -raw13298step0 := by apply Matrix.ext; change ∀ i j, raw13298step1 i j = -(raw13298step0 i j); unfold raw13298step1 raw13298step0; decide +kernel
      have hl : raw13298step1Labels = raw13298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13298step1 raw13298step1Labels = mixedMoment B raw13298step2 raw13298step2Labels := by
      have ha : raw13298step2 = raw13298step1 := by apply Matrix.ext; unfold raw13298step2 raw13298step1; decide +kernel
      have hl : raw13298step1Labels = labelEmbedding1 ∘ raw13298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13298step1 raw13298step1Labels raw13298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3502 node3502Labels := by rfl

def raw13299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13299 raw13299Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13299 raw13299Labels = mixedMoment B raw13299step0 raw13299step0Labels := by
      have ha : raw13299step0 = (fun i j => raw13299 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13299step0 raw13299; decide +kernel
      have hl : raw13299step0Labels = raw13299Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13299 raw13299Labels permutation157 permutation2
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13300 raw13300Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw13300 raw13300Labels = mixedMoment B raw13300step0 raw13300step0Labels := by
      have ha : raw13300step0 = (fun i j => raw13300 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13300step0 raw13300; decide +kernel
      have hl : raw13300step0Labels = raw13300Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13300 raw13300Labels permutation157 permutation2
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw13301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13301step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13301 raw13301Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw13301 raw13301Labels = mixedMoment B raw13301step0 raw13301step0Labels := by
      have ha : raw13301step0 = (fun i j => raw13301 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13301step0 raw13301; decide +kernel
      have hl : raw13301step0Labels = raw13301Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13301 raw13301Labels permutation181 permutation2
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw13302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13302step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13302 raw13302Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw13302 raw13302Labels = mixedMoment B raw13302step0 raw13302step0Labels := by
      have ha : raw13302step0 = (fun i j => raw13302 (permutation446 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13302step0 raw13302; decide +kernel
      have hl : raw13302step0Labels = raw13302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13302 raw13302Labels permutation446 permutation4
    mixedMoment B raw13302step0 raw13302step0Labels = mixedMoment B raw13302step1 raw13302step1Labels := by
      have ha : raw13302step1 = -raw13302step0 := by apply Matrix.ext; change ∀ i j, raw13302step1 i j = -(raw13302step0 i j); unfold raw13302step1 raw13302step0; decide +kernel
      have hl : raw13302step1Labels = raw13302step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw13303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0]]
def raw13303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw13303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13303 raw13303Labels = mixedMoment B node4008 node4008Labels := by
  calc
    mixedMoment B raw13303 raw13303Labels = mixedMoment B raw13303step0 raw13303step0Labels := by
      have ha : raw13303step0 = (fun i j => raw13303 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13303step0 raw13303; decide +kernel
      have hl : raw13303step0Labels = raw13303Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13303 raw13303Labels permutation155 permutation2
    _ = mixedMoment B node4008 node4008Labels := by rfl

def raw13304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0]]
def raw13304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1]]
def raw13304step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw13304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13304 raw13304Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw13304 raw13304Labels = mixedMoment B raw13304step0 raw13304step0Labels := by
      have hz : ∀ j, raw13304 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13304step0 = (fun i j => raw13304 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13304step0 raw13304; decide +kernel
      have hl : raw13304step0Labels = raw13304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13304 raw13304Labels permutation590 hz
    mixedMoment B raw13304step0 raw13304step0Labels = mixedMoment B raw13304step1 raw13304step1Labels := by
      have ha : raw13304step1 = (fun i j => raw13304step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13304step1 raw13304step0; decide +kernel
      have hl : raw13304step1Labels = raw13304step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13304step0 raw13304step0Labels permutation33 permutation2
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw13305 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]
def raw13305Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13305step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw13305step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13305step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw13305step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13305step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw13305step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical13305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13305 raw13305Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13305 raw13305Labels = mixedMoment B raw13305step0 raw13305step0Labels := by
      have hz : ∀ j, raw13305 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw13305step0 = (fun i j => raw13305 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw13305step0 raw13305; decide +kernel
      have hl : raw13305step0Labels = raw13305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13305 raw13305Labels permutation590 hz
    mixedMoment B raw13305step0 raw13305step0Labels = mixedMoment B raw13305step1 raw13305step1Labels := by
      have ha : raw13305step1 = (fun i j => raw13305step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13305step1 raw13305step0; decide +kernel
      have hl : raw13305step1Labels = raw13305step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13305step0 raw13305step0Labels permutation122 permutation0
    mixedMoment B raw13305step1 raw13305step1Labels = mixedMoment B raw13305step2 raw13305step2Labels := by
      have ha : raw13305step2 = -raw13305step1 := by apply Matrix.ext; change ∀ i j, raw13305step2 i j = -(raw13305step1 i j); unfold raw13305step2 raw13305step1; decide +kernel
      have hl : raw13305step2Labels = raw13305step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw13306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13306 raw13306Labels = mixedMoment B node1403 node1403Labels := by
  calc
    mixedMoment B raw13306 raw13306Labels = mixedMoment B raw13306step0 raw13306step0Labels := by
      have ha : raw13306step0 = (fun i j => raw13306 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13306step0 raw13306; decide +kernel
      have hl : raw13306step0Labels = raw13306Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13306 raw13306Labels permutation181 permutation2
    _ = mixedMoment B node1403 node1403Labels := by rfl

def raw13307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13307 raw13307Labels = mixedMoment B node1403 node1403Labels := by
  calc
    mixedMoment B raw13307 raw13307Labels = mixedMoment B raw13307step0 raw13307step0Labels := by
      have ha : raw13307step0 = (fun i j => raw13307 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13307step0 raw13307; decide +kernel
      have hl : raw13307step0Labels = raw13307Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13307 raw13307Labels permutation157 permutation2
    _ = mixedMoment B node1403 node1403Labels := by rfl

def raw13308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw13308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13308 raw13308Labels = mixedMoment B node1383 node1383Labels := by
  calc
    mixedMoment B raw13308 raw13308Labels = mixedMoment B raw13308step0 raw13308step0Labels := by
      have ha : raw13308step0 = (fun i j => raw13308 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13308step0 raw13308; decide +kernel
      have hl : raw13308step0Labels = raw13308Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13308 raw13308Labels permutation157 permutation2
    _ = mixedMoment B node1383 node1383Labels := by rfl

def raw13309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw13309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw13309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13309 raw13309Labels = mixedMoment B node1384 node1384Labels := by
  calc
    mixedMoment B raw13309 raw13309Labels = mixedMoment B raw13309step0 raw13309step0Labels := by
      have ha : raw13309step0 = (fun i j => raw13309 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13309step0 raw13309; decide +kernel
      have hl : raw13309step0Labels = raw13309Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13309 raw13309Labels permutation156 permutation2
    _ = mixedMoment B node1384 node1384Labels := by rfl

def raw13310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw13310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13310 raw13310Labels = mixedMoment B node1387 node1387Labels := by
  calc
    mixedMoment B raw13310 raw13310Labels = mixedMoment B raw13310step0 raw13310step0Labels := by
      have ha : raw13310step0 = (fun i j => raw13310 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13310step0 raw13310; decide +kernel
      have hl : raw13310step0Labels = raw13310Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13310 raw13310Labels permutation154 permutation2
    _ = mixedMoment B node1387 node1387Labels := by rfl

def raw13311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw13311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13311 raw13311Labels = mixedMoment B node2951 node2951Labels := by
  calc
    mixedMoment B raw13311 raw13311Labels = mixedMoment B raw13311step0 raw13311step0Labels := by
      have ha : raw13311step0 = (fun i j => raw13311 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13311step0 raw13311; decide +kernel
      have hl : raw13311step0Labels = raw13311Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13311 raw13311Labels permutation157 permutation2
    _ = mixedMoment B node2951 node2951Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
