import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw43008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw43008Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw43008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43008step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43008step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43008step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43008 raw43008Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw43008 raw43008Labels = mixedMoment B raw43008step0 raw43008step0Labels := by
      have ha : raw43008step0 = (fun i j => raw43008 (permutation448 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43008step0 raw43008; decide +kernel
      have hl : raw43008step0Labels = raw43008Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43008 raw43008Labels permutation448 permutation4
    mixedMoment B raw43008step0 raw43008step0Labels = mixedMoment B raw43008step1 raw43008step1Labels := by
      have ha : raw43008step1 = -raw43008step0 := by apply Matrix.ext; change ∀ i j, raw43008step1 i j = -(raw43008step0 i j); unfold raw43008step1 raw43008step0; decide +kernel
      have hl : raw43008step1Labels = raw43008step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43008step1 raw43008step1Labels = mixedMoment B raw43008step2 raw43008step2Labels := by
      have ha : raw43008step2 = raw43008step1 := by apply Matrix.ext; unfold raw43008step2 raw43008step1; decide +kernel
      have hl : raw43008step1Labels = labelEmbedding1 ∘ raw43008step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43008step1 raw43008step1Labels raw43008step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw43009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw43009Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw43009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43009 raw43009Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw43009 raw43009Labels = mixedMoment B raw43009step0 raw43009step0Labels := by
      have ha : raw43009step0 = (fun i j => raw43009 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43009step0 raw43009; decide +kernel
      have hl : raw43009step0Labels = raw43009Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43009 raw43009Labels permutation506 permutation6
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw43010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43010Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw43010step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43010step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43010 raw43010Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw43010 raw43010Labels = mixedMoment B raw43010step0 raw43010step0Labels := by
      have ha : raw43010step0 = (fun i j => raw43010 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43010step0 raw43010; decide +kernel
      have hl : raw43010step0Labels = raw43010Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43010 raw43010Labels permutation683 permutation2
    mixedMoment B raw43010step0 raw43010step0Labels = mixedMoment B raw43010step1 raw43010step1Labels := by
      have ha : raw43010step1 = -raw43010step0 := by apply Matrix.ext; change ∀ i j, raw43010step1 i j = -(raw43010step0 i j); unfold raw43010step1 raw43010step0; decide +kernel
      have hl : raw43010step1Labels = raw43010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43010step1 raw43010step1Labels = mixedMoment B raw43010step2 raw43010step2Labels := by
      have ha : raw43010step2 = raw43010step1 := by apply Matrix.ext; unfold raw43010step2 raw43010step1; decide +kernel
      have hl : raw43010step1Labels = labelEmbedding1 ∘ raw43010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43010step1 raw43010step1Labels raw43010step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw43011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43011Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw43011step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw43011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw43011step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw43011step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw43011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43011 raw43011Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw43011 raw43011Labels = mixedMoment B raw43011step0 raw43011step0Labels := by
      have ha : raw43011step0 = (fun i j => raw43011 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw43011step0 raw43011; decide +kernel
      have hl : raw43011step0Labels = raw43011Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43011 raw43011Labels permutation688 permutation3
    mixedMoment B raw43011step0 raw43011step0Labels = mixedMoment B raw43011step1 raw43011step1Labels := by
      have ha : raw43011step1 = -raw43011step0 := by apply Matrix.ext; change ∀ i j, raw43011step1 i j = -(raw43011step0 i j); unfold raw43011step1 raw43011step0; decide +kernel
      have hl : raw43011step1Labels = raw43011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43011step1 raw43011step1Labels = mixedMoment B raw43011step2 raw43011step2Labels := by
      have ha : raw43011step2 = raw43011step1 := by apply Matrix.ext; unfold raw43011step2 raw43011step1; decide +kernel
      have hl : raw43011step1Labels = labelEmbedding7 ∘ raw43011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43011step1 raw43011step1Labels raw43011step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw43012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw43012Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw43012step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw43012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43012step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43012step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43012 raw43012Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw43012 raw43012Labels = mixedMoment B raw43012step0 raw43012step0Labels := by
      have hz : ∀ j, raw43012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43012step0 = (fun i j => raw43012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43012step0 raw43012; decide +kernel
      have hl : raw43012step0Labels = raw43012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43012 raw43012Labels permutation434 hz
    mixedMoment B raw43012step0 raw43012step0Labels = mixedMoment B raw43012step1 raw43012step1Labels := by
      have ha : raw43012step1 = (fun i j => raw43012step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43012step1 raw43012step0; decide +kernel
      have hl : raw43012step1Labels = raw43012step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43012step0 raw43012step0Labels permutation104 permutation4
    mixedMoment B raw43012step1 raw43012step1Labels = mixedMoment B raw43012step2 raw43012step2Labels := by
      have ha : raw43012step2 = -raw43012step1 := by apply Matrix.ext; change ∀ i j, raw43012step2 i j = -(raw43012step1 i j); unfold raw43012step2 raw43012step1; decide +kernel
      have hl : raw43012step2Labels = raw43012step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43012step2 raw43012step2Labels = mixedMoment B raw43012step3 raw43012step3Labels := by
      have ha : raw43012step3 = raw43012step2 := by apply Matrix.ext; unfold raw43012step3 raw43012step2; decide +kernel
      have hl : raw43012step2Labels = labelEmbedding1 ∘ raw43012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43012step2 raw43012step2Labels raw43012step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw43013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw43013Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw43013step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw43013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43013 raw43013Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw43013 raw43013Labels = mixedMoment B raw43013step0 raw43013step0Labels := by
      have hz : ∀ j, raw43013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43013step0 = (fun i j => raw43013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43013step0 raw43013; decide +kernel
      have hl : raw43013step0Labels = raw43013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43013 raw43013Labels permutation434 hz
    mixedMoment B raw43013step0 raw43013step0Labels = mixedMoment B raw43013step1 raw43013step1Labels := by
      have ha : raw43013step1 = (fun i j => raw43013step0 (permutation108 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43013step1 raw43013step0; decide +kernel
      have hl : raw43013step1Labels = raw43013step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43013step0 raw43013step0Labels permutation108 permutation6
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw43014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw43014Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw43014step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw43014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43014step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43014 raw43014Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw43014 raw43014Labels = mixedMoment B raw43014step0 raw43014step0Labels := by
      have hz : ∀ j, raw43014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43014step0 = (fun i j => raw43014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43014step0 raw43014; decide +kernel
      have hl : raw43014step0Labels = raw43014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43014 raw43014Labels permutation434 hz
    mixedMoment B raw43014step0 raw43014step0Labels = mixedMoment B raw43014step1 raw43014step1Labels := by
      have ha : raw43014step1 = (fun i j => raw43014step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43014step1 raw43014step0; decide +kernel
      have hl : raw43014step1Labels = raw43014step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43014step0 raw43014step0Labels permutation128 permutation4
    mixedMoment B raw43014step1 raw43014step1Labels = mixedMoment B raw43014step2 raw43014step2Labels := by
      have ha : raw43014step2 = -raw43014step1 := by apply Matrix.ext; change ∀ i j, raw43014step2 i j = -(raw43014step1 i j); unfold raw43014step2 raw43014step1; decide +kernel
      have hl : raw43014step2Labels = raw43014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43014step2 raw43014step2Labels = mixedMoment B raw43014step3 raw43014step3Labels := by
      have ha : raw43014step3 = raw43014step2 := by apply Matrix.ext; unfold raw43014step3 raw43014step2; decide +kernel
      have hl : raw43014step2Labels = labelEmbedding1 ∘ raw43014step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43014step2 raw43014step2Labels raw43014step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw43015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw43015Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw43015step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw43015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43015 raw43015Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw43015 raw43015Labels = mixedMoment B raw43015step0 raw43015step0Labels := by
      have hz : ∀ j, raw43015 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43015step0 = (fun i j => raw43015 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43015step0 raw43015; decide +kernel
      have hl : raw43015step0Labels = raw43015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43015 raw43015Labels permutation434 hz
    mixedMoment B raw43015step0 raw43015step0Labels = mixedMoment B raw43015step1 raw43015step1Labels := by
      have ha : raw43015step1 = (fun i j => raw43015step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43015step1 raw43015step0; decide +kernel
      have hl : raw43015step1Labels = raw43015step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43015step0 raw43015step0Labels permutation129 permutation6
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw43016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw43016Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw43016step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43016step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43016step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43016 raw43016Labels = mixedMoment B node3290 node3290Labels := by
  calc
    mixedMoment B raw43016 raw43016Labels = mixedMoment B raw43016step0 raw43016step0Labels := by
      have ha : raw43016step0 = (fun i j => raw43016 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43016step0 raw43016; decide +kernel
      have hl : raw43016step0Labels = raw43016Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43016 raw43016Labels permutation683 permutation2
    mixedMoment B raw43016step0 raw43016step0Labels = mixedMoment B raw43016step1 raw43016step1Labels := by
      have ha : raw43016step1 = -raw43016step0 := by apply Matrix.ext; change ∀ i j, raw43016step1 i j = -(raw43016step0 i j); unfold raw43016step1 raw43016step0; decide +kernel
      have hl : raw43016step1Labels = raw43016step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43016step1 raw43016step1Labels = mixedMoment B raw43016step2 raw43016step2Labels := by
      have ha : raw43016step2 = raw43016step1 := by apply Matrix.ext; unfold raw43016step2 raw43016step1; decide +kernel
      have hl : raw43016step1Labels = labelEmbedding1 ∘ raw43016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43016step1 raw43016step1Labels raw43016step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3290 node3290Labels := by rfl

def raw43017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw43017Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw43017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43017 raw43017Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw43017 raw43017Labels = mixedMoment B raw43017step0 raw43017step0Labels := by
      have ha : raw43017step0 = (fun i j => raw43017 (permutation600 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43017step0 raw43017; decide +kernel
      have hl : raw43017step0Labels = raw43017Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43017 raw43017Labels permutation600 permutation6
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw43018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43018Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43018step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43018 raw43018Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw43018 raw43018Labels = mixedMoment B raw43018step0 raw43018step0Labels := by
      have ha : raw43018step0 = (fun i j => raw43018 (permutation405 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43018step0 raw43018; decide +kernel
      have hl : raw43018step0Labels = raw43018Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43018 raw43018Labels permutation405 permutation4
    mixedMoment B raw43018step0 raw43018step0Labels = mixedMoment B raw43018step1 raw43018step1Labels := by
      have ha : raw43018step1 = raw43018step0 := by apply Matrix.ext; unfold raw43018step1 raw43018step0; decide +kernel
      have hl : raw43018step0Labels = labelEmbedding1 ∘ raw43018step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43018step0 raw43018step0Labels raw43018step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw43019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43019Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw43019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw43019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw43019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43019 raw43019Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw43019 raw43019Labels = mixedMoment B raw43019step0 raw43019step0Labels := by
      have ha : raw43019step0 = (fun i j => raw43019 (permutation376 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43019step0 raw43019; decide +kernel
      have hl : raw43019step0Labels = raw43019Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43019 raw43019Labels permutation376 permutation6
    mixedMoment B raw43019step0 raw43019step0Labels = mixedMoment B raw43019step1 raw43019step1Labels := by
      have ha : raw43019step1 = -raw43019step0 := by apply Matrix.ext; change ∀ i j, raw43019step1 i j = -(raw43019step0 i j); unfold raw43019step1 raw43019step0; decide +kernel
      have hl : raw43019step1Labels = raw43019step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw43020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw43020Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw43020step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw43020step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43020step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43020step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43020step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43020 raw43020Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw43020 raw43020Labels = mixedMoment B raw43020step0 raw43020step0Labels := by
      have hz : ∀ j, raw43020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43020step0 = (fun i j => raw43020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43020step0 raw43020; decide +kernel
      have hl : raw43020step0Labels = raw43020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43020 raw43020Labels permutation434 hz
    mixedMoment B raw43020step0 raw43020step0Labels = mixedMoment B raw43020step1 raw43020step1Labels := by
      have ha : raw43020step1 = (fun i j => raw43020step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43020step1 raw43020step0; decide +kernel
      have hl : raw43020step1Labels = raw43020step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43020step0 raw43020step0Labels permutation129 permutation4
    mixedMoment B raw43020step1 raw43020step1Labels = mixedMoment B raw43020step2 raw43020step2Labels := by
      have ha : raw43020step2 = -raw43020step1 := by apply Matrix.ext; change ∀ i j, raw43020step2 i j = -(raw43020step1 i j); unfold raw43020step2 raw43020step1; decide +kernel
      have hl : raw43020step2Labels = raw43020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43020step2 raw43020step2Labels = mixedMoment B raw43020step3 raw43020step3Labels := by
      have ha : raw43020step3 = raw43020step2 := by apply Matrix.ext; unfold raw43020step3 raw43020step2; decide +kernel
      have hl : raw43020step2Labels = labelEmbedding1 ∘ raw43020step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43020step2 raw43020step2Labels raw43020step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw43021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw43021Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw43021step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw43021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43021 raw43021Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw43021 raw43021Labels = mixedMoment B raw43021step0 raw43021step0Labels := by
      have hz : ∀ j, raw43021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43021step0 = (fun i j => raw43021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43021step0 raw43021; decide +kernel
      have hl : raw43021step0Labels = raw43021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43021 raw43021Labels permutation434 hz
    mixedMoment B raw43021step0 raw43021step0Labels = mixedMoment B raw43021step1 raw43021step1Labels := by
      have ha : raw43021step1 = (fun i j => raw43021step0 (permutation132 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43021step1 raw43021step0; decide +kernel
      have hl : raw43021step1Labels = raw43021step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43021step0 raw43021step0Labels permutation132 permutation6
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw43022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43022Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw43022step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43022step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43022step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43022step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43022step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43022 raw43022Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw43022 raw43022Labels = mixedMoment B raw43022step0 raw43022step0Labels := by
      have ha : raw43022step0 = (fun i j => raw43022 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43022step0 raw43022; decide +kernel
      have hl : raw43022step0Labels = raw43022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43022 raw43022Labels permutation683 permutation2
    mixedMoment B raw43022step0 raw43022step0Labels = mixedMoment B raw43022step1 raw43022step1Labels := by
      have ha : raw43022step1 = -raw43022step0 := by apply Matrix.ext; change ∀ i j, raw43022step1 i j = -(raw43022step0 i j); unfold raw43022step1 raw43022step0; decide +kernel
      have hl : raw43022step1Labels = raw43022step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43022step1 raw43022step1Labels = mixedMoment B raw43022step2 raw43022step2Labels := by
      have ha : raw43022step2 = raw43022step1 := by apply Matrix.ext; unfold raw43022step2 raw43022step1; decide +kernel
      have hl : raw43022step1Labels = labelEmbedding1 ∘ raw43022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43022step1 raw43022step1Labels raw43022step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

def raw43023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw43023Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw43023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43023 raw43023Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw43023 raw43023Labels = mixedMoment B raw43023step0 raw43023step0Labels := by
      have ha : raw43023step0 = (fun i j => raw43023 (permutation507 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43023step0 raw43023; decide +kernel
      have hl : raw43023step0Labels = raw43023Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43023 raw43023Labels permutation507 permutation6
    _ = mixedMoment B node5377 node5377Labels := by rfl

def raw43024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw43024Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 2, -4]]
def raw43024step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw43024step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43024step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43024step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43024step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43024 raw43024Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw43024 raw43024Labels = mixedMoment B raw43024step0 raw43024step0Labels := by
      have hz : ∀ j, raw43024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43024step0 = (fun i j => raw43024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43024step0 raw43024; decide +kernel
      have hl : raw43024step0Labels = raw43024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43024 raw43024Labels permutation434 hz
    mixedMoment B raw43024step0 raw43024step0Labels = mixedMoment B raw43024step1 raw43024step1Labels := by
      have ha : raw43024step1 = (fun i j => raw43024step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43024step1 raw43024step0; decide +kernel
      have hl : raw43024step1Labels = raw43024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43024step0 raw43024step0Labels permutation146 permutation2
    mixedMoment B raw43024step1 raw43024step1Labels = mixedMoment B raw43024step2 raw43024step2Labels := by
      have ha : raw43024step2 = -raw43024step1 := by apply Matrix.ext; change ∀ i j, raw43024step2 i j = -(raw43024step1 i j); unfold raw43024step2 raw43024step1; decide +kernel
      have hl : raw43024step2Labels = raw43024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43024step2 raw43024step2Labels = mixedMoment B raw43024step3 raw43024step3Labels := by
      have ha : raw43024step3 = raw43024step2 := by apply Matrix.ext; unfold raw43024step3 raw43024step2; decide +kernel
      have hl : raw43024step2Labels = labelEmbedding1 ∘ raw43024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43024step2 raw43024step2Labels raw43024step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

def raw43025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw43025Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 2, -4]]
def raw43025step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw43025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43025 raw43025Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw43025 raw43025Labels = mixedMoment B raw43025step0 raw43025step0Labels := by
      have hz : ∀ j, raw43025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43025step0 = (fun i j => raw43025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43025step0 raw43025; decide +kernel
      have hl : raw43025step0Labels = raw43025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43025 raw43025Labels permutation434 hz
    mixedMoment B raw43025step0 raw43025step0Labels = mixedMoment B raw43025step1 raw43025step1Labels := by
      have ha : raw43025step1 = (fun i j => raw43025step0 (permutation132 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43025step1 raw43025step0; decide +kernel
      have hl : raw43025step1Labels = raw43025step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43025step0 raw43025step0Labels permutation132 permutation6
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw43026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw43026Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw43026step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw43026step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43026step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw43026step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43026step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw43026step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43026 raw43026Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw43026 raw43026Labels = mixedMoment B raw43026step0 raw43026step0Labels := by
      have hz : ∀ j, raw43026 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw43026step0 = (fun i j => raw43026 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw43026step0 raw43026; decide +kernel
      have hl : raw43026step0Labels = raw43026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43026 raw43026Labels permutation520 hz
    mixedMoment B raw43026step0 raw43026step0Labels = mixedMoment B raw43026step1 raw43026step1Labels := by
      have ha : raw43026step1 = (fun i j => raw43026step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43026step1 raw43026step0; decide +kernel
      have hl : raw43026step1Labels = raw43026step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43026step0 raw43026step0Labels permutation104 permutation4
    mixedMoment B raw43026step1 raw43026step1Labels = mixedMoment B raw43026step2 raw43026step2Labels := by
      have ha : raw43026step2 = -raw43026step1 := by apply Matrix.ext; change ∀ i j, raw43026step2 i j = -(raw43026step1 i j); unfold raw43026step2 raw43026step1; decide +kernel
      have hl : raw43026step2Labels = raw43026step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43026step2 raw43026step2Labels = mixedMoment B raw43026step3 raw43026step3Labels := by
      have ha : raw43026step3 = raw43026step2 := by apply Matrix.ext; unfold raw43026step3 raw43026step2; decide +kernel
      have hl : raw43026step2Labels = labelEmbedding1 ∘ raw43026step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43026step2 raw43026step2Labels raw43026step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw43027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw43027Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw43027step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw43027step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw43027step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43027step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw43027step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43027 raw43027Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw43027 raw43027Labels = mixedMoment B raw43027step0 raw43027step0Labels := by
      have hz : ∀ j, raw43027 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw43027step0 = (fun i j => raw43027 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw43027step0 raw43027; decide +kernel
      have hl : raw43027step0Labels = raw43027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43027 raw43027Labels permutation520 hz
    mixedMoment B raw43027step0 raw43027step0Labels = mixedMoment B raw43027step1 raw43027step1Labels := by
      have ha : raw43027step1 = (fun i j => raw43027step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43027step1 raw43027step0; decide +kernel
      have hl : raw43027step1Labels = raw43027step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43027step0 raw43027step0Labels permutation104 permutation4
    mixedMoment B raw43027step1 raw43027step1Labels = mixedMoment B raw43027step2 raw43027step2Labels := by
      have ha : raw43027step2 = -raw43027step1 := by apply Matrix.ext; change ∀ i j, raw43027step2 i j = -(raw43027step1 i j); unfold raw43027step2 raw43027step1; decide +kernel
      have hl : raw43027step2Labels = raw43027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43027step2 raw43027step2Labels = mixedMoment B raw43027step3 raw43027step3Labels := by
      have ha : raw43027step3 = raw43027step2 := by apply Matrix.ext; unfold raw43027step3 raw43027step2; decide +kernel
      have hl : raw43027step2Labels = labelEmbedding10 ∘ raw43027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43027step2 raw43027step2Labels raw43027step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4886 node4886Labels := by rfl

def raw43028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw43028Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw43028step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw43028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43028step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw43028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43028 raw43028Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw43028 raw43028Labels = mixedMoment B raw43028step0 raw43028step0Labels := by
      have ha : raw43028step0 = (fun i j => raw43028 (permutation484 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43028step0 raw43028; decide +kernel
      have hl : raw43028step0Labels = raw43028Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43028 raw43028Labels permutation484 permutation4
    mixedMoment B raw43028step0 raw43028step0Labels = mixedMoment B raw43028step1 raw43028step1Labels := by
      have ha : raw43028step1 = -raw43028step0 := by apply Matrix.ext; change ∀ i j, raw43028step1 i j = -(raw43028step0 i j); unfold raw43028step1 raw43028step0; decide +kernel
      have hl : raw43028step1Labels = raw43028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43028step1 raw43028step1Labels = mixedMoment B raw43028step2 raw43028step2Labels := by
      have ha : raw43028step2 = raw43028step1 := by apply Matrix.ext; unfold raw43028step2 raw43028step1; decide +kernel
      have hl : raw43028step1Labels = labelEmbedding1 ∘ raw43028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43028step1 raw43028step1Labels raw43028step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2187 node2187Labels := by rfl

def raw43029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, 0, -1], ![2, -3, 1]]
def raw43029Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw43029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43029 raw43029Labels = mixedMoment B node4830 node4830Labels := by
  calc
    mixedMoment B raw43029 raw43029Labels = mixedMoment B raw43029step0 raw43029step0Labels := by
      have ha : raw43029step0 = (fun i j => raw43029 (permutation484 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43029step0 raw43029; decide +kernel
      have hl : raw43029step0Labels = raw43029Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43029 raw43029Labels permutation484 permutation6
    _ = mixedMoment B node4830 node4830Labels := by rfl

def raw43030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw43030Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw43030step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43030step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43030 raw43030Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw43030 raw43030Labels = mixedMoment B raw43030step0 raw43030step0Labels := by
      have ha : raw43030step0 = (fun i j => raw43030 (permutation434 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43030step0 raw43030; decide +kernel
      have hl : raw43030step0Labels = raw43030Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43030 raw43030Labels permutation434 permutation4
    mixedMoment B raw43030step0 raw43030step0Labels = mixedMoment B raw43030step1 raw43030step1Labels := by
      have ha : raw43030step1 = -raw43030step0 := by apply Matrix.ext; change ∀ i j, raw43030step1 i j = -(raw43030step0 i j); unfold raw43030step1 raw43030step0; decide +kernel
      have hl : raw43030step1Labels = raw43030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43030step1 raw43030step1Labels = mixedMoment B raw43030step2 raw43030step2Labels := by
      have ha : raw43030step2 = raw43030step1 := by apply Matrix.ext; unfold raw43030step2 raw43030step1; decide +kernel
      have hl : raw43030step1Labels = labelEmbedding1 ∘ raw43030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43030step1 raw43030step1Labels raw43030step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2233 node2233Labels := by rfl

def raw43031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw43031Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw43031step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43031step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw43031step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43031 raw43031Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw43031 raw43031Labels = mixedMoment B raw43031step0 raw43031step0Labels := by
      have ha : raw43031step0 = (fun i j => raw43031 (permutation434 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43031step0 raw43031; decide +kernel
      have hl : raw43031step0Labels = raw43031Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43031 raw43031Labels permutation434 permutation4
    mixedMoment B raw43031step0 raw43031step0Labels = mixedMoment B raw43031step1 raw43031step1Labels := by
      have ha : raw43031step1 = -raw43031step0 := by apply Matrix.ext; change ∀ i j, raw43031step1 i j = -(raw43031step0 i j); unfold raw43031step1 raw43031step0; decide +kernel
      have hl : raw43031step1Labels = raw43031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43031step1 raw43031step1Labels = mixedMoment B raw43031step2 raw43031step2Labels := by
      have ha : raw43031step2 = raw43031step1 := by apply Matrix.ext; unfold raw43031step2 raw43031step1; decide +kernel
      have hl : raw43031step1Labels = labelEmbedding10 ∘ raw43031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43031step1 raw43031step1Labels raw43031step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw43032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw43032Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw43032step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw43032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43032step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw43032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43032 raw43032Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw43032 raw43032Labels = mixedMoment B raw43032step0 raw43032step0Labels := by
      have ha : raw43032step0 = (fun i j => raw43032 (permutation435 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43032step0 raw43032; decide +kernel
      have hl : raw43032step0Labels = raw43032Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43032 raw43032Labels permutation435 permutation4
    mixedMoment B raw43032step0 raw43032step0Labels = mixedMoment B raw43032step1 raw43032step1Labels := by
      have ha : raw43032step1 = -raw43032step0 := by apply Matrix.ext; change ∀ i j, raw43032step1 i j = -(raw43032step0 i j); unfold raw43032step1 raw43032step0; decide +kernel
      have hl : raw43032step1Labels = raw43032step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43032step1 raw43032step1Labels = mixedMoment B raw43032step2 raw43032step2Labels := by
      have ha : raw43032step2 = raw43032step1 := by apply Matrix.ext; unfold raw43032step2 raw43032step1; decide +kernel
      have hl : raw43032step1Labels = labelEmbedding1 ∘ raw43032step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43032step1 raw43032step1Labels raw43032step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2232 node2232Labels := by rfl

def raw43033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw43033Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw43033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43033 raw43033Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw43033 raw43033Labels = mixedMoment B raw43033step0 raw43033step0Labels := by
      have ha : raw43033step0 = (fun i j => raw43033 (permutation505 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43033step0 raw43033; decide +kernel
      have hl : raw43033step0Labels = raw43033Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43033 raw43033Labels permutation505 permutation6
    _ = mixedMoment B node4863 node4863Labels := by rfl

def raw43034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw43034Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw43034step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw43034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43034step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw43034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43034 raw43034Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw43034 raw43034Labels = mixedMoment B raw43034step0 raw43034step0Labels := by
      have ha : raw43034step0 = (fun i j => raw43034 (permutation659 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43034step0 raw43034; decide +kernel
      have hl : raw43034step0Labels = raw43034Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43034 raw43034Labels permutation659 permutation2
    mixedMoment B raw43034step0 raw43034step0Labels = mixedMoment B raw43034step1 raw43034step1Labels := by
      have ha : raw43034step1 = -raw43034step0 := by apply Matrix.ext; change ∀ i j, raw43034step1 i j = -(raw43034step0 i j); unfold raw43034step1 raw43034step0; decide +kernel
      have hl : raw43034step1Labels = raw43034step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43034step1 raw43034step1Labels = mixedMoment B raw43034step2 raw43034step2Labels := by
      have ha : raw43034step2 = raw43034step1 := by apply Matrix.ext; unfold raw43034step2 raw43034step1; decide +kernel
      have hl : raw43034step1Labels = labelEmbedding1 ∘ raw43034step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43034step1 raw43034step1Labels raw43034step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3221 node3221Labels := by rfl

def raw43035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw43035Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43035step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw43035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw43035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43035 raw43035Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw43035 raw43035Labels = mixedMoment B raw43035step0 raw43035step0Labels := by
      have ha : raw43035step0 = (fun i j => raw43035 (permutation591 i) (permutation5 j)) := by apply Matrix.ext; unfold raw43035step0 raw43035; decide +kernel
      have hl : raw43035step0Labels = raw43035Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43035 raw43035Labels permutation591 permutation5
    mixedMoment B raw43035step0 raw43035step0Labels = mixedMoment B raw43035step1 raw43035step1Labels := by
      have ha : raw43035step1 = raw43035step0 := by apply Matrix.ext; unfold raw43035step1 raw43035step0; decide +kernel
      have hl : raw43035step0Labels = labelEmbedding9 ∘ raw43035step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43035step0 raw43035step0Labels raw43035step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw43036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw43036Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw43036step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw43036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43036 raw43036Labels = mixedMoment B node3059 node3059Labels := by
  calc
    mixedMoment B raw43036 raw43036Labels = mixedMoment B raw43036step0 raw43036step0Labels := by
      have ha : raw43036step0 = (fun i j => raw43036 (permutation591 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43036step0 raw43036; decide +kernel
      have hl : raw43036step0Labels = raw43036Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43036 raw43036Labels permutation591 permutation4
    mixedMoment B raw43036step0 raw43036step0Labels = mixedMoment B raw43036step1 raw43036step1Labels := by
      have ha : raw43036step1 = raw43036step0 := by apply Matrix.ext; unfold raw43036step1 raw43036step0; decide +kernel
      have hl : raw43036step0Labels = labelEmbedding1 ∘ raw43036step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43036step0 raw43036step0Labels raw43036step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3059 node3059Labels := by rfl

def raw43037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw43037Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw43037step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw43037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw43037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43037 raw43037Labels = mixedMoment B node5277 node5277Labels := by
  calc
    mixedMoment B raw43037 raw43037Labels = mixedMoment B raw43037step0 raw43037step0Labels := by
      have ha : raw43037step0 = (fun i j => raw43037 (permutation591 i) (permutation5 j)) := by apply Matrix.ext; unfold raw43037step0 raw43037; decide +kernel
      have hl : raw43037step0Labels = raw43037Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43037 raw43037Labels permutation591 permutation5
    mixedMoment B raw43037step0 raw43037step0Labels = mixedMoment B raw43037step1 raw43037step1Labels := by
      have ha : raw43037step1 = raw43037step0 := by apply Matrix.ext; unfold raw43037step1 raw43037step0; decide +kernel
      have hl : raw43037step0Labels = labelEmbedding9 ∘ raw43037step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43037step0 raw43037step0Labels raw43037step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5277 node5277Labels := by rfl

def raw43038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw43038Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw43038step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw43038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43038 raw43038Labels = mixedMoment B node2690 node2690Labels := by
  calc
    mixedMoment B raw43038 raw43038Labels = mixedMoment B raw43038step0 raw43038step0Labels := by
      have ha : raw43038step0 = (fun i j => raw43038 (permutation521 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43038step0 raw43038; decide +kernel
      have hl : raw43038step0Labels = raw43038Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43038 raw43038Labels permutation521 permutation4
    mixedMoment B raw43038step0 raw43038step0Labels = mixedMoment B raw43038step1 raw43038step1Labels := by
      have ha : raw43038step1 = raw43038step0 := by apply Matrix.ext; unfold raw43038step1 raw43038step0; decide +kernel
      have hl : raw43038step0Labels = labelEmbedding1 ∘ raw43038step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43038step0 raw43038step0Labels raw43038step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2690 node2690Labels := by rfl

def raw43039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw43039Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw43039step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw43039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw43039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43039 raw43039Labels = mixedMoment B node4975 node4975Labels := by
  calc
    mixedMoment B raw43039 raw43039Labels = mixedMoment B raw43039step0 raw43039step0Labels := by
      have ha : raw43039step0 = (fun i j => raw43039 (permutation647 i) (permutation7 j)) := by apply Matrix.ext; unfold raw43039step0 raw43039; decide +kernel
      have hl : raw43039step0Labels = raw43039Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43039 raw43039Labels permutation647 permutation7
    mixedMoment B raw43039step0 raw43039step0Labels = mixedMoment B raw43039step1 raw43039step1Labels := by
      have ha : raw43039step1 = raw43039step0 := by apply Matrix.ext; unfold raw43039step1 raw43039step0; decide +kernel
      have hl : raw43039step0Labels = labelEmbedding6 ∘ raw43039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43039step0 raw43039step0Labels raw43039step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4975 node4975Labels := by rfl

def raw43040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw43040Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw43040step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw43040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43040 raw43040Labels = mixedMoment B node3058 node3058Labels := by
  calc
    mixedMoment B raw43040 raw43040Labels = mixedMoment B raw43040step0 raw43040step0Labels := by
      have ha : raw43040step0 = (fun i j => raw43040 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43040step0 raw43040; decide +kernel
      have hl : raw43040step0Labels = raw43040Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43040 raw43040Labels permutation590 permutation4
    mixedMoment B raw43040step0 raw43040step0Labels = mixedMoment B raw43040step1 raw43040step1Labels := by
      have ha : raw43040step1 = raw43040step0 := by apply Matrix.ext; unfold raw43040step1 raw43040step0; decide +kernel
      have hl : raw43040step0Labels = labelEmbedding1 ∘ raw43040step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43040step0 raw43040step0Labels raw43040step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3058 node3058Labels := by rfl

def raw43041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw43041Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw43041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43041 raw43041Labels = mixedMoment B node5097 node5097Labels := by
  calc
    mixedMoment B raw43041 raw43041Labels = mixedMoment B raw43041step0 raw43041step0Labels := by
      have ha : raw43041step0 = (fun i j => raw43041 (permutation553 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43041step0 raw43041; decide +kernel
      have hl : raw43041step0Labels = raw43041Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43041 raw43041Labels permutation553 permutation6
    _ = mixedMoment B node5097 node5097Labels := by rfl

def raw43042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw43042Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw43042step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw43042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43042 raw43042Labels = mixedMoment B node2688 node2688Labels := by
  calc
    mixedMoment B raw43042 raw43042Labels = mixedMoment B raw43042step0 raw43042step0Labels := by
      have ha : raw43042step0 = (fun i j => raw43042 (permutation520 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43042step0 raw43042; decide +kernel
      have hl : raw43042step0Labels = raw43042Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43042 raw43042Labels permutation520 permutation4
    mixedMoment B raw43042step0 raw43042step0Labels = mixedMoment B raw43042step1 raw43042step1Labels := by
      have ha : raw43042step1 = raw43042step0 := by apply Matrix.ext; unfold raw43042step1 raw43042step0; decide +kernel
      have hl : raw43042step0Labels = labelEmbedding1 ∘ raw43042step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43042step0 raw43042step0Labels raw43042step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2688 node2688Labels := by rfl

def raw43043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw43043Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw43043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43043 raw43043Labels = mixedMoment B node4540 node4540Labels := by
  calc
    mixedMoment B raw43043 raw43043Labels = mixedMoment B raw43043step0 raw43043step0Labels := by
      have ha : raw43043step0 = (fun i j => raw43043 (permutation647 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43043step0 raw43043; decide +kernel
      have hl : raw43043step0Labels = raw43043Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43043 raw43043Labels permutation647 permutation6
    _ = mixedMoment B node4540 node4540Labels := by rfl

def raw43044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw43044Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 3, -4], ![2, -3, 1]]
def raw43044step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw43044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw43044step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43044step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw43044step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43044 raw43044Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw43044 raw43044Labels = mixedMoment B raw43044step0 raw43044step0Labels := by
      have hz : ∀ j, raw43044 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43044step0 = (fun i j => raw43044 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43044step0 raw43044; decide +kernel
      have hl : raw43044step0Labels = raw43044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43044 raw43044Labels permutation434 hz
    mixedMoment B raw43044step0 raw43044step0Labels = mixedMoment B raw43044step1 raw43044step1Labels := by
      have ha : raw43044step1 = (fun i j => raw43044step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43044step1 raw43044step0; decide +kernel
      have hl : raw43044step1Labels = raw43044step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43044step0 raw43044step0Labels permutation104 permutation4
    mixedMoment B raw43044step1 raw43044step1Labels = mixedMoment B raw43044step2 raw43044step2Labels := by
      have ha : raw43044step2 = -raw43044step1 := by apply Matrix.ext; change ∀ i j, raw43044step2 i j = -(raw43044step1 i j); unfold raw43044step2 raw43044step1; decide +kernel
      have hl : raw43044step2Labels = raw43044step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43044step2 raw43044step2Labels = mixedMoment B raw43044step3 raw43044step3Labels := by
      have ha : raw43044step3 = raw43044step2 := by apply Matrix.ext; unfold raw43044step3 raw43044step2; decide +kernel
      have hl : raw43044step2Labels = labelEmbedding1 ∘ raw43044step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43044step2 raw43044step2Labels raw43044step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1700 node1700Labels := by rfl

def raw43045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 3, -4], ![2, -3, 1]]
def raw43045Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 3, -4], ![2, -3, 1]]
def raw43045step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw43045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43045 raw43045Labels = mixedMoment B node4494 node4494Labels := by
  calc
    mixedMoment B raw43045 raw43045Labels = mixedMoment B raw43045step0 raw43045step0Labels := by
      have hz : ∀ j, raw43045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43045step0 = (fun i j => raw43045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43045step0 raw43045; decide +kernel
      have hl : raw43045step0Labels = raw43045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43045 raw43045Labels permutation434 hz
    mixedMoment B raw43045step0 raw43045step0Labels = mixedMoment B raw43045step1 raw43045step1Labels := by
      have ha : raw43045step1 = (fun i j => raw43045step0 (permutation104 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43045step1 raw43045step0; decide +kernel
      have hl : raw43045step1Labels = raw43045step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43045step0 raw43045step0Labels permutation104 permutation6
    _ = mixedMoment B node4494 node4494Labels := by rfl

def raw43046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw43046Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw43046step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw43046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43046step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw43046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43046 raw43046Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw43046 raw43046Labels = mixedMoment B raw43046step0 raw43046step0Labels := by
      have ha : raw43046step0 = (fun i j => raw43046 (permutation520 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43046step0 raw43046; decide +kernel
      have hl : raw43046step0Labels = raw43046Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43046 raw43046Labels permutation520 permutation4
    mixedMoment B raw43046step0 raw43046step0Labels = mixedMoment B raw43046step1 raw43046step1Labels := by
      have ha : raw43046step1 = -raw43046step0 := by apply Matrix.ext; change ∀ i j, raw43046step1 i j = -(raw43046step0 i j); unfold raw43046step1 raw43046step0; decide +kernel
      have hl : raw43046step1Labels = raw43046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43046step1 raw43046step1Labels = mixedMoment B raw43046step2 raw43046step2Labels := by
      have ha : raw43046step2 = raw43046step1 := by apply Matrix.ext; unfold raw43046step2 raw43046step1; decide +kernel
      have hl : raw43046step1Labels = labelEmbedding1 ∘ raw43046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43046step1 raw43046step1Labels raw43046step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw43047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw43047Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw43047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43047 raw43047Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw43047 raw43047Labels = mixedMoment B raw43047step0 raw43047step0Labels := by
      have ha : raw43047step0 = (fun i j => raw43047 (permutation569 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43047step0 raw43047; decide +kernel
      have hl : raw43047step0Labels = raw43047Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43047 raw43047Labels permutation569 permutation6
    _ = mixedMoment B node4473 node4473Labels := by rfl

def raw43048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw43048Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw43048step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43048step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43048 raw43048Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw43048 raw43048Labels = mixedMoment B raw43048step0 raw43048step0Labels := by
      have ha : raw43048step0 = (fun i j => raw43048 (permutation590 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43048step0 raw43048; decide +kernel
      have hl : raw43048step0Labels = raw43048Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43048 raw43048Labels permutation590 permutation4
    mixedMoment B raw43048step0 raw43048step0Labels = mixedMoment B raw43048step1 raw43048step1Labels := by
      have ha : raw43048step1 = -raw43048step0 := by apply Matrix.ext; change ∀ i j, raw43048step1 i j = -(raw43048step0 i j); unfold raw43048step1 raw43048step0; decide +kernel
      have hl : raw43048step1Labels = raw43048step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43048step1 raw43048step1Labels = mixedMoment B raw43048step2 raw43048step2Labels := by
      have ha : raw43048step2 = raw43048step1 := by apply Matrix.ext; unfold raw43048step2 raw43048step1; decide +kernel
      have hl : raw43048step1Labels = labelEmbedding1 ∘ raw43048step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43048step1 raw43048step1Labels raw43048step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1502 node1502Labels := by rfl

def raw43049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw43049Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43049 raw43049Labels = mixedMoment B node4169 node4169Labels := by
  calc
    mixedMoment B raw43049 raw43049Labels = mixedMoment B raw43049step0 raw43049step0Labels := by
      have ha : raw43049step0 = (fun i j => raw43049 (permutation590 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43049step0 raw43049; decide +kernel
      have hl : raw43049step0Labels = raw43049Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43049 raw43049Labels permutation590 permutation6
    _ = mixedMoment B node4169 node4169Labels := by rfl

def raw43050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw43050Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw43050step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw43050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43050step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw43050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43050 raw43050Labels = mixedMoment B node1501 node1501Labels := by
  calc
    mixedMoment B raw43050 raw43050Labels = mixedMoment B raw43050step0 raw43050step0Labels := by
      have ha : raw43050step0 = (fun i j => raw43050 (permutation591 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43050step0 raw43050; decide +kernel
      have hl : raw43050step0Labels = raw43050Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43050 raw43050Labels permutation591 permutation4
    mixedMoment B raw43050step0 raw43050step0Labels = mixedMoment B raw43050step1 raw43050step1Labels := by
      have ha : raw43050step1 = -raw43050step0 := by apply Matrix.ext; change ∀ i j, raw43050step1 i j = -(raw43050step0 i j); unfold raw43050step1 raw43050step0; decide +kernel
      have hl : raw43050step1Labels = raw43050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43050step1 raw43050step1Labels = mixedMoment B raw43050step2 raw43050step2Labels := by
      have ha : raw43050step2 = raw43050step1 := by apply Matrix.ext; unfold raw43050step2 raw43050step1; decide +kernel
      have hl : raw43050step1Labels = labelEmbedding1 ∘ raw43050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43050step1 raw43050step1Labels raw43050step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1501 node1501Labels := by rfl

def raw43051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw43051Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw43051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43051 raw43051Labels = mixedMoment B node4149 node4149Labels := by
  calc
    mixedMoment B raw43051 raw43051Labels = mixedMoment B raw43051step0 raw43051step0Labels := by
      have ha : raw43051step0 = (fun i j => raw43051 (permutation665 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43051step0 raw43051; decide +kernel
      have hl : raw43051step0Labels = raw43051Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43051 raw43051Labels permutation665 permutation6
    _ = mixedMoment B node4149 node4149Labels := by rfl

def raw43052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw43052Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw43052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43052 raw43052Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw43052 raw43052Labels = mixedMoment B raw43052step0 raw43052step0Labels := by
      have ha : raw43052step0 = (fun i j => raw43052 (permutation484 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43052step0 raw43052; decide +kernel
      have hl : raw43052step0Labels = raw43052Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43052 raw43052Labels permutation484 permutation4
    mixedMoment B raw43052step0 raw43052step0Labels = mixedMoment B raw43052step1 raw43052step1Labels := by
      have ha : raw43052step1 = -raw43052step0 := by apply Matrix.ext; change ∀ i j, raw43052step1 i j = -(raw43052step0 i j); unfold raw43052step1 raw43052step0; decide +kernel
      have hl : raw43052step1Labels = raw43052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43052step1 raw43052step1Labels = mixedMoment B raw43052step2 raw43052step2Labels := by
      have ha : raw43052step2 = raw43052step1 := by apply Matrix.ext; unfold raw43052step2 raw43052step1; decide +kernel
      have hl : raw43052step1Labels = labelEmbedding1 ∘ raw43052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43052step1 raw43052step1Labels raw43052step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw43053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw43053Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw43053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43053 raw43053Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw43053 raw43053Labels = mixedMoment B raw43053step0 raw43053step0Labels := by
      have ha : raw43053step0 = (fun i j => raw43053 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43053step0 raw43053; decide +kernel
      have hl : raw43053step0Labels = raw43053Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43053 raw43053Labels permutation499 permutation6
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw43054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw43054Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw43054step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43054step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw43054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43054 raw43054Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw43054 raw43054Labels = mixedMoment B raw43054step0 raw43054step0Labels := by
      have ha : raw43054step0 = (fun i j => raw43054 (permutation439 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43054step0 raw43054; decide +kernel
      have hl : raw43054step0Labels = raw43054Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43054 raw43054Labels permutation439 permutation4
    mixedMoment B raw43054step0 raw43054step0Labels = mixedMoment B raw43054step1 raw43054step1Labels := by
      have ha : raw43054step1 = -raw43054step0 := by apply Matrix.ext; change ∀ i j, raw43054step1 i j = -(raw43054step0 i j); unfold raw43054step1 raw43054step0; decide +kernel
      have hl : raw43054step1Labels = raw43054step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43054step1 raw43054step1Labels = mixedMoment B raw43054step2 raw43054step2Labels := by
      have ha : raw43054step2 = raw43054step1 := by apply Matrix.ext; unfold raw43054step2 raw43054step1; decide +kernel
      have hl : raw43054step1Labels = labelEmbedding1 ∘ raw43054step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43054step1 raw43054step1Labels raw43054step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw43055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw43055Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw43055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43055 raw43055Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw43055 raw43055Labels = mixedMoment B raw43055step0 raw43055step0Labels := by
      have ha : raw43055step0 = (fun i j => raw43055 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43055step0 raw43055; decide +kernel
      have hl : raw43055step0Labels = raw43055Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43055 raw43055Labels permutation514 permutation6
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw43056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw43056Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw43056step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43056step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43056step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43056 raw43056Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw43056 raw43056Labels = mixedMoment B raw43056step0 raw43056step0Labels := by
      have ha : raw43056step0 = (fun i j => raw43056 (permutation505 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43056step0 raw43056; decide +kernel
      have hl : raw43056step0Labels = raw43056Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43056 raw43056Labels permutation505 permutation4
    mixedMoment B raw43056step0 raw43056step0Labels = mixedMoment B raw43056step1 raw43056step1Labels := by
      have ha : raw43056step1 = -raw43056step0 := by apply Matrix.ext; change ∀ i j, raw43056step1 i j = -(raw43056step0 i j); unfold raw43056step1 raw43056step0; decide +kernel
      have hl : raw43056step1Labels = raw43056step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43056step1 raw43056step1Labels = mixedMoment B raw43056step2 raw43056step2Labels := by
      have ha : raw43056step2 = raw43056step1 := by apply Matrix.ext; unfold raw43056step2 raw43056step1; decide +kernel
      have hl : raw43056step1Labels = labelEmbedding1 ∘ raw43056step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43056step1 raw43056step1Labels raw43056step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

def raw43057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw43057Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw43057step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43057 raw43057Labels = mixedMoment B node4677 node4677Labels := by
  calc
    mixedMoment B raw43057 raw43057Labels = mixedMoment B raw43057step0 raw43057step0Labels := by
      have ha : raw43057step0 = (fun i j => raw43057 (permutation506 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43057step0 raw43057; decide +kernel
      have hl : raw43057step0Labels = raw43057Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43057 raw43057Labels permutation506 permutation6
    _ = mixedMoment B node4677 node4677Labels := by rfl

def raw43058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw43058Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw43058step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw43058step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43058step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw43058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43058 raw43058Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw43058 raw43058Labels = mixedMoment B raw43058step0 raw43058step0Labels := by
      have ha : raw43058step0 = (fun i j => raw43058 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43058step0 raw43058; decide +kernel
      have hl : raw43058step0Labels = raw43058Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43058 raw43058Labels permutation683 permutation2
    mixedMoment B raw43058step0 raw43058step0Labels = mixedMoment B raw43058step1 raw43058step1Labels := by
      have ha : raw43058step1 = -raw43058step0 := by apply Matrix.ext; change ∀ i j, raw43058step1 i j = -(raw43058step0 i j); unfold raw43058step1 raw43058step0; decide +kernel
      have hl : raw43058step1Labels = raw43058step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43058step1 raw43058step1Labels = mixedMoment B raw43058step2 raw43058step2Labels := by
      have ha : raw43058step2 = raw43058step1 := by apply Matrix.ext; unfold raw43058step2 raw43058step1; decide +kernel
      have hl : raw43058step1Labels = labelEmbedding1 ∘ raw43058step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43058step1 raw43058step1Labels raw43058step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

def raw43059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw43059Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43059step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw43059step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw43059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43059 raw43059Labels = mixedMoment B node4964 node4964Labels := by
  calc
    mixedMoment B raw43059 raw43059Labels = mixedMoment B raw43059step0 raw43059step0Labels := by
      have ha : raw43059step0 = (fun i j => raw43059 (permutation659 i) (permutation7 j)) := by apply Matrix.ext; unfold raw43059step0 raw43059; decide +kernel
      have hl : raw43059step0Labels = raw43059Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43059 raw43059Labels permutation659 permutation7
    mixedMoment B raw43059step0 raw43059step0Labels = mixedMoment B raw43059step1 raw43059step1Labels := by
      have ha : raw43059step1 = raw43059step0 := by apply Matrix.ext; unfold raw43059step1 raw43059step0; decide +kernel
      have hl : raw43059step0Labels = labelEmbedding6 ∘ raw43059step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43059step0 raw43059step0Labels raw43059step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4964 node4964Labels := by rfl

def raw43060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw43060Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw43060step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43060step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43060step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43060 raw43060Labels = mixedMoment B node3257 node3257Labels := by
  calc
    mixedMoment B raw43060 raw43060Labels = mixedMoment B raw43060step0 raw43060step0Labels := by
      have ha : raw43060step0 = (fun i j => raw43060 (permutation647 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43060step0 raw43060; decide +kernel
      have hl : raw43060step0Labels = raw43060Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43060 raw43060Labels permutation647 permutation4
    mixedMoment B raw43060step0 raw43060step0Labels = mixedMoment B raw43060step1 raw43060step1Labels := by
      have ha : raw43060step1 = -raw43060step0 := by apply Matrix.ext; change ∀ i j, raw43060step1 i j = -(raw43060step0 i j); unfold raw43060step1 raw43060step0; decide +kernel
      have hl : raw43060step1Labels = raw43060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43060step1 raw43060step1Labels = mixedMoment B raw43060step2 raw43060step2Labels := by
      have ha : raw43060step2 = raw43060step1 := by apply Matrix.ext; unfold raw43060step2 raw43060step1; decide +kernel
      have hl : raw43060step1Labels = labelEmbedding1 ∘ raw43060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43060step1 raw43060step1Labels raw43060step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3257 node3257Labels := by rfl

def raw43061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw43061Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw43061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43061 raw43061Labels = mixedMoment B node4542 node4542Labels := by
  calc
    mixedMoment B raw43061 raw43061Labels = mixedMoment B raw43061step0 raw43061step0Labels := by
      have ha : raw43061step0 = (fun i j => raw43061 (permutation648 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43061step0 raw43061; decide +kernel
      have hl : raw43061step0Labels = raw43061Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43061 raw43061Labels permutation648 permutation6
    _ = mixedMoment B node4542 node4542Labels := by rfl

def raw43062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw43062Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw43062step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw43062step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43062step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw43062step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43062 raw43062Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw43062 raw43062Labels = mixedMoment B raw43062step0 raw43062step0Labels := by
      have hz : ∀ j, raw43062 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43062step0 = (fun i j => raw43062 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43062step0 raw43062; decide +kernel
      have hl : raw43062step0Labels = raw43062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43062 raw43062Labels permutation434 hz
    mixedMoment B raw43062step0 raw43062step0Labels = mixedMoment B raw43062step1 raw43062step1Labels := by
      have ha : raw43062step1 = (fun i j => raw43062step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43062step1 raw43062step0; decide +kernel
      have hl : raw43062step1Labels = raw43062step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43062step0 raw43062step0Labels permutation104 permutation4
    mixedMoment B raw43062step1 raw43062step1Labels = mixedMoment B raw43062step2 raw43062step2Labels := by
      have ha : raw43062step2 = -raw43062step1 := by apply Matrix.ext; change ∀ i j, raw43062step2 i j = -(raw43062step1 i j); unfold raw43062step2 raw43062step1; decide +kernel
      have hl : raw43062step2Labels = raw43062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43062step2 raw43062step2Labels = mixedMoment B raw43062step3 raw43062step3Labels := by
      have ha : raw43062step3 = raw43062step2 := by apply Matrix.ext; unfold raw43062step3 raw43062step2; decide +kernel
      have hl : raw43062step2Labels = labelEmbedding1 ∘ raw43062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43062step2 raw43062step2Labels raw43062step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw43063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw43063Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw43063step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw43063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43063 raw43063Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw43063 raw43063Labels = mixedMoment B raw43063step0 raw43063step0Labels := by
      have hz : ∀ j, raw43063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43063step0 = (fun i j => raw43063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43063step0 raw43063; decide +kernel
      have hl : raw43063step0Labels = raw43063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43063 raw43063Labels permutation434 hz
    mixedMoment B raw43063step0 raw43063step0Labels = mixedMoment B raw43063step1 raw43063step1Labels := by
      have ha : raw43063step1 = (fun i j => raw43063step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43063step1 raw43063step0; decide +kernel
      have hl : raw43063step1Labels = raw43063step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43063step0 raw43063step0Labels permutation122 permutation6
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw43064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw43064Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw43064step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw43064step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43064step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43064step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43064step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw43064step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43064 raw43064Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw43064 raw43064Labels = mixedMoment B raw43064step0 raw43064step0Labels := by
      have hz : ∀ j, raw43064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43064step0 = (fun i j => raw43064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43064step0 raw43064; decide +kernel
      have hl : raw43064step0Labels = raw43064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43064 raw43064Labels permutation434 hz
    mixedMoment B raw43064step0 raw43064step0Labels = mixedMoment B raw43064step1 raw43064step1Labels := by
      have ha : raw43064step1 = (fun i j => raw43064step0 (permutation128 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43064step1 raw43064step0; decide +kernel
      have hl : raw43064step1Labels = raw43064step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43064step0 raw43064step0Labels permutation128 permutation4
    mixedMoment B raw43064step1 raw43064step1Labels = mixedMoment B raw43064step2 raw43064step2Labels := by
      have ha : raw43064step2 = -raw43064step1 := by apply Matrix.ext; change ∀ i j, raw43064step2 i j = -(raw43064step1 i j); unfold raw43064step2 raw43064step1; decide +kernel
      have hl : raw43064step2Labels = raw43064step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43064step2 raw43064step2Labels = mixedMoment B raw43064step3 raw43064step3Labels := by
      have ha : raw43064step3 = raw43064step2 := by apply Matrix.ext; unfold raw43064step3 raw43064step2; decide +kernel
      have hl : raw43064step2Labels = labelEmbedding1 ∘ raw43064step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43064step2 raw43064step2Labels raw43064step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

def raw43065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw43065Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw43065step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw43065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43065 raw43065Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw43065 raw43065Labels = mixedMoment B raw43065step0 raw43065step0Labels := by
      have hz : ∀ j, raw43065 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43065step0 = (fun i j => raw43065 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43065step0 raw43065; decide +kernel
      have hl : raw43065step0Labels = raw43065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43065 raw43065Labels permutation434 hz
    mixedMoment B raw43065step0 raw43065step0Labels = mixedMoment B raw43065step1 raw43065step1Labels := by
      have ha : raw43065step1 = (fun i j => raw43065step0 (permutation129 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43065step1 raw43065step0; decide +kernel
      have hl : raw43065step1Labels = raw43065step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43065step0 raw43065step0Labels permutation129 permutation6
    _ = mixedMoment B node4173 node4173Labels := by rfl

def raw43066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw43066Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw43066step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43066step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw43066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43066 raw43066Labels = mixedMoment B node1504 node1504Labels := by
  calc
    mixedMoment B raw43066 raw43066Labels = mixedMoment B raw43066step0 raw43066step0Labels := by
      have ha : raw43066step0 = (fun i j => raw43066 (permutation594 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43066step0 raw43066; decide +kernel
      have hl : raw43066step0Labels = raw43066Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43066 raw43066Labels permutation594 permutation4
    mixedMoment B raw43066step0 raw43066step0Labels = mixedMoment B raw43066step1 raw43066step1Labels := by
      have ha : raw43066step1 = -raw43066step0 := by apply Matrix.ext; change ∀ i j, raw43066step1 i j = -(raw43066step0 i j); unfold raw43066step1 raw43066step0; decide +kernel
      have hl : raw43066step1Labels = raw43066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43066step1 raw43066step1Labels = mixedMoment B raw43066step2 raw43066step2Labels := by
      have ha : raw43066step2 = raw43066step1 := by apply Matrix.ext; unfold raw43066step2 raw43066step1; decide +kernel
      have hl : raw43066step1Labels = labelEmbedding1 ∘ raw43066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43066step1 raw43066step1Labels raw43066step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1504 node1504Labels := by rfl

def raw43067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw43067Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw43067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43067 raw43067Labels = mixedMoment B node4150 node4150Labels := by
  calc
    mixedMoment B raw43067 raw43067Labels = mixedMoment B raw43067step0 raw43067step0Labels := by
      have ha : raw43067step0 = (fun i j => raw43067 (permutation666 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43067step0 raw43067; decide +kernel
      have hl : raw43067step0Labels = raw43067Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43067 raw43067Labels permutation666 permutation6
    _ = mixedMoment B node4150 node4150Labels := by rfl

def raw43068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw43068Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw43068step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43068step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43068step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43068 raw43068Labels = mixedMoment B node2140 node2140Labels := by
  calc
    mixedMoment B raw43068 raw43068Labels = mixedMoment B raw43068step0 raw43068step0Labels := by
      have ha : raw43068step0 = (fun i j => raw43068 (permutation506 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43068step0 raw43068; decide +kernel
      have hl : raw43068step0Labels = raw43068Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43068 raw43068Labels permutation506 permutation4
    mixedMoment B raw43068step0 raw43068step0Labels = mixedMoment B raw43068step1 raw43068step1Labels := by
      have ha : raw43068step1 = -raw43068step0 := by apply Matrix.ext; change ∀ i j, raw43068step1 i j = -(raw43068step0 i j); unfold raw43068step1 raw43068step0; decide +kernel
      have hl : raw43068step1Labels = raw43068step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43068step1 raw43068step1Labels = mixedMoment B raw43068step2 raw43068step2Labels := by
      have ha : raw43068step2 = raw43068step1 := by apply Matrix.ext; unfold raw43068step2 raw43068step1; decide +kernel
      have hl : raw43068step1Labels = labelEmbedding1 ∘ raw43068step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43068step1 raw43068step1Labels raw43068step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2140 node2140Labels := by rfl

def raw43069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw43069Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw43069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43069 raw43069Labels = mixedMoment B node4663 node4663Labels := by
  calc
    mixedMoment B raw43069 raw43069Labels = mixedMoment B raw43069step0 raw43069step0Labels := by
      have ha : raw43069step0 = (fun i j => raw43069 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43069step0 raw43069; decide +kernel
      have hl : raw43069step0Labels = raw43069Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43069 raw43069Labels permutation514 permutation6
    _ = mixedMoment B node4663 node4663Labels := by rfl

def raw43070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw43070Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw43070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw43070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw43070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43070 raw43070Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw43070 raw43070Labels = mixedMoment B raw43070step0 raw43070step0Labels := by
      have ha : raw43070step0 = (fun i j => raw43070 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43070step0 raw43070; decide +kernel
      have hl : raw43070step0Labels = raw43070Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43070 raw43070Labels permutation683 permutation2
    mixedMoment B raw43070step0 raw43070step0Labels = mixedMoment B raw43070step1 raw43070step1Labels := by
      have ha : raw43070step1 = -raw43070step0 := by apply Matrix.ext; change ∀ i j, raw43070step1 i j = -(raw43070step0 i j); unfold raw43070step1 raw43070step0; decide +kernel
      have hl : raw43070step1Labels = raw43070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43070step1 raw43070step1Labels = mixedMoment B raw43070step2 raw43070step2Labels := by
      have ha : raw43070step2 = raw43070step1 := by apply Matrix.ext; unfold raw43070step2 raw43070step1; decide +kernel
      have hl : raw43070step1Labels = labelEmbedding1 ∘ raw43070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43070step1 raw43070step1Labels raw43070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

def raw43071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw43071Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw43071step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw43071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw43071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43071 raw43071Labels = mixedMoment B node4956 node4956Labels := by
  calc
    mixedMoment B raw43071 raw43071Labels = mixedMoment B raw43071step0 raw43071step0Labels := by
      have ha : raw43071step0 = (fun i j => raw43071 (permutation659 i) (permutation7 j)) := by apply Matrix.ext; unfold raw43071step0 raw43071; decide +kernel
      have hl : raw43071step0Labels = raw43071Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43071 raw43071Labels permutation659 permutation7
    mixedMoment B raw43071step0 raw43071step0Labels = mixedMoment B raw43071step1 raw43071step1Labels := by
      have ha : raw43071step1 = raw43071step0 := by apply Matrix.ext; unfold raw43071step1 raw43071step0; decide +kernel
      have hl : raw43071step0Labels = labelEmbedding6 ∘ raw43071step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43071step0 raw43071step0Labels raw43071step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4956 node4956Labels := by rfl

def raw43072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw43072Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw43072step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43072step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43072 raw43072Labels = mixedMoment B node3255 node3255Labels := by
  calc
    mixedMoment B raw43072 raw43072Labels = mixedMoment B raw43072step0 raw43072step0Labels := by
      have ha : raw43072step0 = (fun i j => raw43072 (permutation648 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43072step0 raw43072; decide +kernel
      have hl : raw43072step0Labels = raw43072Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43072 raw43072Labels permutation648 permutation4
    mixedMoment B raw43072step0 raw43072step0Labels = mixedMoment B raw43072step1 raw43072step1Labels := by
      have ha : raw43072step1 = -raw43072step0 := by apply Matrix.ext; change ∀ i j, raw43072step1 i j = -(raw43072step0 i j); unfold raw43072step1 raw43072step0; decide +kernel
      have hl : raw43072step1Labels = raw43072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43072step1 raw43072step1Labels = mixedMoment B raw43072step2 raw43072step2Labels := by
      have ha : raw43072step2 = raw43072step1 := by apply Matrix.ext; unfold raw43072step2 raw43072step1; decide +kernel
      have hl : raw43072step1Labels = labelEmbedding1 ∘ raw43072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43072step1 raw43072step1Labels raw43072step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3255 node3255Labels := by rfl

def raw43073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw43073Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw43073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43073 raw43073Labels = mixedMoment B node4527 node4527Labels := by
  calc
    mixedMoment B raw43073 raw43073Labels = mixedMoment B raw43073step0 raw43073step0Labels := by
      have ha : raw43073step0 = (fun i j => raw43073 (permutation659 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43073step0 raw43073; decide +kernel
      have hl : raw43073step0Labels = raw43073Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43073 raw43073Labels permutation659 permutation6
    _ = mixedMoment B node4527 node4527Labels := by rfl

def raw43074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw43074Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw43074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw43074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43074step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43074step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw43074step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43074 raw43074Labels = mixedMoment B node1505 node1505Labels := by
  calc
    mixedMoment B raw43074 raw43074Labels = mixedMoment B raw43074step0 raw43074step0Labels := by
      have hz : ∀ j, raw43074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43074step0 = (fun i j => raw43074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43074step0 raw43074; decide +kernel
      have hl : raw43074step0Labels = raw43074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43074 raw43074Labels permutation434 hz
    mixedMoment B raw43074step0 raw43074step0Labels = mixedMoment B raw43074step1 raw43074step1Labels := by
      have ha : raw43074step1 = (fun i j => raw43074step0 (permutation129 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43074step1 raw43074step0; decide +kernel
      have hl : raw43074step1Labels = raw43074step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43074step0 raw43074step0Labels permutation129 permutation4
    mixedMoment B raw43074step1 raw43074step1Labels = mixedMoment B raw43074step2 raw43074step2Labels := by
      have ha : raw43074step2 = -raw43074step1 := by apply Matrix.ext; change ∀ i j, raw43074step2 i j = -(raw43074step1 i j); unfold raw43074step2 raw43074step1; decide +kernel
      have hl : raw43074step2Labels = raw43074step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43074step2 raw43074step2Labels = mixedMoment B raw43074step3 raw43074step3Labels := by
      have ha : raw43074step3 = raw43074step2 := by apply Matrix.ext; unfold raw43074step3 raw43074step2; decide +kernel
      have hl : raw43074step2Labels = labelEmbedding1 ∘ raw43074step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43074step2 raw43074step2Labels raw43074step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1505 node1505Labels := by rfl

def raw43075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw43075Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw43075step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw43075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43075 raw43075Labels = mixedMoment B node4151 node4151Labels := by
  calc
    mixedMoment B raw43075 raw43075Labels = mixedMoment B raw43075step0 raw43075step0Labels := by
      have hz : ∀ j, raw43075 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43075step0 = (fun i j => raw43075 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43075step0 raw43075; decide +kernel
      have hl : raw43075step0Labels = raw43075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43075 raw43075Labels permutation434 hz
    mixedMoment B raw43075step0 raw43075step0Labels = mixedMoment B raw43075step1 raw43075step1Labels := by
      have ha : raw43075step1 = (fun i j => raw43075step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43075step1 raw43075step0; decide +kernel
      have hl : raw43075step1Labels = raw43075step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43075step0 raw43075step0Labels permutation146 permutation6
    _ = mixedMoment B node4151 node4151Labels := by rfl

def raw43076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw43076Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw43076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43076 raw43076Labels = mixedMoment B node2148 node2148Labels := by
  calc
    mixedMoment B raw43076 raw43076Labels = mixedMoment B raw43076step0 raw43076step0Labels := by
      have ha : raw43076step0 = (fun i j => raw43076 (permutation507 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43076step0 raw43076; decide +kernel
      have hl : raw43076step0Labels = raw43076Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43076 raw43076Labels permutation507 permutation4
    mixedMoment B raw43076step0 raw43076step0Labels = mixedMoment B raw43076step1 raw43076step1Labels := by
      have ha : raw43076step1 = -raw43076step0 := by apply Matrix.ext; change ∀ i j, raw43076step1 i j = -(raw43076step0 i j); unfold raw43076step1 raw43076step0; decide +kernel
      have hl : raw43076step1Labels = raw43076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43076step1 raw43076step1Labels = mixedMoment B raw43076step2 raw43076step2Labels := by
      have ha : raw43076step2 = raw43076step1 := by apply Matrix.ext; unfold raw43076step2 raw43076step1; decide +kernel
      have hl : raw43076step1Labels = labelEmbedding1 ∘ raw43076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43076step1 raw43076step1Labels raw43076step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2148 node2148Labels := by rfl

def raw43077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw43077Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw43077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43077 raw43077Labels = mixedMoment B node4666 node4666Labels := by
  calc
    mixedMoment B raw43077 raw43077Labels = mixedMoment B raw43077step0 raw43077step0Labels := by
      have ha : raw43077step0 = (fun i j => raw43077 (permutation514 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43077step0 raw43077; decide +kernel
      have hl : raw43077step0Labels = raw43077Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43077 raw43077Labels permutation514 permutation6
    _ = mixedMoment B node4666 node4666Labels := by rfl

def raw43078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw43078Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw43078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw43078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw43078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43078 raw43078Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw43078 raw43078Labels = mixedMoment B raw43078step0 raw43078step0Labels := by
      have ha : raw43078step0 = (fun i j => raw43078 (permutation683 i) (permutation2 j)) := by apply Matrix.ext; unfold raw43078step0 raw43078; decide +kernel
      have hl : raw43078step0Labels = raw43078Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43078 raw43078Labels permutation683 permutation2
    mixedMoment B raw43078step0 raw43078step0Labels = mixedMoment B raw43078step1 raw43078step1Labels := by
      have ha : raw43078step1 = -raw43078step0 := by apply Matrix.ext; change ∀ i j, raw43078step1 i j = -(raw43078step0 i j); unfold raw43078step1 raw43078step0; decide +kernel
      have hl : raw43078step1Labels = raw43078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43078step1 raw43078step1Labels = mixedMoment B raw43078step2 raw43078step2Labels := by
      have ha : raw43078step2 = raw43078step1 := by apply Matrix.ext; unfold raw43078step2 raw43078step1; decide +kernel
      have hl : raw43078step1Labels = labelEmbedding1 ∘ raw43078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43078step1 raw43078step1Labels raw43078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

def raw43079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw43079Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw43079step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw43079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw43079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43079 raw43079Labels = mixedMoment B node4958 node4958Labels := by
  calc
    mixedMoment B raw43079 raw43079Labels = mixedMoment B raw43079step0 raw43079step0Labels := by
      have ha : raw43079step0 = (fun i j => raw43079 (permutation659 i) (permutation7 j)) := by apply Matrix.ext; unfold raw43079step0 raw43079; decide +kernel
      have hl : raw43079step0Labels = raw43079Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43079 raw43079Labels permutation659 permutation7
    mixedMoment B raw43079step0 raw43079step0Labels = mixedMoment B raw43079step1 raw43079step1Labels := by
      have ha : raw43079step1 = raw43079step0 := by apply Matrix.ext; unfold raw43079step1 raw43079step0; decide +kernel
      have hl : raw43079step0Labels = labelEmbedding6 ∘ raw43079step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43079step0 raw43079step0Labels raw43079step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4958 node4958Labels := by rfl

def raw43080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw43080Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw43080step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43080 raw43080Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw43080 raw43080Labels = mixedMoment B raw43080step0 raw43080step0Labels := by
      have ha : raw43080step0 = (fun i j => raw43080 (permutation650 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43080step0 raw43080; decide +kernel
      have hl : raw43080step0Labels = raw43080Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43080 raw43080Labels permutation650 permutation4
    mixedMoment B raw43080step0 raw43080step0Labels = mixedMoment B raw43080step1 raw43080step1Labels := by
      have ha : raw43080step1 = -raw43080step0 := by apply Matrix.ext; change ∀ i j, raw43080step1 i j = -(raw43080step0 i j); unfold raw43080step1 raw43080step0; decide +kernel
      have hl : raw43080step1Labels = raw43080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43080step1 raw43080step1Labels = mixedMoment B raw43080step2 raw43080step2Labels := by
      have ha : raw43080step2 = raw43080step1 := by apply Matrix.ext; unfold raw43080step2 raw43080step1; decide +kernel
      have hl : raw43080step1Labels = labelEmbedding1 ∘ raw43080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43080step1 raw43080step1Labels raw43080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

def raw43081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw43081Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw43081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43081 raw43081Labels = mixedMoment B node4530 node4530Labels := by
  calc
    mixedMoment B raw43081 raw43081Labels = mixedMoment B raw43081step0 raw43081step0Labels := by
      have ha : raw43081step0 = (fun i j => raw43081 (permutation659 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43081step0 raw43081; decide +kernel
      have hl : raw43081step0Labels = raw43081Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43081 raw43081Labels permutation659 permutation6
    _ = mixedMoment B node4530 node4530Labels := by rfl

def raw43082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw43082Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw43082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw43082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43082step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw43082step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw43082step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical43082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43082 raw43082Labels = mixedMoment B node1515 node1515Labels := by
  calc
    mixedMoment B raw43082 raw43082Labels = mixedMoment B raw43082step0 raw43082step0Labels := by
      have hz : ∀ j, raw43082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43082step0 = (fun i j => raw43082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43082step0 raw43082; decide +kernel
      have hl : raw43082step0Labels = raw43082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43082 raw43082Labels permutation434 hz
    mixedMoment B raw43082step0 raw43082step0Labels = mixedMoment B raw43082step1 raw43082step1Labels := by
      have ha : raw43082step1 = (fun i j => raw43082step0 (permutation132 i) (permutation4 j)) := by apply Matrix.ext; unfold raw43082step1 raw43082step0; decide +kernel
      have hl : raw43082step1Labels = raw43082step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43082step0 raw43082step0Labels permutation132 permutation4
    mixedMoment B raw43082step1 raw43082step1Labels = mixedMoment B raw43082step2 raw43082step2Labels := by
      have ha : raw43082step2 = -raw43082step1 := by apply Matrix.ext; change ∀ i j, raw43082step2 i j = -(raw43082step1 i j); unfold raw43082step2 raw43082step1; decide +kernel
      have hl : raw43082step2Labels = raw43082step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw43082step2 raw43082step2Labels = mixedMoment B raw43082step3 raw43082step3Labels := by
      have ha : raw43082step3 = raw43082step2 := by apply Matrix.ext; unfold raw43082step3 raw43082step2; decide +kernel
      have hl : raw43082step2Labels = labelEmbedding1 ∘ raw43082step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw43082step2 raw43082step2Labels raw43082step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1515 node1515Labels := by rfl

def raw43083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw43083Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 3, -5]]
def raw43083step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw43083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw43083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical43083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw43083 raw43083Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw43083 raw43083Labels = mixedMoment B raw43083step0 raw43083step0Labels := by
      have hz : ∀ j, raw43083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw43083step0 = (fun i j => raw43083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw43083step0 raw43083; decide +kernel
      have hl : raw43083step0Labels = raw43083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw43083 raw43083Labels permutation434 hz
    mixedMoment B raw43083step0 raw43083step0Labels = mixedMoment B raw43083step1 raw43083step1Labels := by
      have ha : raw43083step1 = (fun i j => raw43083step0 (permutation146 i) (permutation6 j)) := by apply Matrix.ext; unfold raw43083step1 raw43083step0; decide +kernel
      have hl : raw43083step1Labels = raw43083step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw43083step0 raw43083step0Labels permutation146 permutation6
    _ = mixedMoment B node4155 node4155Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
