import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
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

def raw2560 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2560step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2560 raw2560Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw2560 raw2560Labels = mixedMoment B raw2560step0 raw2560step0Labels := by
      have ha : raw2560step0 = (fun i j => raw2560 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2560step0 raw2560; decide +kernel
      have hl : raw2560step0Labels = raw2560Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2560 raw2560Labels permutation8 permutation4
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw2561 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2561Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2561step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2561step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2561 raw2561Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw2561 raw2561Labels = mixedMoment B raw2561step0 raw2561step0Labels := by
      have ha : raw2561step0 = (fun i j => raw2561 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2561step0 raw2561; decide +kernel
      have hl : raw2561step0Labels = raw2561Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2561 raw2561Labels permutation10 permutation6
    mixedMoment B raw2561step0 raw2561step0Labels = mixedMoment B raw2561step1 raw2561step1Labels := by
      have ha : raw2561step1 = -raw2561step0 := by apply Matrix.ext; change ∀ i j, raw2561step1 i j = -(raw2561step0 i j); unfold raw2561step1 raw2561step0; decide +kernel
      have hl : raw2561step1Labels = raw2561step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2561step1 raw2561step1Labels = mixedMoment B raw2561step2 raw2561step2Labels := by
      have ha : raw2561step2 = raw2561step1 := by apply Matrix.ext; unfold raw2561step2 raw2561step1; decide +kernel
      have hl : raw2561step1Labels = labelEmbedding1 ∘ raw2561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2561step1 raw2561step1Labels raw2561step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw2562 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2562 raw2562Labels = mixedMoment B node5452 node5452Labels := by
  calc
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw2563 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2563 raw2563Labels = mixedMoment B node3911 node3911Labels := by
  calc
    _ = mixedMoment B node3911 node3911Labels := by rfl

def raw2564 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2564Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2564step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2564 raw2564Labels = mixedMoment B node4039 node4039Labels := by
  calc
    mixedMoment B raw2564 raw2564Labels = mixedMoment B raw2564step0 raw2564step0Labels := by
      have ha : raw2564step0 = (fun i j => raw2564 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2564step0 raw2564; decide +kernel
      have hl : raw2564step0Labels = raw2564Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2564 raw2564Labels permutation32 permutation3
    mixedMoment B raw2564step0 raw2564step0Labels = mixedMoment B raw2564step1 raw2564step1Labels := by
      have ha : raw2564step1 = raw2564step0 := by apply Matrix.ext; unfold raw2564step1 raw2564step0; decide +kernel
      have hl : raw2564step0Labels = labelEmbedding1 ∘ raw2564step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2564step0 raw2564step0Labels raw2564step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4039 node4039Labels := by rfl

def raw2565 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2565 raw2565Labels = mixedMoment B node5453 node5453Labels := by
  calc
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2566 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2566 raw2566Labels = mixedMoment B node3912 node3912Labels := by
  calc
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw2567 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2567Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2567step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2567step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2567step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2567step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2567step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2567step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2567 raw2567Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw2567 raw2567Labels = mixedMoment B raw2567step0 raw2567step0Labels := by
      have ha : raw2567step0 = (fun i j => raw2567 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2567step0 raw2567; decide +kernel
      have hl : raw2567step0Labels = raw2567Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2567 raw2567Labels permutation29 permutation3
    mixedMoment B raw2567step0 raw2567step0Labels = mixedMoment B raw2567step1 raw2567step1Labels := by
      have ha : raw2567step1 = -raw2567step0 := by apply Matrix.ext; change ∀ i j, raw2567step1 i j = -(raw2567step0 i j); unfold raw2567step1 raw2567step0; decide +kernel
      have hl : raw2567step1Labels = raw2567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2567step1 raw2567step1Labels = mixedMoment B raw2567step2 raw2567step2Labels := by
      have ha : raw2567step2 = raw2567step1 := by apply Matrix.ext; unfold raw2567step2 raw2567step1; decide +kernel
      have hl : raw2567step1Labels = labelEmbedding1 ∘ raw2567step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2567step1 raw2567step1Labels raw2567step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw2568 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2568 raw2568Labels = mixedMoment B node5456 node5456Labels := by
  calc
    _ = mixedMoment B node5456 node5456Labels := by rfl

def raw2569 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2569 raw2569Labels = mixedMoment B node3916 node3916Labels := by
  calc
    _ = mixedMoment B node3916 node3916Labels := by rfl

def raw2570 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2570Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2570step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -2, 2], ![-2, 2, 0]]
def raw2570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2570step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2570step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2570step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw2570step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2570 raw2570Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw2570 raw2570Labels = mixedMoment B raw2570step0 raw2570step0Labels := by
      have ha : raw2570step0 = (fun i j => raw2570 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2570step0 raw2570; decide +kernel
      have hl : raw2570step0Labels = raw2570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2570 raw2570Labels permutation7 permutation3
    mixedMoment B raw2570step0 raw2570step0Labels = mixedMoment B raw2570step1 raw2570step1Labels := by
      have ha : raw2570step1 = -raw2570step0 := by apply Matrix.ext; change ∀ i j, raw2570step1 i j = -(raw2570step0 i j); unfold raw2570step1 raw2570step0; decide +kernel
      have hl : raw2570step1Labels = raw2570step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2570step1 raw2570step1Labels = mixedMoment B raw2570step2 raw2570step2Labels := by
      have ha : raw2570step2 = raw2570step1 := by apply Matrix.ext; unfold raw2570step2 raw2570step1; decide +kernel
      have hl : raw2570step1Labels = labelEmbedding1 ∘ raw2570step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2570step1 raw2570step1Labels raw2570step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3916 node3916Labels := by rfl

def raw2571 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2571Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2571step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2571step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2571 raw2571Labels = mixedMoment B node5464 node5464Labels := by
  calc
    mixedMoment B raw2571 raw2571Labels = mixedMoment B raw2571step0 raw2571step0Labels := by
      have ha : raw2571step0 = (fun i j => raw2571 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2571step0 raw2571; decide +kernel
      have hl : raw2571step0Labels = raw2571Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2571 raw2571Labels permutation152 permutation4
    mixedMoment B raw2571step0 raw2571step0Labels = mixedMoment B raw2571step1 raw2571step1Labels := by
      have ha : raw2571step1 = raw2571step0 := by apply Matrix.ext; unfold raw2571step1 raw2571step0; decide +kernel
      have hl : raw2571step0Labels = labelEmbedding7 ∘ raw2571step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2571step0 raw2571step0Labels raw2571step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5464 node5464Labels := by rfl

def raw2572 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2572 raw2572Labels = mixedMoment B node3930 node3930Labels := by
  calc
    mixedMoment B raw2572 raw2572Labels = mixedMoment B raw2572step0 raw2572step0Labels := by
      have ha : raw2572step0 = (fun i j => raw2572 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2572step0 raw2572; decide +kernel
      have hl : raw2572step0Labels = raw2572Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2572 raw2572Labels permutation152 permutation4
    _ = mixedMoment B node3930 node3930Labels := by rfl

def raw2573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2573Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2573step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2573step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2573step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2573step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2573 raw2573Labels = mixedMoment B node4041 node4041Labels := by
  calc
    mixedMoment B raw2573 raw2573Labels = mixedMoment B raw2573step0 raw2573step0Labels := by
      have ha : raw2573step0 = (fun i j => raw2573 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2573step0 raw2573; decide +kernel
      have hl : raw2573step0Labels = raw2573Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2573 raw2573Labels permutation168 permutation3
    mixedMoment B raw2573step0 raw2573step0Labels = mixedMoment B raw2573step1 raw2573step1Labels := by
      have ha : raw2573step1 = -raw2573step0 := by apply Matrix.ext; change ∀ i j, raw2573step1 i j = -(raw2573step0 i j); unfold raw2573step1 raw2573step0; decide +kernel
      have hl : raw2573step1Labels = raw2573step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2573step1 raw2573step1Labels = mixedMoment B raw2573step2 raw2573step2Labels := by
      have ha : raw2573step2 = raw2573step1 := by apply Matrix.ext; unfold raw2573step2 raw2573step1; decide +kernel
      have hl : raw2573step1Labels = labelEmbedding1 ∘ raw2573step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2573step1 raw2573step1Labels raw2573step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4041 node4041Labels := by rfl

def raw2574 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2574Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2574step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2574step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2574 raw2574Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw2574 raw2574Labels = mixedMoment B raw2574step0 raw2574step0Labels := by
      have ha : raw2574step0 = (fun i j => raw2574 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2574step0 raw2574; decide +kernel
      have hl : raw2574step0Labels = raw2574Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2574 raw2574Labels permutation32 permutation4
    mixedMoment B raw2574step0 raw2574step0Labels = mixedMoment B raw2574step1 raw2574step1Labels := by
      have ha : raw2574step1 = raw2574step0 := by apply Matrix.ext; unfold raw2574step1 raw2574step0; decide +kernel
      have hl : raw2574step0Labels = labelEmbedding7 ∘ raw2574step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2574step0 raw2574step0Labels raw2574step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw2575 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2575 raw2575Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw2575 raw2575Labels = mixedMoment B raw2575step0 raw2575step0Labels := by
      have ha : raw2575step0 = (fun i j => raw2575 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2575step0 raw2575; decide +kernel
      have hl : raw2575step0Labels = raw2575Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2575 raw2575Labels permutation32 permutation4
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw2576 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2576Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2576step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2576step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2576 raw2576Labels = mixedMoment B node4042 node4042Labels := by
  calc
    mixedMoment B raw2576 raw2576Labels = mixedMoment B raw2576step0 raw2576step0Labels := by
      have ha : raw2576step0 = (fun i j => raw2576 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2576step0 raw2576; decide +kernel
      have hl : raw2576step0Labels = raw2576Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2576 raw2576Labels permutation34 permutation3
    mixedMoment B raw2576step0 raw2576step0Labels = mixedMoment B raw2576step1 raw2576step1Labels := by
      have ha : raw2576step1 = -raw2576step0 := by apply Matrix.ext; change ∀ i j, raw2576step1 i j = -(raw2576step0 i j); unfold raw2576step1 raw2576step0; decide +kernel
      have hl : raw2576step1Labels = raw2576step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2576step1 raw2576step1Labels = mixedMoment B raw2576step2 raw2576step2Labels := by
      have ha : raw2576step2 = raw2576step1 := by apply Matrix.ext; unfold raw2576step2 raw2576step1; decide +kernel
      have hl : raw2576step1Labels = labelEmbedding1 ∘ raw2576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2576step1 raw2576step1Labels raw2576step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4042 node4042Labels := by rfl

def raw2577 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2577Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2577step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw2577step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2577step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw2577step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2577 raw2577Labels = mixedMoment B node5466 node5466Labels := by
  calc
    mixedMoment B raw2577 raw2577Labels = mixedMoment B raw2577step0 raw2577step0Labels := by
      have ha : raw2577step0 = (fun i j => raw2577 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2577step0 raw2577; decide +kernel
      have hl : raw2577step0Labels = raw2577Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2577 raw2577Labels permutation8 permutation4
    mixedMoment B raw2577step0 raw2577step0Labels = mixedMoment B raw2577step1 raw2577step1Labels := by
      have ha : raw2577step1 = raw2577step0 := by apply Matrix.ext; unfold raw2577step1 raw2577step0; decide +kernel
      have hl : raw2577step0Labels = labelEmbedding7 ∘ raw2577step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2577step0 raw2577step0Labels raw2577step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5466 node5466Labels := by rfl

def raw2578 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2578Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2578step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw2578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2578 raw2578Labels = mixedMoment B node3934 node3934Labels := by
  calc
    mixedMoment B raw2578 raw2578Labels = mixedMoment B raw2578step0 raw2578step0Labels := by
      have ha : raw2578step0 = (fun i j => raw2578 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2578step0 raw2578; decide +kernel
      have hl : raw2578step0Labels = raw2578Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2578 raw2578Labels permutation8 permutation4
    _ = mixedMoment B node3934 node3934Labels := by rfl

def raw2579 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2579Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2579step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]
def raw2579step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2579step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2]]
def raw2579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2579 raw2579Labels = mixedMoment B node4043 node4043Labels := by
  calc
    mixedMoment B raw2579 raw2579Labels = mixedMoment B raw2579step0 raw2579step0Labels := by
      have ha : raw2579step0 = (fun i j => raw2579 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2579step0 raw2579; decide +kernel
      have hl : raw2579step0Labels = raw2579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2579 raw2579Labels permutation24 permutation3
    mixedMoment B raw2579step0 raw2579step0Labels = mixedMoment B raw2579step1 raw2579step1Labels := by
      have ha : raw2579step1 = raw2579step0 := by apply Matrix.ext; unfold raw2579step1 raw2579step0; decide +kernel
      have hl : raw2579step0Labels = labelEmbedding1 ∘ raw2579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2579step0 raw2579step0Labels raw2579step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4043 node4043Labels := by rfl

def raw2580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2580step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2580 raw2580Labels = mixedMoment B node5467 node5467Labels := by
  calc
    mixedMoment B raw2580 raw2580Labels = mixedMoment B raw2580step0 raw2580step0Labels := by
      have ha : raw2580step0 = (fun i j => raw2580 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2580step0 raw2580; decide +kernel
      have hl : raw2580step0Labels = raw2580Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2580 raw2580Labels permutation152 permutation4
    mixedMoment B raw2580step0 raw2580step0Labels = mixedMoment B raw2580step1 raw2580step1Labels := by
      have ha : raw2580step1 = raw2580step0 := by apply Matrix.ext; unfold raw2580step1 raw2580step0; decide +kernel
      have hl : raw2580step0Labels = labelEmbedding7 ∘ raw2580step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2580step0 raw2580step0Labels raw2580step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5467 node5467Labels := by rfl

def raw2581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2581Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2581 raw2581Labels = mixedMoment B node3942 node3942Labels := by
  calc
    mixedMoment B raw2581 raw2581Labels = mixedMoment B raw2581step0 raw2581step0Labels := by
      have ha : raw2581step0 = (fun i j => raw2581 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2581step0 raw2581; decide +kernel
      have hl : raw2581step0Labels = raw2581Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2581 raw2581Labels permutation152 permutation4
    _ = mixedMoment B node3942 node3942Labels := by rfl

def raw2582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw2582Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2582step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2582 raw2582Labels = mixedMoment B node3942 node3942Labels := by
  calc
    mixedMoment B raw2582 raw2582Labels = mixedMoment B raw2582step0 raw2582step0Labels := by
      have ha : raw2582step0 = (fun i j => raw2582 (permutation588 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2582step0 raw2582; decide +kernel
      have hl : raw2582step0Labels = raw2582Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2582 raw2582Labels permutation588 permutation6
    mixedMoment B raw2582step0 raw2582step0Labels = mixedMoment B raw2582step1 raw2582step1Labels := by
      have ha : raw2582step1 = raw2582step0 := by apply Matrix.ext; unfold raw2582step1 raw2582step0; decide +kernel
      have hl : raw2582step0Labels = labelEmbedding1 ∘ raw2582step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2582step0 raw2582step0Labels raw2582step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3942 node3942Labels := by rfl

def raw2583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2583step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2583 raw2583Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw2583 raw2583Labels = mixedMoment B raw2583step0 raw2583step0Labels := by
      have ha : raw2583step0 = (fun i j => raw2583 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2583step0 raw2583; decide +kernel
      have hl : raw2583step0Labels = raw2583Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2583 raw2583Labels permutation152 permutation4
    mixedMoment B raw2583step0 raw2583step0Labels = mixedMoment B raw2583step1 raw2583step1Labels := by
      have ha : raw2583step1 = raw2583step0 := by apply Matrix.ext; unfold raw2583step1 raw2583step0; decide +kernel
      have hl : raw2583step0Labels = labelEmbedding7 ∘ raw2583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2583step0 raw2583step0Labels raw2583step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw2584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2584Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2584 raw2584Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw2584 raw2584Labels = mixedMoment B raw2584step0 raw2584step0Labels := by
      have ha : raw2584step0 = (fun i j => raw2584 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2584step0 raw2584; decide +kernel
      have hl : raw2584step0Labels = raw2584Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2584 raw2584Labels permutation152 permutation4
    _ = mixedMoment B node3945 node3945Labels := by rfl

def raw2585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2585Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2585step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2585step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2585step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2585step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2585 raw2585Labels = mixedMoment B node3952 node3952Labels := by
  calc
    mixedMoment B raw2585 raw2585Labels = mixedMoment B raw2585step0 raw2585step0Labels := by
      have ha : raw2585step0 = (fun i j => raw2585 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2585step0 raw2585; decide +kernel
      have hl : raw2585step0Labels = raw2585Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2585 raw2585Labels permutation265 permutation6
    mixedMoment B raw2585step0 raw2585step0Labels = mixedMoment B raw2585step1 raw2585step1Labels := by
      have ha : raw2585step1 = -raw2585step0 := by apply Matrix.ext; change ∀ i j, raw2585step1 i j = -(raw2585step0 i j); unfold raw2585step1 raw2585step0; decide +kernel
      have hl : raw2585step1Labels = raw2585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2585step1 raw2585step1Labels = mixedMoment B raw2585step2 raw2585step2Labels := by
      have ha : raw2585step2 = raw2585step1 := by apply Matrix.ext; unfold raw2585step2 raw2585step1; decide +kernel
      have hl : raw2585step1Labels = labelEmbedding1 ∘ raw2585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2585step1 raw2585step1Labels raw2585step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3952 node3952Labels := by rfl

def raw2586 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2586step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2586 raw2586Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw2586 raw2586Labels = mixedMoment B raw2586step0 raw2586step0Labels := by
      have ha : raw2586step0 = (fun i j => raw2586 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2586step0 raw2586; decide +kernel
      have hl : raw2586step0Labels = raw2586Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2586 raw2586Labels permutation152 permutation4
    mixedMoment B raw2586step0 raw2586step0Labels = mixedMoment B raw2586step1 raw2586step1Labels := by
      have ha : raw2586step1 = raw2586step0 := by apply Matrix.ext; unfold raw2586step1 raw2586step0; decide +kernel
      have hl : raw2586step0Labels = labelEmbedding7 ∘ raw2586step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2586step0 raw2586step0Labels raw2586step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw2587 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2587Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2587 raw2587Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw2587 raw2587Labels = mixedMoment B raw2587step0 raw2587step0Labels := by
      have ha : raw2587step0 = (fun i j => raw2587 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2587step0 raw2587; decide +kernel
      have hl : raw2587step0Labels = raw2587Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2587 raw2587Labels permutation152 permutation4
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw2588 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2588Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2588step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2588step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2588step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2588step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2588 raw2588Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw2588 raw2588Labels = mixedMoment B raw2588step0 raw2588step0Labels := by
      have ha : raw2588step0 = (fun i j => raw2588 (permutation271 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2588step0 raw2588; decide +kernel
      have hl : raw2588step0Labels = raw2588Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2588 raw2588Labels permutation271 permutation6
    mixedMoment B raw2588step0 raw2588step0Labels = mixedMoment B raw2588step1 raw2588step1Labels := by
      have ha : raw2588step1 = -raw2588step0 := by apply Matrix.ext; change ∀ i j, raw2588step1 i j = -(raw2588step0 i j); unfold raw2588step1 raw2588step0; decide +kernel
      have hl : raw2588step1Labels = raw2588step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2588step1 raw2588step1Labels = mixedMoment B raw2588step2 raw2588step2Labels := by
      have ha : raw2588step2 = raw2588step1 := by apply Matrix.ext; unfold raw2588step2 raw2588step1; decide +kernel
      have hl : raw2588step1Labels = labelEmbedding1 ∘ raw2588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2588step1 raw2588step1Labels raw2588step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw2589 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2589step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2589step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2589step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2589 raw2589Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw2589 raw2589Labels = mixedMoment B raw2589step0 raw2589step0Labels := by
      have ha : raw2589step0 = (fun i j => raw2589 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2589step0 raw2589; decide +kernel
      have hl : raw2589step0Labels = raw2589Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2589 raw2589Labels permutation32 permutation4
    mixedMoment B raw2589step0 raw2589step0Labels = mixedMoment B raw2589step1 raw2589step1Labels := by
      have ha : raw2589step1 = raw2589step0 := by apply Matrix.ext; unfold raw2589step1 raw2589step0; decide +kernel
      have hl : raw2589step0Labels = labelEmbedding7 ∘ raw2589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2589step0 raw2589step0Labels raw2589step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw2590 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2590Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2590 raw2590Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw2590 raw2590Labels = mixedMoment B raw2590step0 raw2590step0Labels := by
      have ha : raw2590step0 = (fun i j => raw2590 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2590step0 raw2590; decide +kernel
      have hl : raw2590step0Labels = raw2590Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2590 raw2590Labels permutation32 permutation4
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw2591 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2591Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2591step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2591step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2591step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2591 raw2591Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw2591 raw2591Labels = mixedMoment B raw2591step0 raw2591step0Labels := by
      have ha : raw2591step0 = (fun i j => raw2591 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2591step0 raw2591; decide +kernel
      have hl : raw2591step0Labels = raw2591Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2591 raw2591Labels permutation56 permutation6
    mixedMoment B raw2591step0 raw2591step0Labels = mixedMoment B raw2591step1 raw2591step1Labels := by
      have ha : raw2591step1 = -raw2591step0 := by apply Matrix.ext; change ∀ i j, raw2591step1 i j = -(raw2591step0 i j); unfold raw2591step1 raw2591step0; decide +kernel
      have hl : raw2591step1Labels = raw2591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2591step1 raw2591step1Labels = mixedMoment B raw2591step2 raw2591step2Labels := by
      have ha : raw2591step2 = raw2591step1 := by apply Matrix.ext; unfold raw2591step2 raw2591step1; decide +kernel
      have hl : raw2591step1Labels = labelEmbedding1 ∘ raw2591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2591step1 raw2591step1Labels raw2591step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw2592 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw2592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2592step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2592step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2592step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2592 raw2592Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw2592 raw2592Labels = mixedMoment B raw2592step0 raw2592step0Labels := by
      have ha : raw2592step0 = (fun i j => raw2592 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2592step0 raw2592; decide +kernel
      have hl : raw2592step0Labels = raw2592Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2592 raw2592Labels permutation8 permutation4
    mixedMoment B raw2592step0 raw2592step0Labels = mixedMoment B raw2592step1 raw2592step1Labels := by
      have ha : raw2592step1 = raw2592step0 := by apply Matrix.ext; unfold raw2592step1 raw2592step0; decide +kernel
      have hl : raw2592step0Labels = labelEmbedding7 ∘ raw2592step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2592step0 raw2592step0Labels raw2592step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

def raw2593 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw2593Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2593step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2593 raw2593Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw2593 raw2593Labels = mixedMoment B raw2593step0 raw2593step0Labels := by
      have ha : raw2593step0 = (fun i j => raw2593 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2593step0 raw2593; decide +kernel
      have hl : raw2593step0Labels = raw2593Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2593 raw2593Labels permutation8 permutation4
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw2594 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw2594Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2594step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2594step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2594step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw2594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2594 raw2594Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw2594 raw2594Labels = mixedMoment B raw2594step0 raw2594step0Labels := by
      have ha : raw2594step0 = (fun i j => raw2594 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2594step0 raw2594; decide +kernel
      have hl : raw2594step0Labels = raw2594Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2594 raw2594Labels permutation24 permutation6
    mixedMoment B raw2594step0 raw2594step0Labels = mixedMoment B raw2594step1 raw2594step1Labels := by
      have ha : raw2594step1 = raw2594step0 := by apply Matrix.ext; unfold raw2594step1 raw2594step0; decide +kernel
      have hl : raw2594step0Labels = labelEmbedding1 ∘ raw2594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2594step0 raw2594step0Labels raw2594step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw2595 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2595step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2595 raw2595Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw2595 raw2595Labels = mixedMoment B raw2595step0 raw2595step0Labels := by
      have ha : raw2595step0 = (fun i j => raw2595 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2595step0 raw2595; decide +kernel
      have hl : raw2595step0Labels = raw2595Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2595 raw2595Labels permutation152 permutation4
    mixedMoment B raw2595step0 raw2595step0Labels = mixedMoment B raw2595step1 raw2595step1Labels := by
      have ha : raw2595step1 = raw2595step0 := by apply Matrix.ext; unfold raw2595step1 raw2595step0; decide +kernel
      have hl : raw2595step0Labels = labelEmbedding7 ∘ raw2595step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2595step0 raw2595step0Labels raw2595step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5476 node5476Labels := by rfl

def raw2596 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2596Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2596 raw2596Labels = mixedMoment B node3965 node3965Labels := by
  calc
    mixedMoment B raw2596 raw2596Labels = mixedMoment B raw2596step0 raw2596step0Labels := by
      have ha : raw2596step0 = (fun i j => raw2596 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2596step0 raw2596; decide +kernel
      have hl : raw2596step0Labels = raw2596Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2596 raw2596Labels permutation152 permutation4
    _ = mixedMoment B node3965 node3965Labels := by rfl

def raw2597 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2597Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2597step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2597step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2597 raw2597Labels = mixedMoment B node4045 node4045Labels := by
  calc
    mixedMoment B raw2597 raw2597Labels = mixedMoment B raw2597step0 raw2597step0Labels := by
      have ha : raw2597step0 = (fun i j => raw2597 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2597step0 raw2597; decide +kernel
      have hl : raw2597step0Labels = raw2597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2597 raw2597Labels permutation662 permutation3
    mixedMoment B raw2597step0 raw2597step0Labels = mixedMoment B raw2597step1 raw2597step1Labels := by
      have ha : raw2597step1 = raw2597step0 := by apply Matrix.ext; unfold raw2597step1 raw2597step0; decide +kernel
      have hl : raw2597step0Labels = labelEmbedding1 ∘ raw2597step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2597step0 raw2597step0Labels raw2597step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4045 node4045Labels := by rfl

def raw2598 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2598step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2598 raw2598Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw2598 raw2598Labels = mixedMoment B raw2598step0 raw2598step0Labels := by
      have ha : raw2598step0 = (fun i j => raw2598 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2598step0 raw2598; decide +kernel
      have hl : raw2598step0Labels = raw2598Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2598 raw2598Labels permutation152 permutation4
    mixedMoment B raw2598step0 raw2598step0Labels = mixedMoment B raw2598step1 raw2598step1Labels := by
      have ha : raw2598step1 = raw2598step0 := by apply Matrix.ext; unfold raw2598step1 raw2598step0; decide +kernel
      have hl : raw2598step0Labels = labelEmbedding7 ∘ raw2598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2598step0 raw2598step0Labels raw2598step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw2599 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2599Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2599 raw2599Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2599 raw2599Labels = mixedMoment B raw2599step0 raw2599step0Labels := by
      have ha : raw2599step0 = (fun i j => raw2599 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2599step0 raw2599; decide +kernel
      have hl : raw2599step0Labels = raw2599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2599 raw2599Labels permutation152 permutation4
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw2600 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw2600Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2600 raw2600Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw2600 raw2600Labels = mixedMoment B raw2600step0 raw2600step0Labels := by
      have ha : raw2600step0 = (fun i j => raw2600 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2600step0 raw2600; decide +kernel
      have hl : raw2600step0Labels = raw2600Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2600 raw2600Labels permutation688 permutation6
    mixedMoment B raw2600step0 raw2600step0Labels = mixedMoment B raw2600step1 raw2600step1Labels := by
      have ha : raw2600step1 = raw2600step0 := by apply Matrix.ext; unfold raw2600step1 raw2600step0; decide +kernel
      have hl : raw2600step0Labels = labelEmbedding1 ∘ raw2600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2600step0 raw2600step0Labels raw2600step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw2601 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2601step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2601 raw2601Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw2601 raw2601Labels = mixedMoment B raw2601step0 raw2601step0Labels := by
      have ha : raw2601step0 = (fun i j => raw2601 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2601step0 raw2601; decide +kernel
      have hl : raw2601step0Labels = raw2601Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2601 raw2601Labels permutation152 permutation4
    mixedMoment B raw2601step0 raw2601step0Labels = mixedMoment B raw2601step1 raw2601step1Labels := by
      have ha : raw2601step1 = raw2601step0 := by apply Matrix.ext; unfold raw2601step1 raw2601step0; decide +kernel
      have hl : raw2601step0Labels = labelEmbedding7 ∘ raw2601step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2601step0 raw2601step0Labels raw2601step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw2602 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2602Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2602step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2602 raw2602Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw2602 raw2602Labels = mixedMoment B raw2602step0 raw2602step0Labels := by
      have ha : raw2602step0 = (fun i j => raw2602 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2602step0 raw2602; decide +kernel
      have hl : raw2602step0Labels = raw2602Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2602 raw2602Labels permutation152 permutation4
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw2603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2603Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2603step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2603step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2603 raw2603Labels = mixedMoment B node4046 node4046Labels := by
  calc
    mixedMoment B raw2603 raw2603Labels = mixedMoment B raw2603step0 raw2603step0Labels := by
      have ha : raw2603step0 = (fun i j => raw2603 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2603step0 raw2603; decide +kernel
      have hl : raw2603step0Labels = raw2603Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2603 raw2603Labels permutation160 permutation6
    mixedMoment B raw2603step0 raw2603step0Labels = mixedMoment B raw2603step1 raw2603step1Labels := by
      have ha : raw2603step1 = -raw2603step0 := by apply Matrix.ext; change ∀ i j, raw2603step1 i j = -(raw2603step0 i j); unfold raw2603step1 raw2603step0; decide +kernel
      have hl : raw2603step1Labels = raw2603step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2603step1 raw2603step1Labels = mixedMoment B raw2603step2 raw2603step2Labels := by
      have ha : raw2603step2 = raw2603step1 := by apply Matrix.ext; unfold raw2603step2 raw2603step1; decide +kernel
      have hl : raw2603step1Labels = labelEmbedding1 ∘ raw2603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2603step1 raw2603step1Labels raw2603step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4046 node4046Labels := by rfl

def raw2604 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2604step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2604 raw2604Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw2604 raw2604Labels = mixedMoment B raw2604step0 raw2604step0Labels := by
      have ha : raw2604step0 = (fun i j => raw2604 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2604step0 raw2604; decide +kernel
      have hl : raw2604step0Labels = raw2604Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2604 raw2604Labels permutation32 permutation4
    mixedMoment B raw2604step0 raw2604step0Labels = mixedMoment B raw2604step1 raw2604step1Labels := by
      have ha : raw2604step1 = raw2604step0 := by apply Matrix.ext; unfold raw2604step1 raw2604step0; decide +kernel
      have hl : raw2604step0Labels = labelEmbedding7 ∘ raw2604step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2604step0 raw2604step0Labels raw2604step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw2605 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2605Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2605step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2605 raw2605Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw2605 raw2605Labels = mixedMoment B raw2605step0 raw2605step0Labels := by
      have ha : raw2605step0 = (fun i j => raw2605 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2605step0 raw2605; decide +kernel
      have hl : raw2605step0Labels = raw2605Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2605 raw2605Labels permutation32 permutation4
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw2606 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2606Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2606 raw2606Labels = mixedMoment B node4047 node4047Labels := by
  calc
    mixedMoment B raw2606 raw2606Labels = mixedMoment B raw2606step0 raw2606step0Labels := by
      have ha : raw2606step0 = (fun i j => raw2606 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2606step0 raw2606; decide +kernel
      have hl : raw2606step0Labels = raw2606Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2606 raw2606Labels permutation149 permutation3
    mixedMoment B raw2606step0 raw2606step0Labels = mixedMoment B raw2606step1 raw2606step1Labels := by
      have ha : raw2606step1 = raw2606step0 := by apply Matrix.ext; unfold raw2606step1 raw2606step0; decide +kernel
      have hl : raw2606step0Labels = labelEmbedding1 ∘ raw2606step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2606step0 raw2606step0Labels raw2606step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4047 node4047Labels := by rfl

def raw2607 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2607step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2607 raw2607Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw2607 raw2607Labels = mixedMoment B raw2607step0 raw2607step0Labels := by
      have ha : raw2607step0 = (fun i j => raw2607 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2607step0 raw2607; decide +kernel
      have hl : raw2607step0Labels = raw2607Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2607 raw2607Labels permutation32 permutation4
    mixedMoment B raw2607step0 raw2607step0Labels = mixedMoment B raw2607step1 raw2607step1Labels := by
      have ha : raw2607step1 = raw2607step0 := by apply Matrix.ext; unfold raw2607step1 raw2607step0; decide +kernel
      have hl : raw2607step0Labels = labelEmbedding7 ∘ raw2607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2607step0 raw2607step0Labels raw2607step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw2608 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2608Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2608 raw2608Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2608 raw2608Labels = mixedMoment B raw2608step0 raw2608step0Labels := by
      have ha : raw2608step0 = (fun i j => raw2608 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2608step0 raw2608; decide +kernel
      have hl : raw2608step0Labels = raw2608Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2608 raw2608Labels permutation32 permutation4
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw2609 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2609Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2609step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2609step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2609 raw2609Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw2609 raw2609Labels = mixedMoment B raw2609step0 raw2609step0Labels := by
      have ha : raw2609step0 = (fun i j => raw2609 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2609step0 raw2609; decide +kernel
      have hl : raw2609step0Labels = raw2609Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2609 raw2609Labels permutation151 permutation6
    mixedMoment B raw2609step0 raw2609step0Labels = mixedMoment B raw2609step1 raw2609step1Labels := by
      have ha : raw2609step1 = raw2609step0 := by apply Matrix.ext; unfold raw2609step1 raw2609step0; decide +kernel
      have hl : raw2609step0Labels = labelEmbedding1 ∘ raw2609step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2609step0 raw2609step0Labels raw2609step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw2610 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2610step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2610step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2610 raw2610Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw2610 raw2610Labels = mixedMoment B raw2610step0 raw2610step0Labels := by
      have ha : raw2610step0 = (fun i j => raw2610 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2610step0 raw2610; decide +kernel
      have hl : raw2610step0Labels = raw2610Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2610 raw2610Labels permutation32 permutation4
    mixedMoment B raw2610step0 raw2610step0Labels = mixedMoment B raw2610step1 raw2610step1Labels := by
      have ha : raw2610step1 = raw2610step0 := by apply Matrix.ext; unfold raw2610step1 raw2610step0; decide +kernel
      have hl : raw2610step0Labels = labelEmbedding7 ∘ raw2610step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2610step0 raw2610step0Labels raw2610step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw2611 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2611Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2611 raw2611Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw2611 raw2611Labels = mixedMoment B raw2611step0 raw2611step0Labels := by
      have ha : raw2611step0 = (fun i j => raw2611 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2611step0 raw2611; decide +kernel
      have hl : raw2611step0Labels = raw2611Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2611 raw2611Labels permutation32 permutation4
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw2612 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2612Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2612 raw2612Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw2612 raw2612Labels = mixedMoment B raw2612step0 raw2612step0Labels := by
      have ha : raw2612step0 = (fun i j => raw2612 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2612step0 raw2612; decide +kernel
      have hl : raw2612step0Labels = raw2612Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2612 raw2612Labels permutation145 permutation6
    mixedMoment B raw2612step0 raw2612step0Labels = mixedMoment B raw2612step1 raw2612step1Labels := by
      have ha : raw2612step1 = raw2612step0 := by apply Matrix.ext; unfold raw2612step1 raw2612step0; decide +kernel
      have hl : raw2612step0Labels = labelEmbedding1 ∘ raw2612step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2612step0 raw2612step0Labels raw2612step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw2613 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2613 raw2613Labels = mixedMoment B node5490 node5490Labels := by
  calc
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw2614 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2614Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2614 raw2614Labels = mixedMoment B node4013 node4013Labels := by
  calc
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw2615 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2615Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2615 raw2615Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw2615 raw2615Labels = mixedMoment B raw2615step0 raw2615step0Labels := by
      have ha : raw2615step0 = (fun i j => raw2615 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2615step0 raw2615; decide +kernel
      have hl : raw2615step0Labels = raw2615Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2615 raw2615Labels permutation39 permutation3
    mixedMoment B raw2615step0 raw2615step0Labels = mixedMoment B raw2615step1 raw2615step1Labels := by
      have ha : raw2615step1 = raw2615step0 := by apply Matrix.ext; unfold raw2615step1 raw2615step0; decide +kernel
      have hl : raw2615step0Labels = labelEmbedding1 ∘ raw2615step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2615step0 raw2615step0Labels raw2615step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw2616 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2616 raw2616Labels = mixedMoment B node5491 node5491Labels := by
  calc
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw2617 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2617Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2617 raw2617Labels = mixedMoment B node4014 node4014Labels := by
  calc
    _ = mixedMoment B node4014 node4014Labels := by rfl

def raw2618 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2618Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2618step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2618step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw2618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2618 raw2618Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw2618 raw2618Labels = mixedMoment B raw2618step0 raw2618step0Labels := by
      have ha : raw2618step0 = (fun i j => raw2618 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2618step0 raw2618; decide +kernel
      have hl : raw2618step0Labels = raw2618Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2618 raw2618Labels permutation10 permutation3
    mixedMoment B raw2618step0 raw2618step0Labels = mixedMoment B raw2618step1 raw2618step1Labels := by
      have ha : raw2618step1 = raw2618step0 := by apply Matrix.ext; unfold raw2618step1 raw2618step0; decide +kernel
      have hl : raw2618step0Labels = labelEmbedding1 ∘ raw2618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2618step0 raw2618step0Labels raw2618step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4014 node4014Labels := by rfl

def raw2619 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2619 raw2619Labels = mixedMoment B node5492 node5492Labels := by
  calc
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw2620 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2620Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2620 raw2620Labels = mixedMoment B node4015 node4015Labels := by
  calc
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw2621 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw2621Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2621step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2621step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2621 raw2621Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw2621 raw2621Labels = mixedMoment B raw2621step0 raw2621step0Labels := by
      have ha : raw2621step0 = (fun i j => raw2621 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2621step0 raw2621; decide +kernel
      have hl : raw2621step0Labels = raw2621Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2621 raw2621Labels permutation9 permutation3
    mixedMoment B raw2621step0 raw2621step0Labels = mixedMoment B raw2621step1 raw2621step1Labels := by
      have ha : raw2621step1 = raw2621step0 := by apply Matrix.ext; unfold raw2621step1 raw2621step0; decide +kernel
      have hl : raw2621step0Labels = labelEmbedding1 ∘ raw2621step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2621step0 raw2621step0Labels raw2621step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw2622 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2622 raw2622Labels = mixedMoment B node5494 node5494Labels := by
  calc
    _ = mixedMoment B node5494 node5494Labels := by rfl

def raw2623 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2623Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2623 raw2623Labels = mixedMoment B node4020 node4020Labels := by
  calc
    _ = mixedMoment B node4020 node4020Labels := by rfl

def raw2624 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2624Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2624step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2624step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw2624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2624 raw2624Labels = mixedMoment B node4020 node4020Labels := by
  calc
    mixedMoment B raw2624 raw2624Labels = mixedMoment B raw2624step0 raw2624step0Labels := by
      have ha : raw2624step0 = (fun i j => raw2624 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2624step0 raw2624; decide +kernel
      have hl : raw2624step0Labels = raw2624Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2624 raw2624Labels permutation3 permutation3
    mixedMoment B raw2624step0 raw2624step0Labels = mixedMoment B raw2624step1 raw2624step1Labels := by
      have ha : raw2624step1 = raw2624step0 := by apply Matrix.ext; unfold raw2624step1 raw2624step0; decide +kernel
      have hl : raw2624step0Labels = labelEmbedding1 ∘ raw2624step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2624step0 raw2624step0Labels raw2624step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4020 node4020Labels := by rfl

def raw2625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2625 raw2625Labels = mixedMoment B node5498 node5498Labels := by
  calc
    _ = mixedMoment B node5498 node5498Labels := by rfl

def raw2626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2626Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2626 raw2626Labels = mixedMoment B node4051 node4051Labels := by
  calc
    _ = mixedMoment B node4051 node4051Labels := by rfl

def raw2627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2627Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw2627step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2627step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2627 raw2627Labels = mixedMoment B node4051 node4051Labels := by
  calc
    mixedMoment B raw2627 raw2627Labels = mixedMoment B raw2627step0 raw2627step0Labels := by
      have ha : raw2627step0 = (fun i j => raw2627 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2627step0 raw2627; decide +kernel
      have hl : raw2627step0Labels = raw2627Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2627 raw2627Labels permutation583 permutation3
    mixedMoment B raw2627step0 raw2627step0Labels = mixedMoment B raw2627step1 raw2627step1Labels := by
      have ha : raw2627step1 = -raw2627step0 := by apply Matrix.ext; change ∀ i j, raw2627step1 i j = -(raw2627step0 i j); unfold raw2627step1 raw2627step0; decide +kernel
      have hl : raw2627step1Labels = raw2627step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2627step1 raw2627step1Labels = mixedMoment B raw2627step2 raw2627step2Labels := by
      have ha : raw2627step2 = raw2627step1 := by apply Matrix.ext; unfold raw2627step2 raw2627step1; decide +kernel
      have hl : raw2627step1Labels = labelEmbedding1 ∘ raw2627step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2627step1 raw2627step1Labels raw2627step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4051 node4051Labels := by rfl

def raw2628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2628 raw2628Labels = mixedMoment B node5500 node5500Labels := by
  calc
    _ = mixedMoment B node5500 node5500Labels := by rfl

def raw2629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2629Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2629 raw2629Labels = mixedMoment B node4053 node4053Labels := by
  calc
    _ = mixedMoment B node4053 node4053Labels := by rfl

def raw2630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2630Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2630 raw2630Labels = mixedMoment B node4053 node4053Labels := by
  calc
    mixedMoment B raw2630 raw2630Labels = mixedMoment B raw2630step0 raw2630step0Labels := by
      have ha : raw2630step0 = (fun i j => raw2630 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2630step0 raw2630; decide +kernel
      have hl : raw2630step0Labels = raw2630Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2630 raw2630Labels permutation272 permutation3
    mixedMoment B raw2630step0 raw2630step0Labels = mixedMoment B raw2630step1 raw2630step1Labels := by
      have ha : raw2630step1 = raw2630step0 := by apply Matrix.ext; unfold raw2630step1 raw2630step0; decide +kernel
      have hl : raw2630step0Labels = labelEmbedding1 ∘ raw2630step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2630step0 raw2630step0Labels raw2630step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4053 node4053Labels := by rfl

def raw2631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2631step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2631step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2631step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2631step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2631step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2631step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2631step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2631step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2631 raw2631Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2631 raw2631Labels = mixedMoment B raw2631step0 raw2631step0Labels := by
      have hz : ∀ j, raw2631 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2631step0 = (fun i j => raw2631 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2631step0 raw2631; decide +kernel
      have hl : raw2631step0Labels = raw2631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2631 raw2631Labels permutation434 hz
    mixedMoment B raw2631step0 raw2631step0Labels = mixedMoment B raw2631step1 raw2631step1Labels := by
      have hz : ∀ j, raw2631step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2631step1 = (fun i j => raw2631step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2631step1 raw2631step0; decide +kernel
      have hl : raw2631step1Labels = raw2631step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2631step0 raw2631step0Labels permutation80 hz
    mixedMoment B raw2631step1 raw2631step1Labels = mixedMoment B raw2631step2 raw2631step2Labels := by
      have ha : raw2631step2 = (fun i j => raw2631step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2631step2 raw2631step1; decide +kernel
      have hl : raw2631step2Labels = raw2631step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2631step1 raw2631step1Labels permutation22 permutation4
    mixedMoment B raw2631step2 raw2631step2Labels = mixedMoment B raw2631step3 raw2631step3Labels := by
      have ha : raw2631step3 = -raw2631step2 := by apply Matrix.ext; change ∀ i j, raw2631step3 i j = -(raw2631step2 i j); unfold raw2631step3 raw2631step2; decide +kernel
      have hl : raw2631step3Labels = raw2631step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2631step3 raw2631step3Labels = mixedMoment B raw2631step4 raw2631step4Labels := by
      have ha : raw2631step4 = raw2631step3 := by apply Matrix.ext; unfold raw2631step4 raw2631step3; decide +kernel
      have hl : raw2631step3Labels = labelEmbedding7 ∘ raw2631step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2631step3 raw2631step3Labels raw2631step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2632step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2632step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2632step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2632step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2632step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2632step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2632step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2632step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2632 raw2632Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2632 raw2632Labels = mixedMoment B raw2632step0 raw2632step0Labels := by
      have hz : ∀ j, raw2632 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2632step0 = (fun i j => raw2632 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2632step0 raw2632; decide +kernel
      have hl : raw2632step0Labels = raw2632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2632 raw2632Labels permutation434 hz
    mixedMoment B raw2632step0 raw2632step0Labels = mixedMoment B raw2632step1 raw2632step1Labels := by
      have hz : ∀ j, raw2632step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2632step1 = (fun i j => raw2632step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2632step1 raw2632step0; decide +kernel
      have hl : raw2632step1Labels = raw2632step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2632step0 raw2632step0Labels permutation56 hz
    mixedMoment B raw2632step1 raw2632step1Labels = mixedMoment B raw2632step2 raw2632step2Labels := by
      have ha : raw2632step2 = (fun i j => raw2632step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2632step2 raw2632step1; decide +kernel
      have hl : raw2632step2Labels = raw2632step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2632step1 raw2632step1Labels permutation22 permutation4
    mixedMoment B raw2632step2 raw2632step2Labels = mixedMoment B raw2632step3 raw2632step3Labels := by
      have ha : raw2632step3 = -raw2632step2 := by apply Matrix.ext; change ∀ i j, raw2632step3 i j = -(raw2632step2 i j); unfold raw2632step3 raw2632step2; decide +kernel
      have hl : raw2632step3Labels = raw2632step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2632step3 raw2632step3Labels = mixedMoment B raw2632step4 raw2632step4Labels := by
      have ha : raw2632step4 = raw2632step3 := by apply Matrix.ext; unfold raw2632step4 raw2632step3; decide +kernel
      have hl : raw2632step3Labels = labelEmbedding7 ∘ raw2632step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2632step3 raw2632step3Labels raw2632step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2633step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2633step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2633step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2633step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2633step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2633step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2633step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2633step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2633 raw2633Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2633 raw2633Labels = mixedMoment B raw2633step0 raw2633step0Labels := by
      have hz : ∀ j, raw2633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2633step0 = (fun i j => raw2633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2633step0 raw2633; decide +kernel
      have hl : raw2633step0Labels = raw2633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2633 raw2633Labels permutation346 hz
    mixedMoment B raw2633step0 raw2633step0Labels = mixedMoment B raw2633step1 raw2633step1Labels := by
      have hz : ∀ j, raw2633step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2633step1 = (fun i j => raw2633step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2633step1 raw2633step0; decide +kernel
      have hl : raw2633step1Labels = raw2633step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2633step0 raw2633step0Labels permutation56 hz
    mixedMoment B raw2633step1 raw2633step1Labels = mixedMoment B raw2633step2 raw2633step2Labels := by
      have ha : raw2633step2 = (fun i j => raw2633step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2633step2 raw2633step1; decide +kernel
      have hl : raw2633step2Labels = raw2633step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2633step1 raw2633step1Labels permutation22 permutation4
    mixedMoment B raw2633step2 raw2633step2Labels = mixedMoment B raw2633step3 raw2633step3Labels := by
      have ha : raw2633step3 = -raw2633step2 := by apply Matrix.ext; change ∀ i j, raw2633step3 i j = -(raw2633step2 i j); unfold raw2633step3 raw2633step2; decide +kernel
      have hl : raw2633step3Labels = raw2633step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2633step3 raw2633step3Labels = mixedMoment B raw2633step4 raw2633step4Labels := by
      have ha : raw2633step4 = raw2633step3 := by apply Matrix.ext; unfold raw2633step4 raw2633step3; decide +kernel
      have hl : raw2633step3Labels = labelEmbedding7 ∘ raw2633step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2633step3 raw2633step3Labels raw2633step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2634step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2634step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2634step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 3, -2], ![2, -2, 0]]
def raw2634step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2634step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw2634step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2634step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2634step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2634step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2634step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2634 raw2634Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2634 raw2634Labels = mixedMoment B raw2634step0 raw2634step0Labels := by
      have hz : ∀ j, raw2634 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2634step0 = (fun i j => raw2634 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2634step0 raw2634; decide +kernel
      have hl : raw2634step0Labels = raw2634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2634 raw2634Labels permutation434 hz
    mixedMoment B raw2634step0 raw2634step0Labels = mixedMoment B raw2634step1 raw2634step1Labels := by
      have hz : ∀ j, raw2634step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2634step1 = (fun i j => raw2634step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2634step1 raw2634step0; decide +kernel
      have hl : raw2634step1Labels = raw2634step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2634step0 raw2634step0Labels permutation80 hz
    mixedMoment B raw2634step1 raw2634step1Labels = mixedMoment B raw2634step2 raw2634step2Labels := by
      have hz : ∀ j, raw2634step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2634step2 = (fun i j => raw2634step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2634step2 raw2634step1; decide +kernel
      have hl : raw2634step2Labels = raw2634step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2634step1 raw2634step1Labels permutation14 hz
    mixedMoment B raw2634step2 raw2634step2Labels = mixedMoment B raw2634step3 raw2634step3Labels := by
      have ha : raw2634step3 = (fun i j => raw2634step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2634step3 raw2634step2; decide +kernel
      have hl : raw2634step3Labels = raw2634step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2634step2 raw2634step2Labels permutation4 permutation4
    mixedMoment B raw2634step3 raw2634step3Labels = mixedMoment B raw2634step4 raw2634step4Labels := by
      have ha : raw2634step4 = -raw2634step3 := by apply Matrix.ext; change ∀ i j, raw2634step4 i j = -(raw2634step3 i j); unfold raw2634step4 raw2634step3; decide +kernel
      have hl : raw2634step4Labels = raw2634step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2634step4 raw2634step4Labels = mixedMoment B raw2634step5 raw2634step5Labels := by
      have ha : raw2634step5 = raw2634step4 := by apply Matrix.ext; unfold raw2634step5 raw2634step4; decide +kernel
      have hl : raw2634step4Labels = labelEmbedding7 ∘ raw2634step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2634step4 raw2634step4Labels raw2634step5Labels labelEmbedding7 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw2635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2635step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2635step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 2, -2], ![1, -1, 0]]
def raw2635step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2635step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2635step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2635step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2635step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2635 raw2635Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2635 raw2635Labels = mixedMoment B raw2635step0 raw2635step0Labels := by
      have hz : ∀ j, raw2635 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2635step0 = (fun i j => raw2635 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2635step0 raw2635; decide +kernel
      have hl : raw2635step0Labels = raw2635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2635 raw2635Labels permutation434 hz
    mixedMoment B raw2635step0 raw2635step0Labels = mixedMoment B raw2635step1 raw2635step1Labels := by
      have hz : ∀ j, raw2635step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2635step1 = (fun i j => raw2635step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2635step1 raw2635step0; decide +kernel
      have hl : raw2635step1Labels = raw2635step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2635step0 raw2635step0Labels permutation80 hz
    mixedMoment B raw2635step1 raw2635step1Labels = mixedMoment B raw2635step2 raw2635step2Labels := by
      have hz : ∀ j, raw2635step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2635step2 = (fun i j => raw2635step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2635step2 raw2635step1; decide +kernel
      have hl : raw2635step2Labels = raw2635step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2635step1 raw2635step1Labels permutation14 hz
    mixedMoment B raw2635step2 raw2635step2Labels = mixedMoment B raw2635step3 raw2635step3Labels := by
      have ha : raw2635step3 = (fun i j => raw2635step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2635step3 raw2635step2; decide +kernel
      have hl : raw2635step3Labels = raw2635step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2635step2 raw2635step2Labels permutation5 permutation6
    mixedMoment B raw2635step3 raw2635step3Labels = mixedMoment B raw2635step4 raw2635step4Labels := by
      have ha : raw2635step4 = raw2635step3 := by apply Matrix.ext; unfold raw2635step4 raw2635step3; decide +kernel
      have hl : raw2635step3Labels = labelEmbedding9 ∘ raw2635step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2635step3 raw2635step3Labels raw2635step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw2636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2636step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2636step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2636step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2636 raw2636Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2636 raw2636Labels = mixedMoment B raw2636step0 raw2636step0Labels := by
      have hz : ∀ j, raw2636 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2636step0 = (fun i j => raw2636 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2636step0 raw2636; decide +kernel
      have hl : raw2636step0Labels = raw2636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2636 raw2636Labels permutation434 hz
    mixedMoment B raw2636step0 raw2636step0Labels = mixedMoment B raw2636step1 raw2636step1Labels := by
      have hz : ∀ j, raw2636step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2636step1 = (fun i j => raw2636step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2636step1 raw2636step0; decide +kernel
      have hl : raw2636step1Labels = raw2636step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2636step0 raw2636step0Labels permutation80 hz
    mixedMoment B raw2636step1 raw2636step1Labels = mixedMoment B raw2636step2 raw2636step2Labels := by
      have ha : raw2636step2 = (fun i j => raw2636step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2636step2 raw2636step1; decide +kernel
      have hl : raw2636step2Labels = raw2636step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2636step1 raw2636step1Labels permutation10 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw2637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2637step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2637step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2637step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2637step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2637 raw2637Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2637 raw2637Labels = mixedMoment B raw2637step0 raw2637step0Labels := by
      have hz : ∀ j, raw2637 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2637step0 = (fun i j => raw2637 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2637step0 raw2637; decide +kernel
      have hl : raw2637step0Labels = raw2637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2637 raw2637Labels permutation434 hz
    mixedMoment B raw2637step0 raw2637step0Labels = mixedMoment B raw2637step1 raw2637step1Labels := by
      have ha : raw2637step1 = (fun i j => raw2637step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2637step1 raw2637step0; decide +kernel
      have hl : raw2637step1Labels = raw2637step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2637step0 raw2637step0Labels permutation139 permutation3
    mixedMoment B raw2637step1 raw2637step1Labels = mixedMoment B raw2637step2 raw2637step2Labels := by
      have ha : raw2637step2 = -raw2637step1 := by apply Matrix.ext; change ∀ i j, raw2637step2 i j = -(raw2637step1 i j); unfold raw2637step2 raw2637step1; decide +kernel
      have hl : raw2637step2Labels = raw2637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2637step2 raw2637step2Labels = mixedMoment B raw2637step3 raw2637step3Labels := by
      have ha : raw2637step3 = raw2637step2 := by apply Matrix.ext; unfold raw2637step3 raw2637step2; decide +kernel
      have hl : raw2637step2Labels = labelEmbedding6 ∘ raw2637step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2637step2 raw2637step2Labels raw2637step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw2638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2638step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2638step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2638step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2638step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2638step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2638 raw2638Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2638 raw2638Labels = mixedMoment B raw2638step0 raw2638step0Labels := by
      have hz : ∀ j, raw2638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2638step0 = (fun i j => raw2638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2638step0 raw2638; decide +kernel
      have hl : raw2638step0Labels = raw2638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2638 raw2638Labels permutation346 hz
    mixedMoment B raw2638step0 raw2638step0Labels = mixedMoment B raw2638step1 raw2638step1Labels := by
      have ha : raw2638step1 = (fun i j => raw2638step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2638step1 raw2638step0; decide +kernel
      have hl : raw2638step1Labels = raw2638step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2638step0 raw2638step0Labels permutation139 permutation3
    mixedMoment B raw2638step1 raw2638step1Labels = mixedMoment B raw2638step2 raw2638step2Labels := by
      have ha : raw2638step2 = -raw2638step1 := by apply Matrix.ext; change ∀ i j, raw2638step2 i j = -(raw2638step1 i j); unfold raw2638step2 raw2638step1; decide +kernel
      have hl : raw2638step2Labels = raw2638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2638step2 raw2638step2Labels = mixedMoment B raw2638step3 raw2638step3Labels := by
      have ha : raw2638step3 = raw2638step2 := by apply Matrix.ext; unfold raw2638step3 raw2638step2; decide +kernel
      have hl : raw2638step2Labels = labelEmbedding6 ∘ raw2638step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2638step2 raw2638step2Labels raw2638step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw2639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2639step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2639step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw2639step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2639step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2639step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2639step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2639step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2639 raw2639Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2639 raw2639Labels = mixedMoment B raw2639step0 raw2639step0Labels := by
      have hz : ∀ j, raw2639 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2639step0 = (fun i j => raw2639 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2639step0 raw2639; decide +kernel
      have hl : raw2639step0Labels = raw2639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2639 raw2639Labels permutation434 hz
    mixedMoment B raw2639step0 raw2639step0Labels = mixedMoment B raw2639step1 raw2639step1Labels := by
      have hz : ∀ j, raw2639step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2639step1 = (fun i j => raw2639step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2639step1 raw2639step0; decide +kernel
      have hl : raw2639step1Labels = raw2639step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2639step0 raw2639step0Labels permutation80 hz
    mixedMoment B raw2639step1 raw2639step1Labels = mixedMoment B raw2639step2 raw2639step2Labels := by
      have ha : raw2639step2 = (fun i j => raw2639step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2639step2 raw2639step1; decide +kernel
      have hl : raw2639step2Labels = raw2639step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2639step1 raw2639step1Labels permutation20 permutation4
    mixedMoment B raw2639step2 raw2639step2Labels = mixedMoment B raw2639step3 raw2639step3Labels := by
      have ha : raw2639step3 = -raw2639step2 := by apply Matrix.ext; change ∀ i j, raw2639step3 i j = -(raw2639step2 i j); unfold raw2639step3 raw2639step2; decide +kernel
      have hl : raw2639step3Labels = raw2639step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2639step3 raw2639step3Labels = mixedMoment B raw2639step4 raw2639step4Labels := by
      have ha : raw2639step4 = raw2639step3 := by apply Matrix.ext; unfold raw2639step4 raw2639step3; decide +kernel
      have hl : raw2639step3Labels = labelEmbedding7 ∘ raw2639step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2639step3 raw2639step3Labels raw2639step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw2640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2640step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2640step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2640step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2640step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2640step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2640step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2640 raw2640Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2640 raw2640Labels = mixedMoment B raw2640step0 raw2640step0Labels := by
      have hz : ∀ j, raw2640 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2640step0 = (fun i j => raw2640 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2640step0 raw2640; decide +kernel
      have hl : raw2640step0Labels = raw2640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2640 raw2640Labels permutation434 hz
    mixedMoment B raw2640step0 raw2640step0Labels = mixedMoment B raw2640step1 raw2640step1Labels := by
      have hz : ∀ j, raw2640step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2640step1 = (fun i j => raw2640step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2640step1 raw2640step0; decide +kernel
      have hl : raw2640step1Labels = raw2640step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2640step0 raw2640step0Labels permutation80 hz
    mixedMoment B raw2640step1 raw2640step1Labels = mixedMoment B raw2640step2 raw2640step2Labels := by
      have ha : raw2640step2 = (fun i j => raw2640step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2640step2 raw2640step1; decide +kernel
      have hl : raw2640step2Labels = raw2640step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2640step1 raw2640step1Labels permutation23 permutation6
    mixedMoment B raw2640step2 raw2640step2Labels = mixedMoment B raw2640step3 raw2640step3Labels := by
      have ha : raw2640step3 = raw2640step2 := by apply Matrix.ext; unfold raw2640step3 raw2640step2; decide +kernel
      have hl : raw2640step2Labels = labelEmbedding9 ∘ raw2640step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2640step2 raw2640step2Labels raw2640step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2641step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2641step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2641step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2641step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2641 raw2641Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2641 raw2641Labels = mixedMoment B raw2641step0 raw2641step0Labels := by
      have hz : ∀ j, raw2641 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2641step0 = (fun i j => raw2641 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2641step0 raw2641; decide +kernel
      have hl : raw2641step0Labels = raw2641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2641 raw2641Labels permutation434 hz
    mixedMoment B raw2641step0 raw2641step0Labels = mixedMoment B raw2641step1 raw2641step1Labels := by
      have hz : ∀ j, raw2641step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2641step1 = (fun i j => raw2641step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2641step1 raw2641step0; decide +kernel
      have hl : raw2641step1Labels = raw2641step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2641step0 raw2641step0Labels permutation56 hz
    mixedMoment B raw2641step1 raw2641step1Labels = mixedMoment B raw2641step2 raw2641step2Labels := by
      have ha : raw2641step2 = (fun i j => raw2641step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2641step2 raw2641step1; decide +kernel
      have hl : raw2641step2Labels = raw2641step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2641step1 raw2641step1Labels permutation10 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw2642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2642step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2642step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2642step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2642step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2642 raw2642Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2642 raw2642Labels = mixedMoment B raw2642step0 raw2642step0Labels := by
      have hz : ∀ j, raw2642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2642step0 = (fun i j => raw2642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2642step0 raw2642; decide +kernel
      have hl : raw2642step0Labels = raw2642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2642 raw2642Labels permutation434 hz
    mixedMoment B raw2642step0 raw2642step0Labels = mixedMoment B raw2642step1 raw2642step1Labels := by
      have ha : raw2642step1 = (fun i j => raw2642step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2642step1 raw2642step0; decide +kernel
      have hl : raw2642step1Labels = raw2642step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2642step0 raw2642step0Labels permutation145 permutation3
    mixedMoment B raw2642step1 raw2642step1Labels = mixedMoment B raw2642step2 raw2642step2Labels := by
      have ha : raw2642step2 = -raw2642step1 := by apply Matrix.ext; change ∀ i j, raw2642step2 i j = -(raw2642step1 i j); unfold raw2642step2 raw2642step1; decide +kernel
      have hl : raw2642step2Labels = raw2642step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2642step2 raw2642step2Labels = mixedMoment B raw2642step3 raw2642step3Labels := by
      have ha : raw2642step3 = raw2642step2 := by apply Matrix.ext; unfold raw2642step3 raw2642step2; decide +kernel
      have hl : raw2642step2Labels = labelEmbedding6 ∘ raw2642step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2642step2 raw2642step2Labels raw2642step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw2643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2643step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2643step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2643step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2643step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2643step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2643 raw2643Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2643 raw2643Labels = mixedMoment B raw2643step0 raw2643step0Labels := by
      have hz : ∀ j, raw2643 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2643step0 = (fun i j => raw2643 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2643step0 raw2643; decide +kernel
      have hl : raw2643step0Labels = raw2643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2643 raw2643Labels permutation265 hz
    mixedMoment B raw2643step0 raw2643step0Labels = mixedMoment B raw2643step1 raw2643step1Labels := by
      have ha : raw2643step1 = (fun i j => raw2643step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2643step1 raw2643step0; decide +kernel
      have hl : raw2643step1Labels = raw2643step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2643step0 raw2643step0Labels permutation139 permutation3
    mixedMoment B raw2643step1 raw2643step1Labels = mixedMoment B raw2643step2 raw2643step2Labels := by
      have ha : raw2643step2 = -raw2643step1 := by apply Matrix.ext; change ∀ i j, raw2643step2 i j = -(raw2643step1 i j); unfold raw2643step2 raw2643step1; decide +kernel
      have hl : raw2643step2Labels = raw2643step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2643step2 raw2643step2Labels = mixedMoment B raw2643step3 raw2643step3Labels := by
      have ha : raw2643step3 = raw2643step2 := by apply Matrix.ext; unfold raw2643step3 raw2643step2; decide +kernel
      have hl : raw2643step2Labels = labelEmbedding6 ∘ raw2643step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2643step2 raw2643step2Labels raw2643step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw2644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2644step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2644step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2644step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw2644step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2644step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2644step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2644step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2644step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2644 raw2644Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2644 raw2644Labels = mixedMoment B raw2644step0 raw2644step0Labels := by
      have hz : ∀ j, raw2644 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2644step0 = (fun i j => raw2644 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2644step0 raw2644; decide +kernel
      have hl : raw2644step0Labels = raw2644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2644 raw2644Labels permutation434 hz
    mixedMoment B raw2644step0 raw2644step0Labels = mixedMoment B raw2644step1 raw2644step1Labels := by
      have hz : ∀ j, raw2644step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2644step1 = (fun i j => raw2644step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2644step1 raw2644step0; decide +kernel
      have hl : raw2644step1Labels = raw2644step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2644step0 raw2644step0Labels permutation56 hz
    mixedMoment B raw2644step1 raw2644step1Labels = mixedMoment B raw2644step2 raw2644step2Labels := by
      have ha : raw2644step2 = (fun i j => raw2644step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2644step2 raw2644step1; decide +kernel
      have hl : raw2644step2Labels = raw2644step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2644step1 raw2644step1Labels permutation20 permutation4
    mixedMoment B raw2644step2 raw2644step2Labels = mixedMoment B raw2644step3 raw2644step3Labels := by
      have ha : raw2644step3 = -raw2644step2 := by apply Matrix.ext; change ∀ i j, raw2644step3 i j = -(raw2644step2 i j); unfold raw2644step3 raw2644step2; decide +kernel
      have hl : raw2644step3Labels = raw2644step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2644step3 raw2644step3Labels = mixedMoment B raw2644step4 raw2644step4Labels := by
      have ha : raw2644step4 = raw2644step3 := by apply Matrix.ext; unfold raw2644step4 raw2644step3; decide +kernel
      have hl : raw2644step3Labels = labelEmbedding7 ∘ raw2644step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2644step3 raw2644step3Labels raw2644step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw2645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2645step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2645step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2645step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2645step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2645step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2645step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2645 raw2645Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2645 raw2645Labels = mixedMoment B raw2645step0 raw2645step0Labels := by
      have hz : ∀ j, raw2645 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2645step0 = (fun i j => raw2645 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2645step0 raw2645; decide +kernel
      have hl : raw2645step0Labels = raw2645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2645 raw2645Labels permutation434 hz
    mixedMoment B raw2645step0 raw2645step0Labels = mixedMoment B raw2645step1 raw2645step1Labels := by
      have hz : ∀ j, raw2645step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2645step1 = (fun i j => raw2645step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2645step1 raw2645step0; decide +kernel
      have hl : raw2645step1Labels = raw2645step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2645step0 raw2645step0Labels permutation56 hz
    mixedMoment B raw2645step1 raw2645step1Labels = mixedMoment B raw2645step2 raw2645step2Labels := by
      have ha : raw2645step2 = (fun i j => raw2645step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2645step2 raw2645step1; decide +kernel
      have hl : raw2645step2Labels = raw2645step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2645step1 raw2645step1Labels permutation23 permutation6
    mixedMoment B raw2645step2 raw2645step2Labels = mixedMoment B raw2645step3 raw2645step3Labels := by
      have ha : raw2645step3 = raw2645step2 := by apply Matrix.ext; unfold raw2645step3 raw2645step2; decide +kernel
      have hl : raw2645step2Labels = labelEmbedding9 ∘ raw2645step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2645step2 raw2645step2Labels raw2645step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2646step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2646step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2646step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2646 raw2646Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2646 raw2646Labels = mixedMoment B raw2646step0 raw2646step0Labels := by
      have hz : ∀ j, raw2646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2646step0 = (fun i j => raw2646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2646step0 raw2646; decide +kernel
      have hl : raw2646step0Labels = raw2646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2646 raw2646Labels permutation346 hz
    mixedMoment B raw2646step0 raw2646step0Labels = mixedMoment B raw2646step1 raw2646step1Labels := by
      have hz : ∀ j, raw2646step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2646step1 = (fun i j => raw2646step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2646step1 raw2646step0; decide +kernel
      have hl : raw2646step1Labels = raw2646step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2646step0 raw2646step0Labels permutation56 hz
    mixedMoment B raw2646step1 raw2646step1Labels = mixedMoment B raw2646step2 raw2646step2Labels := by
      have ha : raw2646step2 = (fun i j => raw2646step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2646step2 raw2646step1; decide +kernel
      have hl : raw2646step2Labels = raw2646step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2646step1 raw2646step1Labels permutation10 permutation2
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw2647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2647step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2647step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2647step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2647step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2647 raw2647Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2647 raw2647Labels = mixedMoment B raw2647step0 raw2647step0Labels := by
      have hz : ∀ j, raw2647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2647step0 = (fun i j => raw2647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2647step0 raw2647; decide +kernel
      have hl : raw2647step0Labels = raw2647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2647 raw2647Labels permutation346 hz
    mixedMoment B raw2647step0 raw2647step0Labels = mixedMoment B raw2647step1 raw2647step1Labels := by
      have ha : raw2647step1 = (fun i j => raw2647step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2647step1 raw2647step0; decide +kernel
      have hl : raw2647step1Labels = raw2647step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2647step0 raw2647step0Labels permutation145 permutation3
    mixedMoment B raw2647step1 raw2647step1Labels = mixedMoment B raw2647step2 raw2647step2Labels := by
      have ha : raw2647step2 = -raw2647step1 := by apply Matrix.ext; change ∀ i j, raw2647step2 i j = -(raw2647step1 i j); unfold raw2647step2 raw2647step1; decide +kernel
      have hl : raw2647step2Labels = raw2647step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2647step2 raw2647step2Labels = mixedMoment B raw2647step3 raw2647step3Labels := by
      have ha : raw2647step3 = raw2647step2 := by apply Matrix.ext; unfold raw2647step3 raw2647step2; decide +kernel
      have hl : raw2647step2Labels = labelEmbedding6 ∘ raw2647step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2647step2 raw2647step2Labels raw2647step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw2648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw2648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2648step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2648step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2648step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2648step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2648 raw2648Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2648 raw2648Labels = mixedMoment B raw2648step0 raw2648step0Labels := by
      have hz : ∀ j, raw2648 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2648step0 = (fun i j => raw2648 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2648step0 raw2648; decide +kernel
      have hl : raw2648step0Labels = raw2648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2648 raw2648Labels permutation265 hz
    mixedMoment B raw2648step0 raw2648step0Labels = mixedMoment B raw2648step1 raw2648step1Labels := by
      have ha : raw2648step1 = (fun i j => raw2648step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2648step1 raw2648step0; decide +kernel
      have hl : raw2648step1Labels = raw2648step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2648step0 raw2648step0Labels permutation145 permutation3
    mixedMoment B raw2648step1 raw2648step1Labels = mixedMoment B raw2648step2 raw2648step2Labels := by
      have ha : raw2648step2 = -raw2648step1 := by apply Matrix.ext; change ∀ i j, raw2648step2 i j = -(raw2648step1 i j); unfold raw2648step2 raw2648step1; decide +kernel
      have hl : raw2648step2Labels = raw2648step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2648step2 raw2648step2Labels = mixedMoment B raw2648step3 raw2648step3Labels := by
      have ha : raw2648step3 = raw2648step2 := by apply Matrix.ext; unfold raw2648step3 raw2648step2; decide +kernel
      have hl : raw2648step2Labels = labelEmbedding6 ∘ raw2648step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2648step2 raw2648step2Labels raw2648step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw2649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2649step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2649step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 3, -2], ![2, -2, 0]]
def raw2649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2649step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw2649step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2649step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2649step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2649step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw2649step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2649 raw2649Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw2649 raw2649Labels = mixedMoment B raw2649step0 raw2649step0Labels := by
      have hz : ∀ j, raw2649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2649step0 = (fun i j => raw2649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2649step0 raw2649; decide +kernel
      have hl : raw2649step0Labels = raw2649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2649 raw2649Labels permutation346 hz
    mixedMoment B raw2649step0 raw2649step0Labels = mixedMoment B raw2649step1 raw2649step1Labels := by
      have hz : ∀ j, raw2649step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2649step1 = (fun i j => raw2649step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2649step1 raw2649step0; decide +kernel
      have hl : raw2649step1Labels = raw2649step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2649step0 raw2649step0Labels permutation56 hz
    mixedMoment B raw2649step1 raw2649step1Labels = mixedMoment B raw2649step2 raw2649step2Labels := by
      have ha : raw2649step2 = (fun i j => raw2649step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2649step2 raw2649step1; decide +kernel
      have hl : raw2649step2Labels = raw2649step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2649step1 raw2649step1Labels permutation20 permutation4
    mixedMoment B raw2649step2 raw2649step2Labels = mixedMoment B raw2649step3 raw2649step3Labels := by
      have ha : raw2649step3 = -raw2649step2 := by apply Matrix.ext; change ∀ i j, raw2649step3 i j = -(raw2649step2 i j); unfold raw2649step3 raw2649step2; decide +kernel
      have hl : raw2649step3Labels = raw2649step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2649step3 raw2649step3Labels = mixedMoment B raw2649step4 raw2649step4Labels := by
      have ha : raw2649step4 = raw2649step3 := by apply Matrix.ext; unfold raw2649step4 raw2649step3; decide +kernel
      have hl : raw2649step3Labels = labelEmbedding7 ∘ raw2649step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2649step3 raw2649step3Labels raw2649step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw2650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2650step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0]]
def raw2650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2650step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2650step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2650step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2650step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2650 raw2650Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw2650 raw2650Labels = mixedMoment B raw2650step0 raw2650step0Labels := by
      have hz : ∀ j, raw2650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2650step0 = (fun i j => raw2650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2650step0 raw2650; decide +kernel
      have hl : raw2650step0Labels = raw2650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2650 raw2650Labels permutation346 hz
    mixedMoment B raw2650step0 raw2650step0Labels = mixedMoment B raw2650step1 raw2650step1Labels := by
      have hz : ∀ j, raw2650step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2650step1 = (fun i j => raw2650step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2650step1 raw2650step0; decide +kernel
      have hl : raw2650step1Labels = raw2650step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2650step0 raw2650step0Labels permutation56 hz
    mixedMoment B raw2650step1 raw2650step1Labels = mixedMoment B raw2650step2 raw2650step2Labels := by
      have ha : raw2650step2 = (fun i j => raw2650step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2650step2 raw2650step1; decide +kernel
      have hl : raw2650step2Labels = raw2650step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2650step1 raw2650step1Labels permutation23 permutation6
    mixedMoment B raw2650step2 raw2650step2Labels = mixedMoment B raw2650step3 raw2650step3Labels := by
      have ha : raw2650step3 = raw2650step2 := by apply Matrix.ext; unfold raw2650step3 raw2650step2; decide +kernel
      have hl : raw2650step2Labels = labelEmbedding9 ∘ raw2650step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2650step2 raw2650step2Labels raw2650step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw2651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2651step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2651step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2651step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw2651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2651 raw2651Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw2651 raw2651Labels = mixedMoment B raw2651step0 raw2651step0Labels := by
      have hz : ∀ j, raw2651 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2651step0 = (fun i j => raw2651 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2651step0 raw2651; decide +kernel
      have hl : raw2651step0Labels = raw2651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2651 raw2651Labels permutation434 hz
    mixedMoment B raw2651step0 raw2651step0Labels = mixedMoment B raw2651step1 raw2651step1Labels := by
      have hz : ∀ j, raw2651step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2651step1 = (fun i j => raw2651step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2651step1 raw2651step0; decide +kernel
      have hl : raw2651step1Labels = raw2651step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2651step0 raw2651step0Labels permutation80 hz
    mixedMoment B raw2651step1 raw2651step1Labels = mixedMoment B raw2651step2 raw2651step2Labels := by
      have hz : ∀ j, raw2651step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2651step2 = (fun i j => raw2651step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2651step2 raw2651step1; decide +kernel
      have hl : raw2651step2Labels = raw2651step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2651step1 raw2651step1Labels permutation14 hz
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw2652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2652step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2652step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2652step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2652 raw2652Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2652 raw2652Labels = mixedMoment B raw2652step0 raw2652step0Labels := by
      have hz : ∀ j, raw2652 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2652step0 = (fun i j => raw2652 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2652step0 raw2652; decide +kernel
      have hl : raw2652step0Labels = raw2652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2652 raw2652Labels permutation434 hz
    mixedMoment B raw2652step0 raw2652step0Labels = mixedMoment B raw2652step1 raw2652step1Labels := by
      have hz : ∀ j, raw2652step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2652step1 = (fun i j => raw2652step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2652step1 raw2652step0; decide +kernel
      have hl : raw2652step1Labels = raw2652step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2652step0 raw2652step0Labels permutation80 hz
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2653step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2653step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2653 raw2653Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2653 raw2653Labels = mixedMoment B raw2653step0 raw2653step0Labels := by
      have hz : ∀ j, raw2653 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2653step0 = (fun i j => raw2653 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2653step0 raw2653; decide +kernel
      have hl : raw2653step0Labels = raw2653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2653 raw2653Labels permutation434 hz
    mixedMoment B raw2653step0 raw2653step0Labels = mixedMoment B raw2653step1 raw2653step1Labels := by
      have hz : ∀ j, raw2653step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2653step1 = (fun i j => raw2653step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2653step1 raw2653step0; decide +kernel
      have hl : raw2653step1Labels = raw2653step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2653step0 raw2653step0Labels permutation56 hz
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2654Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2654step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2654step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2654step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2654 raw2654Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2654 raw2654Labels = mixedMoment B raw2654step0 raw2654step0Labels := by
      have hz : ∀ j, raw2654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2654step0 = (fun i j => raw2654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2654step0 raw2654; decide +kernel
      have hl : raw2654step0Labels = raw2654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2654 raw2654Labels permutation346 hz
    mixedMoment B raw2654step0 raw2654step0Labels = mixedMoment B raw2654step1 raw2654step1Labels := by
      have hz : ∀ j, raw2654step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2654step1 = (fun i j => raw2654step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2654step1 raw2654step0; decide +kernel
      have hl : raw2654step1Labels = raw2654step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2654step0 raw2654step0Labels permutation56 hz
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw2655Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2655step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw2655step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2655step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw2655step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2655step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 1, -2], ![1, -1, 0]]
def raw2655step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2655step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw2655step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2655step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2655step4Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw2655step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw2655step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2655 raw2655Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw2655 raw2655Labels = mixedMoment B raw2655step0 raw2655step0Labels := by
      have hz : ∀ j, raw2655 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2655step0 = (fun i j => raw2655 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2655step0 raw2655; decide +kernel
      have hl : raw2655step0Labels = raw2655Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2655 raw2655Labels permutation434 hz
    mixedMoment B raw2655step0 raw2655step0Labels = mixedMoment B raw2655step1 raw2655step1Labels := by
      have hz : ∀ j, raw2655step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2655step1 = (fun i j => raw2655step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2655step1 raw2655step0; decide +kernel
      have hl : raw2655step1Labels = raw2655step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2655step0 raw2655step0Labels permutation80 hz
    mixedMoment B raw2655step1 raw2655step1Labels = mixedMoment B raw2655step2 raw2655step2Labels := by
      have hz : ∀ j, raw2655step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2655step2 = (fun i j => raw2655step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2655step2 raw2655step1; decide +kernel
      have hl : raw2655step2Labels = raw2655step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2655step1 raw2655step1Labels permutation14 hz
    mixedMoment B raw2655step2 raw2655step2Labels = mixedMoment B raw2655step3 raw2655step3Labels := by
      have ha : raw2655step3 = (fun i j => raw2655step2 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw2655step3 raw2655step2; decide +kernel
      have hl : raw2655step3Labels = raw2655step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2655step2 raw2655step2Labels permutation3 permutation7
    mixedMoment B raw2655step3 raw2655step3Labels = mixedMoment B raw2655step4 raw2655step4Labels := by
      have ha : raw2655step4 = -raw2655step3 := by apply Matrix.ext; change ∀ i j, raw2655step4 i j = -(raw2655step3 i j); unfold raw2655step4 raw2655step3; decide +kernel
      have hl : raw2655step4Labels = raw2655step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2655step4 raw2655step4Labels = mixedMoment B raw2655step5 raw2655step5Labels := by
      have ha : raw2655step5 = raw2655step4 := by apply Matrix.ext; unfold raw2655step5 raw2655step4; decide +kernel
      have hl : raw2655step4Labels = labelEmbedding10 ∘ raw2655step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2655step4 raw2655step4Labels raw2655step5Labels labelEmbedding10 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw2656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2656Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2656step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2656step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2656step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2656step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw2656step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2656step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw2656step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2656step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw2656step4Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2656step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw2656step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2656 raw2656Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw2656 raw2656Labels = mixedMoment B raw2656step0 raw2656step0Labels := by
      have hz : ∀ j, raw2656 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2656step0 = (fun i j => raw2656 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2656step0 raw2656; decide +kernel
      have hl : raw2656step0Labels = raw2656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2656 raw2656Labels permutation434 hz
    mixedMoment B raw2656step0 raw2656step0Labels = mixedMoment B raw2656step1 raw2656step1Labels := by
      have hz : ∀ j, raw2656step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2656step1 = (fun i j => raw2656step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2656step1 raw2656step0; decide +kernel
      have hl : raw2656step1Labels = raw2656step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2656step0 raw2656step0Labels permutation80 hz
    mixedMoment B raw2656step1 raw2656step1Labels = mixedMoment B raw2656step2 raw2656step2Labels := by
      have hz : ∀ j, raw2656step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2656step2 = (fun i j => raw2656step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2656step2 raw2656step1; decide +kernel
      have hl : raw2656step2Labels = raw2656step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2656step1 raw2656step1Labels permutation14 hz
    mixedMoment B raw2656step2 raw2656step2Labels = mixedMoment B raw2656step3 raw2656step3Labels := by
      have ha : raw2656step3 = (fun i j => raw2656step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2656step3 raw2656step2; decide +kernel
      have hl : raw2656step3Labels = raw2656step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2656step2 raw2656step2Labels permutation7 permutation3
    mixedMoment B raw2656step3 raw2656step3Labels = mixedMoment B raw2656step4 raw2656step4Labels := by
      have ha : raw2656step4 = -raw2656step3 := by apply Matrix.ext; change ∀ i j, raw2656step4 i j = -(raw2656step3 i j); unfold raw2656step4 raw2656step3; decide +kernel
      have hl : raw2656step4Labels = raw2656step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2656step4 raw2656step4Labels = mixedMoment B raw2656step5 raw2656step5Labels := by
      have ha : raw2656step5 = raw2656step4 := by apply Matrix.ext; unfold raw2656step5 raw2656step4; decide +kernel
      have hl : raw2656step4Labels = labelEmbedding6 ∘ raw2656step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2656step4 raw2656step4Labels raw2656step5Labels labelEmbedding6 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw2657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2657Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2657step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2657step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2657step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2657step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2657step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2657step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2657step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2657step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2657step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2657 raw2657Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw2657 raw2657Labels = mixedMoment B raw2657step0 raw2657step0Labels := by
      have hz : ∀ j, raw2657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2657step0 = (fun i j => raw2657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2657step0 raw2657; decide +kernel
      have hl : raw2657step0Labels = raw2657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2657 raw2657Labels permutation434 hz
    mixedMoment B raw2657step0 raw2657step0Labels = mixedMoment B raw2657step1 raw2657step1Labels := by
      have hz : ∀ j, raw2657step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2657step1 = (fun i j => raw2657step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2657step1 raw2657step0; decide +kernel
      have hl : raw2657step1Labels = raw2657step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2657step0 raw2657step0Labels permutation80 hz
    mixedMoment B raw2657step1 raw2657step1Labels = mixedMoment B raw2657step2 raw2657step2Labels := by
      have ha : raw2657step2 = (fun i j => raw2657step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2657step2 raw2657step1; decide +kernel
      have hl : raw2657step2Labels = raw2657step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2657step1 raw2657step1Labels permutation31 permutation3
    mixedMoment B raw2657step2 raw2657step2Labels = mixedMoment B raw2657step3 raw2657step3Labels := by
      have ha : raw2657step3 = -raw2657step2 := by apply Matrix.ext; change ∀ i j, raw2657step3 i j = -(raw2657step2 i j); unfold raw2657step3 raw2657step2; decide +kernel
      have hl : raw2657step3Labels = raw2657step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2657step3 raw2657step3Labels = mixedMoment B raw2657step4 raw2657step4Labels := by
      have ha : raw2657step4 = raw2657step3 := by apply Matrix.ext; unfold raw2657step4 raw2657step3; decide +kernel
      have hl : raw2657step3Labels = labelEmbedding6 ∘ raw2657step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2657step3 raw2657step3Labels raw2657step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw2658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2658Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2658step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2658step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2658step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2658step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2658step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2658step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2658step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2658step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2658step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2658step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2658 raw2658Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw2658 raw2658Labels = mixedMoment B raw2658step0 raw2658step0Labels := by
      have hz : ∀ j, raw2658 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2658step0 = (fun i j => raw2658 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2658step0 raw2658; decide +kernel
      have hl : raw2658step0Labels = raw2658Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2658 raw2658Labels permutation434 hz
    mixedMoment B raw2658step0 raw2658step0Labels = mixedMoment B raw2658step1 raw2658step1Labels := by
      have hz : ∀ j, raw2658step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2658step1 = (fun i j => raw2658step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2658step1 raw2658step0; decide +kernel
      have hl : raw2658step1Labels = raw2658step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2658step0 raw2658step0Labels permutation56 hz
    mixedMoment B raw2658step1 raw2658step1Labels = mixedMoment B raw2658step2 raw2658step2Labels := by
      have ha : raw2658step2 = (fun i j => raw2658step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2658step2 raw2658step1; decide +kernel
      have hl : raw2658step2Labels = raw2658step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2658step1 raw2658step1Labels permutation31 permutation3
    mixedMoment B raw2658step2 raw2658step2Labels = mixedMoment B raw2658step3 raw2658step3Labels := by
      have ha : raw2658step3 = -raw2658step2 := by apply Matrix.ext; change ∀ i j, raw2658step3 i j = -(raw2658step2 i j); unfold raw2658step3 raw2658step2; decide +kernel
      have hl : raw2658step3Labels = raw2658step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2658step3 raw2658step3Labels = mixedMoment B raw2658step4 raw2658step4Labels := by
      have ha : raw2658step4 = raw2658step3 := by apply Matrix.ext; unfold raw2658step4 raw2658step3; decide +kernel
      have hl : raw2658step3Labels = labelEmbedding6 ∘ raw2658step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2658step3 raw2658step3Labels raw2658step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw2659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2659Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2659step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2659step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2659step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw2659step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2659step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2659step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2659step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2659step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2659step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2659step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2659 raw2659Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw2659 raw2659Labels = mixedMoment B raw2659step0 raw2659step0Labels := by
      have hz : ∀ j, raw2659 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2659step0 = (fun i j => raw2659 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2659step0 raw2659; decide +kernel
      have hl : raw2659step0Labels = raw2659Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2659 raw2659Labels permutation346 hz
    mixedMoment B raw2659step0 raw2659step0Labels = mixedMoment B raw2659step1 raw2659step1Labels := by
      have hz : ∀ j, raw2659step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2659step1 = (fun i j => raw2659step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2659step1 raw2659step0; decide +kernel
      have hl : raw2659step1Labels = raw2659step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2659step0 raw2659step0Labels permutation56 hz
    mixedMoment B raw2659step1 raw2659step1Labels = mixedMoment B raw2659step2 raw2659step2Labels := by
      have ha : raw2659step2 = (fun i j => raw2659step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2659step2 raw2659step1; decide +kernel
      have hl : raw2659step2Labels = raw2659step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2659step1 raw2659step1Labels permutation31 permutation3
    mixedMoment B raw2659step2 raw2659step2Labels = mixedMoment B raw2659step3 raw2659step3Labels := by
      have ha : raw2659step3 = -raw2659step2 := by apply Matrix.ext; change ∀ i j, raw2659step3 i j = -(raw2659step2 i j); unfold raw2659step3 raw2659step2; decide +kernel
      have hl : raw2659step3Labels = raw2659step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2659step3 raw2659step3Labels = mixedMoment B raw2659step4 raw2659step4Labels := by
      have ha : raw2659step4 = raw2659step3 := by apply Matrix.ext; unfold raw2659step4 raw2659step3; decide +kernel
      have hl : raw2659step3Labels = labelEmbedding6 ∘ raw2659step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2659step3 raw2659step3Labels raw2659step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw2660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw2660Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2660step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw2660step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2660step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 3, -2], ![3, -3, 0]]
def raw2660step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2660step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw2660step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2660step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw2660step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2660step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw2660step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2660 raw2660Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw2660 raw2660Labels = mixedMoment B raw2660step0 raw2660step0Labels := by
      have hz : ∀ j, raw2660 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw2660step0 = (fun i j => raw2660 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw2660step0 raw2660; decide +kernel
      have hl : raw2660step0Labels = raw2660Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2660 raw2660Labels permutation434 hz
    mixedMoment B raw2660step0 raw2660step0Labels = mixedMoment B raw2660step1 raw2660step1Labels := by
      have hz : ∀ j, raw2660step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw2660step1 = (fun i j => raw2660step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw2660step1 raw2660step0; decide +kernel
      have hl : raw2660step1Labels = raw2660step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2660step0 raw2660step0Labels permutation80 hz
    mixedMoment B raw2660step1 raw2660step1Labels = mixedMoment B raw2660step2 raw2660step2Labels := by
      have hz : ∀ j, raw2660step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw2660step2 = (fun i j => raw2660step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw2660step2 raw2660step1; decide +kernel
      have hl : raw2660step2Labels = raw2660step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2660step1 raw2660step1Labels permutation14 hz
    mixedMoment B raw2660step2 raw2660step2Labels = mixedMoment B raw2660step3 raw2660step3Labels := by
      have ha : raw2660step3 = (fun i j => raw2660step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2660step3 raw2660step2; decide +kernel
      have hl : raw2660step3Labels = raw2660step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2660step2 raw2660step2Labels permutation6 permutation5
    mixedMoment B raw2660step3 raw2660step3Labels = mixedMoment B raw2660step4 raw2660step4Labels := by
      have ha : raw2660step4 = raw2660step3 := by apply Matrix.ext; unfold raw2660step4 raw2660step3; decide +kernel
      have hl : raw2660step3Labels = labelEmbedding8 ∘ raw2660step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2660step3 raw2660step3Labels raw2660step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw2661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2661Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2661step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2661step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2661step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2661 raw2661Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw2661 raw2661Labels = mixedMoment B raw2661step0 raw2661step0Labels := by
      have hz : ∀ j, raw2661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2661step0 = (fun i j => raw2661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2661step0 raw2661; decide +kernel
      have hl : raw2661step0Labels = raw2661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2661 raw2661Labels permutation346 hz
    mixedMoment B raw2661step0 raw2661step0Labels = mixedMoment B raw2661step1 raw2661step1Labels := by
      have ha : raw2661step1 = (fun i j => raw2661step0 (permutation131 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2661step1 raw2661step0; decide +kernel
      have hl : raw2661step1Labels = raw2661step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2661step0 raw2661step0Labels permutation131 permutation5
    mixedMoment B raw2661step1 raw2661step1Labels = mixedMoment B raw2661step2 raw2661step2Labels := by
      have ha : raw2661step2 = raw2661step1 := by apply Matrix.ext; unfold raw2661step2 raw2661step1; decide +kernel
      have hl : raw2661step1Labels = labelEmbedding8 ∘ raw2661step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2661step1 raw2661step1Labels raw2661step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw2662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2662Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2662step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2662step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2662step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2662step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2662step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2662step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2662 raw2662Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw2662 raw2662Labels = mixedMoment B raw2662step0 raw2662step0Labels := by
      have hz : ∀ j, raw2662 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2662step0 = (fun i j => raw2662 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2662step0 raw2662; decide +kernel
      have hl : raw2662step0Labels = raw2662Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2662 raw2662Labels permutation265 hz
    mixedMoment B raw2662step0 raw2662step0Labels = mixedMoment B raw2662step1 raw2662step1Labels := by
      have ha : raw2662step1 = (fun i j => raw2662step0 (permutation131 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2662step1 raw2662step0; decide +kernel
      have hl : raw2662step1Labels = raw2662step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2662step0 raw2662step0Labels permutation131 permutation5
    mixedMoment B raw2662step1 raw2662step1Labels = mixedMoment B raw2662step2 raw2662step2Labels := by
      have ha : raw2662step2 = raw2662step1 := by apply Matrix.ext; unfold raw2662step2 raw2662step1; decide +kernel
      have hl : raw2662step1Labels = labelEmbedding8 ∘ raw2662step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2662step1 raw2662step1Labels raw2662step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw2663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2663step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2663step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2663step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2663 raw2663Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2663 raw2663Labels = mixedMoment B raw2663step0 raw2663step0Labels := by
      have hz : ∀ j, raw2663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2663step0 = (fun i j => raw2663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2663step0 raw2663; decide +kernel
      have hl : raw2663step0Labels = raw2663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2663 raw2663Labels permutation346 hz
    mixedMoment B raw2663step0 raw2663step0Labels = mixedMoment B raw2663step1 raw2663step1Labels := by
      have hz : ∀ j, raw2663step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2663step1 = (fun i j => raw2663step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2663step1 raw2663step0; decide +kernel
      have hl : raw2663step1Labels = raw2663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2663step0 raw2663step0Labels permutation56 hz
    mixedMoment B raw2663step1 raw2663step1Labels = mixedMoment B raw2663step2 raw2663step2Labels := by
      have ha : raw2663step2 = (fun i j => raw2663step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2663step2 raw2663step1; decide +kernel
      have hl : raw2663step2Labels = raw2663step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2663step1 raw2663step1Labels permutation27 permutation5
    mixedMoment B raw2663step2 raw2663step2Labels = mixedMoment B raw2663step3 raw2663step3Labels := by
      have ha : raw2663step3 = raw2663step2 := by apply Matrix.ext; unfold raw2663step3 raw2663step2; decide +kernel
      have hl : raw2663step2Labels = labelEmbedding8 ∘ raw2663step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2663step2 raw2663step2Labels raw2663step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw2664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2664Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2664step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2664step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2664step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2664step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2664step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2664step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2664step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2664 raw2664Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2664 raw2664Labels = mixedMoment B raw2664step0 raw2664step0Labels := by
      have hz : ∀ j, raw2664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2664step0 = (fun i j => raw2664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2664step0 raw2664; decide +kernel
      have hl : raw2664step0Labels = raw2664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2664 raw2664Labels permutation346 hz
    mixedMoment B raw2664step0 raw2664step0Labels = mixedMoment B raw2664step1 raw2664step1Labels := by
      have hz : ∀ j, raw2664step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2664step1 = (fun i j => raw2664step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2664step1 raw2664step0; decide +kernel
      have hl : raw2664step1Labels = raw2664step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2664step0 raw2664step0Labels permutation56 hz
    mixedMoment B raw2664step1 raw2664step1Labels = mixedMoment B raw2664step2 raw2664step2Labels := by
      have ha : raw2664step2 = (fun i j => raw2664step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2664step2 raw2664step1; decide +kernel
      have hl : raw2664step2Labels = raw2664step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2664step1 raw2664step1Labels permutation26 permutation5
    mixedMoment B raw2664step2 raw2664step2Labels = mixedMoment B raw2664step3 raw2664step3Labels := by
      have ha : raw2664step3 = raw2664step2 := by apply Matrix.ext; unfold raw2664step3 raw2664step2; decide +kernel
      have hl : raw2664step2Labels = labelEmbedding8 ∘ raw2664step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2664step2 raw2664step2Labels raw2664step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw2665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2665Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2665step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2665step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2665step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2665step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2665step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2665step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2665step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw2665step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2665step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2665 raw2665Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw2665 raw2665Labels = mixedMoment B raw2665step0 raw2665step0Labels := by
      have hz : ∀ j, raw2665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2665step0 = (fun i j => raw2665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2665step0 raw2665; decide +kernel
      have hl : raw2665step0Labels = raw2665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2665 raw2665Labels permutation346 hz
    mixedMoment B raw2665step0 raw2665step0Labels = mixedMoment B raw2665step1 raw2665step1Labels := by
      have hz : ∀ j, raw2665step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2665step1 = (fun i j => raw2665step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2665step1 raw2665step0; decide +kernel
      have hl : raw2665step1Labels = raw2665step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2665step0 raw2665step0Labels permutation56 hz
    mixedMoment B raw2665step1 raw2665step1Labels = mixedMoment B raw2665step2 raw2665step2Labels := by
      have ha : raw2665step2 = (fun i j => raw2665step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2665step2 raw2665step1; decide +kernel
      have hl : raw2665step2Labels = raw2665step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2665step1 raw2665step1Labels permutation12 permutation6
    mixedMoment B raw2665step2 raw2665step2Labels = mixedMoment B raw2665step3 raw2665step3Labels := by
      have ha : raw2665step3 = -raw2665step2 := by apply Matrix.ext; change ∀ i j, raw2665step3 i j = -(raw2665step2 i j); unfold raw2665step3 raw2665step2; decide +kernel
      have hl : raw2665step3Labels = raw2665step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2665step3 raw2665step3Labels = mixedMoment B raw2665step4 raw2665step4Labels := by
      have ha : raw2665step4 = raw2665step3 := by apply Matrix.ext; unfold raw2665step4 raw2665step3; decide +kernel
      have hl : raw2665step3Labels = labelEmbedding9 ∘ raw2665step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2665step3 raw2665step3Labels raw2665step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw2666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2666Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2666step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2666step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2666step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2666step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2666 raw2666Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2666 raw2666Labels = mixedMoment B raw2666step0 raw2666step0Labels := by
      have hz : ∀ j, raw2666 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2666step0 = (fun i j => raw2666 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2666step0 raw2666; decide +kernel
      have hl : raw2666step0Labels = raw2666Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2666 raw2666Labels permutation346 hz
    mixedMoment B raw2666step0 raw2666step0Labels = mixedMoment B raw2666step1 raw2666step1Labels := by
      have ha : raw2666step1 = (fun i j => raw2666step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2666step1 raw2666step0; decide +kernel
      have hl : raw2666step1Labels = raw2666step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2666step0 raw2666step0Labels permutation40 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw2667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2667Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2667step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2667step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2667step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2667step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2667 raw2667Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw2667 raw2667Labels = mixedMoment B raw2667step0 raw2667step0Labels := by
      have ha : raw2667step0 = (fun i j => raw2667 (permutation616 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2667step0 raw2667; decide +kernel
      have hl : raw2667step0Labels = raw2667Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2667 raw2667Labels permutation616 permutation3
    mixedMoment B raw2667step0 raw2667step0Labels = mixedMoment B raw2667step1 raw2667step1Labels := by
      have ha : raw2667step1 = -raw2667step0 := by apply Matrix.ext; change ∀ i j, raw2667step1 i j = -(raw2667step0 i j); unfold raw2667step1 raw2667step0; decide +kernel
      have hl : raw2667step1Labels = raw2667step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2667step1 raw2667step1Labels = mixedMoment B raw2667step2 raw2667step2Labels := by
      have ha : raw2667step2 = raw2667step1 := by apply Matrix.ext; unfold raw2667step2 raw2667step1; decide +kernel
      have hl : raw2667step1Labels = labelEmbedding6 ∘ raw2667step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2667step1 raw2667step1Labels raw2667step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw2668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2668Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2668step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2668step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2668step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2668step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2668step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2668step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2668 raw2668Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2668 raw2668Labels = mixedMoment B raw2668step0 raw2668step0Labels := by
      have hz : ∀ j, raw2668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2668step0 = (fun i j => raw2668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2668step0 raw2668; decide +kernel
      have hl : raw2668step0Labels = raw2668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2668 raw2668Labels permutation346 hz
    mixedMoment B raw2668step0 raw2668step0Labels = mixedMoment B raw2668step1 raw2668step1Labels := by
      have ha : raw2668step1 = (fun i j => raw2668step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2668step1 raw2668step0; decide +kernel
      have hl : raw2668step1Labels = raw2668step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2668step0 raw2668step0Labels permutation139 permutation3
    mixedMoment B raw2668step1 raw2668step1Labels = mixedMoment B raw2668step2 raw2668step2Labels := by
      have ha : raw2668step2 = -raw2668step1 := by apply Matrix.ext; change ∀ i j, raw2668step2 i j = -(raw2668step1 i j); unfold raw2668step2 raw2668step1; decide +kernel
      have hl : raw2668step2Labels = raw2668step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2668step2 raw2668step2Labels = mixedMoment B raw2668step3 raw2668step3Labels := by
      have ha : raw2668step3 = raw2668step2 := by apply Matrix.ext; unfold raw2668step3 raw2668step2; decide +kernel
      have hl : raw2668step2Labels = labelEmbedding6 ∘ raw2668step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2668step2 raw2668step2Labels raw2668step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw2669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2669Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2669step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2669step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2669step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2669step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2669step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2669step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2669step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2669step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2669 raw2669Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2669 raw2669Labels = mixedMoment B raw2669step0 raw2669step0Labels := by
      have hz : ∀ j, raw2669 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2669step0 = (fun i j => raw2669 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2669step0 raw2669; decide +kernel
      have hl : raw2669step0Labels = raw2669Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2669 raw2669Labels permutation346 hz
    mixedMoment B raw2669step0 raw2669step0Labels = mixedMoment B raw2669step1 raw2669step1Labels := by
      have ha : raw2669step1 = (fun i j => raw2669step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2669step1 raw2669step0; decide +kernel
      have hl : raw2669step1Labels = raw2669step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2669step0 raw2669step0Labels permutation137 permutation3
    mixedMoment B raw2669step1 raw2669step1Labels = mixedMoment B raw2669step2 raw2669step2Labels := by
      have ha : raw2669step2 = -raw2669step1 := by apply Matrix.ext; change ∀ i j, raw2669step2 i j = -(raw2669step1 i j); unfold raw2669step2 raw2669step1; decide +kernel
      have hl : raw2669step2Labels = raw2669step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2669step2 raw2669step2Labels = mixedMoment B raw2669step3 raw2669step3Labels := by
      have ha : raw2669step3 = raw2669step2 := by apply Matrix.ext; unfold raw2669step3 raw2669step2; decide +kernel
      have hl : raw2669step2Labels = labelEmbedding6 ∘ raw2669step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2669step2 raw2669step2Labels raw2669step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw2670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2670Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2670step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2670step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2670 raw2670Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw2670 raw2670Labels = mixedMoment B raw2670step0 raw2670step0Labels := by
      have hz : ∀ j, raw2670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2670step0 = (fun i j => raw2670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2670step0 raw2670; decide +kernel
      have hl : raw2670step0Labels = raw2670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2670 raw2670Labels permutation346 hz
    mixedMoment B raw2670step0 raw2670step0Labels = mixedMoment B raw2670step1 raw2670step1Labels := by
      have ha : raw2670step1 = (fun i j => raw2670step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2670step1 raw2670step0; decide +kernel
      have hl : raw2670step1Labels = raw2670step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2670step0 raw2670step0Labels permutation40 permutation2
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw2671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw2671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2671 raw2671Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw2671 raw2671Labels = mixedMoment B raw2671step0 raw2671step0Labels := by
      have hz : ∀ j, raw2671 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2671step0 = (fun i j => raw2671 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2671step0 raw2671; decide +kernel
      have hl : raw2671step0Labels = raw2671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2671 raw2671Labels permutation265 hz
    mixedMoment B raw2671step0 raw2671step0Labels = mixedMoment B raw2671step1 raw2671step1Labels := by
      have ha : raw2671step1 = (fun i j => raw2671step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2671step1 raw2671step0; decide +kernel
      have hl : raw2671step1Labels = raw2671step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2671step0 raw2671step0Labels permutation40 permutation2
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw2672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2672step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2672step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2672step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2672step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2672 raw2672Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw2672 raw2672Labels = mixedMoment B raw2672step0 raw2672step0Labels := by
      have ha : raw2672step0 = (fun i j => raw2672 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2672step0 raw2672; decide +kernel
      have hl : raw2672step0Labels = raw2672Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2672 raw2672Labels permutation640 permutation3
    mixedMoment B raw2672step0 raw2672step0Labels = mixedMoment B raw2672step1 raw2672step1Labels := by
      have ha : raw2672step1 = -raw2672step0 := by apply Matrix.ext; change ∀ i j, raw2672step1 i j = -(raw2672step0 i j); unfold raw2672step1 raw2672step0; decide +kernel
      have hl : raw2672step1Labels = raw2672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2672step1 raw2672step1Labels = mixedMoment B raw2672step2 raw2672step2Labels := by
      have ha : raw2672step2 = raw2672step1 := by apply Matrix.ext; unfold raw2672step2 raw2672step1; decide +kernel
      have hl : raw2672step1Labels = labelEmbedding6 ∘ raw2672step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2672step1 raw2672step1Labels raw2672step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw2673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2673step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2673step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2673step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2673step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2673step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2673 raw2673Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2673 raw2673Labels = mixedMoment B raw2673step0 raw2673step0Labels := by
      have hz : ∀ j, raw2673 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2673step0 = (fun i j => raw2673 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2673step0 raw2673; decide +kernel
      have hl : raw2673step0Labels = raw2673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2673 raw2673Labels permutation265 hz
    mixedMoment B raw2673step0 raw2673step0Labels = mixedMoment B raw2673step1 raw2673step1Labels := by
      have ha : raw2673step1 = (fun i j => raw2673step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2673step1 raw2673step0; decide +kernel
      have hl : raw2673step1Labels = raw2673step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2673step0 raw2673step0Labels permutation139 permutation3
    mixedMoment B raw2673step1 raw2673step1Labels = mixedMoment B raw2673step2 raw2673step2Labels := by
      have ha : raw2673step2 = -raw2673step1 := by apply Matrix.ext; change ∀ i j, raw2673step2 i j = -(raw2673step1 i j); unfold raw2673step2 raw2673step1; decide +kernel
      have hl : raw2673step2Labels = raw2673step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2673step2 raw2673step2Labels = mixedMoment B raw2673step3 raw2673step3Labels := by
      have ha : raw2673step3 = raw2673step2 := by apply Matrix.ext; unfold raw2673step3 raw2673step2; decide +kernel
      have hl : raw2673step2Labels = labelEmbedding6 ∘ raw2673step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2673step2 raw2673step2Labels raw2673step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw2674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2674step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2674step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2674step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2674step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2674 raw2674Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2674 raw2674Labels = mixedMoment B raw2674step0 raw2674step0Labels := by
      have hz : ∀ j, raw2674 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2674step0 = (fun i j => raw2674 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2674step0 raw2674; decide +kernel
      have hl : raw2674step0Labels = raw2674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2674 raw2674Labels permutation265 hz
    mixedMoment B raw2674step0 raw2674step0Labels = mixedMoment B raw2674step1 raw2674step1Labels := by
      have ha : raw2674step1 = (fun i j => raw2674step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2674step1 raw2674step0; decide +kernel
      have hl : raw2674step1Labels = raw2674step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2674step0 raw2674step0Labels permutation137 permutation3
    mixedMoment B raw2674step1 raw2674step1Labels = mixedMoment B raw2674step2 raw2674step2Labels := by
      have ha : raw2674step2 = -raw2674step1 := by apply Matrix.ext; change ∀ i j, raw2674step2 i j = -(raw2674step1 i j); unfold raw2674step2 raw2674step1; decide +kernel
      have hl : raw2674step2Labels = raw2674step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2674step2 raw2674step2Labels = mixedMoment B raw2674step3 raw2674step3Labels := by
      have ha : raw2674step3 = raw2674step2 := by apply Matrix.ext; unfold raw2674step3 raw2674step2; decide +kernel
      have hl : raw2674step2Labels = labelEmbedding6 ∘ raw2674step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2674step2 raw2674step2Labels raw2674step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw2675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw2675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2675 raw2675Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw2675 raw2675Labels = mixedMoment B raw2675step0 raw2675step0Labels := by
      have hz : ∀ j, raw2675 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2675step0 = (fun i j => raw2675 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2675step0 raw2675; decide +kernel
      have hl : raw2675step0Labels = raw2675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2675 raw2675Labels permutation265 hz
    mixedMoment B raw2675step0 raw2675step0Labels = mixedMoment B raw2675step1 raw2675step1Labels := by
      have ha : raw2675step1 = (fun i j => raw2675step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2675step1 raw2675step0; decide +kernel
      have hl : raw2675step1Labels = raw2675step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2675step0 raw2675step0Labels permutation40 permutation2
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw2676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2676step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2676step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2676step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2676 raw2676Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2676 raw2676Labels = mixedMoment B raw2676step0 raw2676step0Labels := by
      have hz : ∀ j, raw2676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2676step0 = (fun i j => raw2676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2676step0 raw2676; decide +kernel
      have hl : raw2676step0Labels = raw2676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2676 raw2676Labels permutation346 hz
    mixedMoment B raw2676step0 raw2676step0Labels = mixedMoment B raw2676step1 raw2676step1Labels := by
      have hz : ∀ j, raw2676step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2676step1 = (fun i j => raw2676step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2676step1 raw2676step0; decide +kernel
      have hl : raw2676step1Labels = raw2676step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2676step0 raw2676step0Labels permutation56 hz
    mixedMoment B raw2676step1 raw2676step1Labels = mixedMoment B raw2676step2 raw2676step2Labels := by
      have ha : raw2676step2 = (fun i j => raw2676step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2676step2 raw2676step1; decide +kernel
      have hl : raw2676step2Labels = raw2676step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2676step1 raw2676step1Labels permutation10 permutation2
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw2677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2677step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2677step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2677 raw2677Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw2677 raw2677Labels = mixedMoment B raw2677step0 raw2677step0Labels := by
      have hz : ∀ j, raw2677 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2677step0 = (fun i j => raw2677 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2677step0 raw2677; decide +kernel
      have hl : raw2677step0Labels = raw2677Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2677 raw2677Labels permutation346 hz
    mixedMoment B raw2677step0 raw2677step0Labels = mixedMoment B raw2677step1 raw2677step1Labels := by
      have ha : raw2677step1 = (fun i j => raw2677step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2677step1 raw2677step0; decide +kernel
      have hl : raw2677step1Labels = raw2677step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2677step0 raw2677step0Labels permutation34 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw2678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2678step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2678 raw2678Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw2678 raw2678Labels = mixedMoment B raw2678step0 raw2678step0Labels := by
      have hz : ∀ j, raw2678 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2678step0 = (fun i j => raw2678 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2678step0 raw2678; decide +kernel
      have hl : raw2678step0Labels = raw2678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2678 raw2678Labels permutation265 hz
    mixedMoment B raw2678step0 raw2678step0Labels = mixedMoment B raw2678step1 raw2678step1Labels := by
      have ha : raw2678step1 = (fun i j => raw2678step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2678step1 raw2678step0; decide +kernel
      have hl : raw2678step1Labels = raw2678step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2678step0 raw2678step0Labels permutation34 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw2679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2679step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0]]
def raw2679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2679step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2679step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2679step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2679step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2679step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2679step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2679 raw2679Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2679 raw2679Labels = mixedMoment B raw2679step0 raw2679step0Labels := by
      have hz : ∀ j, raw2679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2679step0 = (fun i j => raw2679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2679step0 raw2679; decide +kernel
      have hl : raw2679step0Labels = raw2679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2679 raw2679Labels permutation346 hz
    mixedMoment B raw2679step0 raw2679step0Labels = mixedMoment B raw2679step1 raw2679step1Labels := by
      have hz : ∀ j, raw2679step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2679step1 = (fun i j => raw2679step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2679step1 raw2679step0; decide +kernel
      have hl : raw2679step1Labels = raw2679step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2679step0 raw2679step0Labels permutation56 hz
    mixedMoment B raw2679step1 raw2679step1Labels = mixedMoment B raw2679step2 raw2679step2Labels := by
      have ha : raw2679step2 = (fun i j => raw2679step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2679step2 raw2679step1; decide +kernel
      have hl : raw2679step2Labels = raw2679step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2679step1 raw2679step1Labels permutation29 permutation3
    mixedMoment B raw2679step2 raw2679step2Labels = mixedMoment B raw2679step3 raw2679step3Labels := by
      have ha : raw2679step3 = -raw2679step2 := by apply Matrix.ext; change ∀ i j, raw2679step3 i j = -(raw2679step2 i j); unfold raw2679step3 raw2679step2; decide +kernel
      have hl : raw2679step3Labels = raw2679step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2679step3 raw2679step3Labels = mixedMoment B raw2679step4 raw2679step4Labels := by
      have ha : raw2679step4 = raw2679step3 := by apply Matrix.ext; unfold raw2679step4 raw2679step3; decide +kernel
      have hl : raw2679step3Labels = labelEmbedding6 ∘ raw2679step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2679step3 raw2679step3Labels raw2679step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2680step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw2680step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2680step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2680step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2680 raw2680Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw2680 raw2680Labels = mixedMoment B raw2680step0 raw2680step0Labels := by
      have hz : ∀ j, raw2680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2680step0 = (fun i j => raw2680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2680step0 raw2680; decide +kernel
      have hl : raw2680step0Labels = raw2680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2680 raw2680Labels permutation346 hz
    mixedMoment B raw2680step0 raw2680step0Labels = mixedMoment B raw2680step1 raw2680step1Labels := by
      have hz : ∀ j, raw2680step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2680step1 = (fun i j => raw2680step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2680step1 raw2680step0; decide +kernel
      have hl : raw2680step1Labels = raw2680step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2680step0 raw2680step0Labels permutation56 hz
    mixedMoment B raw2680step1 raw2680step1Labels = mixedMoment B raw2680step2 raw2680step2Labels := by
      have ha : raw2680step2 = (fun i j => raw2680step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2680step2 raw2680step1; decide +kernel
      have hl : raw2680step2Labels = raw2680step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2680step1 raw2680step1Labels permutation11 permutation2
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw2681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2681step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2681step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2681step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2681 raw2681Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw2681 raw2681Labels = mixedMoment B raw2681step0 raw2681step0Labels := by
      have hz : ∀ j, raw2681 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2681step0 = (fun i j => raw2681 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2681step0 raw2681; decide +kernel
      have hl : raw2681step0Labels = raw2681Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2681 raw2681Labels permutation346 hz
    mixedMoment B raw2681step0 raw2681step0Labels = mixedMoment B raw2681step1 raw2681step1Labels := by
      have hz : ∀ j, raw2681step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2681step1 = (fun i j => raw2681step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2681step1 raw2681step0; decide +kernel
      have hl : raw2681step1Labels = raw2681step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2681step0 raw2681step0Labels permutation56 hz
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw2682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2682step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2682 raw2682Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw2682 raw2682Labels = mixedMoment B raw2682step0 raw2682step0Labels := by
      have hz : ∀ j, raw2682 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2682step0 = (fun i j => raw2682 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2682step0 raw2682; decide +kernel
      have hl : raw2682step0Labels = raw2682Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2682 raw2682Labels permutation346 hz
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw2683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2683step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2683step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2683 raw2683Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw2683 raw2683Labels = mixedMoment B raw2683step0 raw2683step0Labels := by
      have hz : ∀ j, raw2683 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw2683step0 = (fun i j => raw2683 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw2683step0 raw2683; decide +kernel
      have hl : raw2683step0Labels = raw2683Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2683 raw2683Labels permutation265 hz
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw2684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2684step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2684step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2684step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2684step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw2684step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2684step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2684step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2684step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2684step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2684 raw2684Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2684 raw2684Labels = mixedMoment B raw2684step0 raw2684step0Labels := by
      have hz : ∀ j, raw2684 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2684step0 = (fun i j => raw2684 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2684step0 raw2684; decide +kernel
      have hl : raw2684step0Labels = raw2684Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2684 raw2684Labels permutation346 hz
    mixedMoment B raw2684step0 raw2684step0Labels = mixedMoment B raw2684step1 raw2684step1Labels := by
      have hz : ∀ j, raw2684step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2684step1 = (fun i j => raw2684step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2684step1 raw2684step0; decide +kernel
      have hl : raw2684step1Labels = raw2684step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2684step0 raw2684step0Labels permutation56 hz
    mixedMoment B raw2684step1 raw2684step1Labels = mixedMoment B raw2684step2 raw2684step2Labels := by
      have ha : raw2684step2 = (fun i j => raw2684step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2684step2 raw2684step1; decide +kernel
      have hl : raw2684step2Labels = raw2684step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2684step1 raw2684step1Labels permutation31 permutation3
    mixedMoment B raw2684step2 raw2684step2Labels = mixedMoment B raw2684step3 raw2684step3Labels := by
      have ha : raw2684step3 = -raw2684step2 := by apply Matrix.ext; change ∀ i j, raw2684step3 i j = -(raw2684step2 i j); unfold raw2684step3 raw2684step2; decide +kernel
      have hl : raw2684step3Labels = raw2684step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2684step3 raw2684step3Labels = mixedMoment B raw2684step4 raw2684step4Labels := by
      have ha : raw2684step4 = raw2684step3 := by apply Matrix.ext; unfold raw2684step4 raw2684step3; decide +kernel
      have hl : raw2684step3Labels = labelEmbedding6 ∘ raw2684step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2684step3 raw2684step3Labels raw2684step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2685step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2685step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw2685step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2685step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2685step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2685 raw2685Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw2685 raw2685Labels = mixedMoment B raw2685step0 raw2685step0Labels := by
      have hz : ∀ j, raw2685 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2685step0 = (fun i j => raw2685 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2685step0 raw2685; decide +kernel
      have hl : raw2685step0Labels = raw2685Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2685 raw2685Labels permutation346 hz
    mixedMoment B raw2685step0 raw2685step0Labels = mixedMoment B raw2685step1 raw2685step1Labels := by
      have hz : ∀ j, raw2685step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2685step1 = (fun i j => raw2685step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2685step1 raw2685step0; decide +kernel
      have hl : raw2685step1Labels = raw2685step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2685step0 raw2685step0Labels permutation56 hz
    mixedMoment B raw2685step1 raw2685step1Labels = mixedMoment B raw2685step2 raw2685step2Labels := by
      have ha : raw2685step2 = (fun i j => raw2685step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2685step2 raw2685step1; decide +kernel
      have hl : raw2685step2Labels = raw2685step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2685step1 raw2685step1Labels permutation9 permutation2
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw2686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2686step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2686step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2686step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw2686step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2686step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw2686step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2686step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw2686step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2686 raw2686Labels = mixedMoment B node4890 node4890Labels := by
  calc
    mixedMoment B raw2686 raw2686Labels = mixedMoment B raw2686step0 raw2686step0Labels := by
      have hz : ∀ j, raw2686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2686step0 = (fun i j => raw2686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2686step0 raw2686; decide +kernel
      have hl : raw2686step0Labels = raw2686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2686 raw2686Labels permutation346 hz
    mixedMoment B raw2686step0 raw2686step0Labels = mixedMoment B raw2686step1 raw2686step1Labels := by
      have hz : ∀ j, raw2686step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw2686step1 = (fun i j => raw2686step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw2686step1 raw2686step0; decide +kernel
      have hl : raw2686step1Labels = raw2686step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2686step0 raw2686step0Labels permutation56 hz
    mixedMoment B raw2686step1 raw2686step1Labels = mixedMoment B raw2686step2 raw2686step2Labels := by
      have ha : raw2686step2 = (fun i j => raw2686step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2686step2 raw2686step1; decide +kernel
      have hl : raw2686step2Labels = raw2686step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2686step1 raw2686step1Labels permutation29 permutation3
    mixedMoment B raw2686step2 raw2686step2Labels = mixedMoment B raw2686step3 raw2686step3Labels := by
      have ha : raw2686step3 = -raw2686step2 := by apply Matrix.ext; change ∀ i j, raw2686step3 i j = -(raw2686step2 i j); unfold raw2686step3 raw2686step2; decide +kernel
      have hl : raw2686step3Labels = raw2686step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2686step3 raw2686step3Labels = mixedMoment B raw2686step4 raw2686step4Labels := by
      have ha : raw2686step4 = raw2686step3 := by apply Matrix.ext; unfold raw2686step4 raw2686step3; decide +kernel
      have hl : raw2686step3Labels = labelEmbedding6 ∘ raw2686step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2686step3 raw2686step3Labels raw2686step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4890 node4890Labels := by rfl

def raw2687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw2687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw2687step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2687step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2687step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw2687step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2687step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2687 raw2687Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw2687 raw2687Labels = mixedMoment B raw2687step0 raw2687step0Labels := by
      have hz : ∀ j, raw2687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw2687step0 = (fun i j => raw2687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw2687step0 raw2687; decide +kernel
      have hl : raw2687step0Labels = raw2687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw2687 raw2687Labels permutation346 hz
    mixedMoment B raw2687step0 raw2687step0Labels = mixedMoment B raw2687step1 raw2687step1Labels := by
      have ha : raw2687step1 = (fun i j => raw2687step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2687step1 raw2687step0; decide +kernel
      have hl : raw2687step1Labels = raw2687step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2687step0 raw2687step0Labels permutation145 permutation3
    mixedMoment B raw2687step1 raw2687step1Labels = mixedMoment B raw2687step2 raw2687step2Labels := by
      have ha : raw2687step2 = -raw2687step1 := by apply Matrix.ext; change ∀ i j, raw2687step2 i j = -(raw2687step1 i j); unfold raw2687step2 raw2687step1; decide +kernel
      have hl : raw2687step2Labels = raw2687step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2687step2 raw2687step2Labels = mixedMoment B raw2687step3 raw2687step3Labels := by
      have ha : raw2687step3 = raw2687step2 := by apply Matrix.ext; unfold raw2687step3 raw2687step2; decide +kernel
      have hl : raw2687step2Labels = labelEmbedding6 ∘ raw2687step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2687step2 raw2687step2Labels raw2687step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
