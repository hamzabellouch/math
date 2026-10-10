import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw2432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw2432Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2432step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw2432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2432 raw2432Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw2432 raw2432Labels = mixedMoment B raw2432step0 raw2432step0Labels := by
      have ha : raw2432step0 = (fun i j => raw2432 (permutation686 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2432step0 raw2432; decide +kernel
      have hl : raw2432step0Labels = raw2432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2432 raw2432Labels permutation686 permutation6
    mixedMoment B raw2432step0 raw2432step0Labels = mixedMoment B raw2432step1 raw2432step1Labels := by
      have ha : raw2432step1 = raw2432step0 := by apply Matrix.ext; unfold raw2432step1 raw2432step0; decide +kernel
      have hl : raw2432step0Labels = labelEmbedding1 ∘ raw2432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2432step0 raw2432step0Labels raw2432step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw2433 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2433step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2433 raw2433Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw2433 raw2433Labels = mixedMoment B raw2433step0 raw2433step0Labels := by
      have ha : raw2433step0 = (fun i j => raw2433 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2433step0 raw2433; decide +kernel
      have hl : raw2433step0Labels = raw2433Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2433 raw2433Labels permutation152 permutation4
    mixedMoment B raw2433step0 raw2433step0Labels = mixedMoment B raw2433step1 raw2433step1Labels := by
      have ha : raw2433step1 = raw2433step0 := by apply Matrix.ext; unfold raw2433step1 raw2433step0; decide +kernel
      have hl : raw2433step0Labels = labelEmbedding7 ∘ raw2433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2433step0 raw2433step0Labels raw2433step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw2434 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2434 raw2434Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw2434 raw2434Labels = mixedMoment B raw2434step0 raw2434step0Labels := by
      have ha : raw2434step0 = (fun i j => raw2434 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2434step0 raw2434; decide +kernel
      have hl : raw2434step0Labels = raw2434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2434 raw2434Labels permutation152 permutation4
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw2435 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2435Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2435step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2435step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2435 raw2435Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw2435 raw2435Labels = mixedMoment B raw2435step0 raw2435step0Labels := by
      have ha : raw2435step0 = (fun i j => raw2435 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2435step0 raw2435; decide +kernel
      have hl : raw2435step0Labels = raw2435Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2435 raw2435Labels permutation176 permutation6
    mixedMoment B raw2435step0 raw2435step0Labels = mixedMoment B raw2435step1 raw2435step1Labels := by
      have ha : raw2435step1 = -raw2435step0 := by apply Matrix.ext; change ∀ i j, raw2435step1 i j = -(raw2435step0 i j); unfold raw2435step1 raw2435step0; decide +kernel
      have hl : raw2435step1Labels = raw2435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2435step1 raw2435step1Labels = mixedMoment B raw2435step2 raw2435step2Labels := by
      have ha : raw2435step2 = raw2435step1 := by apply Matrix.ext; unfold raw2435step2 raw2435step1; decide +kernel
      have hl : raw2435step1Labels = labelEmbedding1 ∘ raw2435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2435step1 raw2435step1Labels raw2435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

def raw2436 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2436step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2436 raw2436Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw2436 raw2436Labels = mixedMoment B raw2436step0 raw2436step0Labels := by
      have ha : raw2436step0 = (fun i j => raw2436 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2436step0 raw2436; decide +kernel
      have hl : raw2436step0Labels = raw2436Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2436 raw2436Labels permutation152 permutation4
    mixedMoment B raw2436step0 raw2436step0Labels = mixedMoment B raw2436step1 raw2436step1Labels := by
      have ha : raw2436step1 = raw2436step0 := by apply Matrix.ext; unfold raw2436step1 raw2436step0; decide +kernel
      have hl : raw2436step0Labels = labelEmbedding7 ∘ raw2436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2436step0 raw2436step0Labels raw2436step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw2437 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2437 raw2437Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw2437 raw2437Labels = mixedMoment B raw2437step0 raw2437step0Labels := by
      have ha : raw2437step0 = (fun i j => raw2437 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2437step0 raw2437; decide +kernel
      have hl : raw2437step0Labels = raw2437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2437 raw2437Labels permutation152 permutation4
    _ = mixedMoment B node3731 node3731Labels := by rfl

def raw2438 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2438Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2438step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2438step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2438step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2438step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2438 raw2438Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw2438 raw2438Labels = mixedMoment B raw2438step0 raw2438step0Labels := by
      have ha : raw2438step0 = (fun i j => raw2438 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2438step0 raw2438; decide +kernel
      have hl : raw2438step0Labels = raw2438Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2438 raw2438Labels permutation176 permutation6
    mixedMoment B raw2438step0 raw2438step0Labels = mixedMoment B raw2438step1 raw2438step1Labels := by
      have ha : raw2438step1 = -raw2438step0 := by apply Matrix.ext; change ∀ i j, raw2438step1 i j = -(raw2438step0 i j); unfold raw2438step1 raw2438step0; decide +kernel
      have hl : raw2438step1Labels = raw2438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2438step1 raw2438step1Labels = mixedMoment B raw2438step2 raw2438step2Labels := by
      have ha : raw2438step2 = raw2438step1 := by apply Matrix.ext; unfold raw2438step2 raw2438step1; decide +kernel
      have hl : raw2438step1Labels = labelEmbedding1 ∘ raw2438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2438step1 raw2438step1Labels raw2438step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3867 node3867Labels := by rfl

def raw2439 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2439step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2439 raw2439Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw2439 raw2439Labels = mixedMoment B raw2439step0 raw2439step0Labels := by
      have ha : raw2439step0 = (fun i j => raw2439 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2439step0 raw2439; decide +kernel
      have hl : raw2439step0Labels = raw2439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2439 raw2439Labels permutation32 permutation4
    mixedMoment B raw2439step0 raw2439step0Labels = mixedMoment B raw2439step1 raw2439step1Labels := by
      have ha : raw2439step1 = raw2439step0 := by apply Matrix.ext; unfold raw2439step1 raw2439step0; decide +kernel
      have hl : raw2439step0Labels = labelEmbedding7 ∘ raw2439step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2439step0 raw2439step0Labels raw2439step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw2440 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2440 raw2440Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw2440 raw2440Labels = mixedMoment B raw2440step0 raw2440step0Labels := by
      have ha : raw2440step0 = (fun i j => raw2440 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2440step0 raw2440; decide +kernel
      have hl : raw2440step0Labels = raw2440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2440 raw2440Labels permutation32 permutation4
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw2441 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2441Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw2441step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw2441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2441 raw2441Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw2441 raw2441Labels = mixedMoment B raw2441step0 raw2441step0Labels := by
      have ha : raw2441step0 = (fun i j => raw2441 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2441step0 raw2441; decide +kernel
      have hl : raw2441step0Labels = raw2441Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2441 raw2441Labels permutation149 permutation6
    mixedMoment B raw2441step0 raw2441step0Labels = mixedMoment B raw2441step1 raw2441step1Labels := by
      have ha : raw2441step1 = raw2441step0 := by apply Matrix.ext; unfold raw2441step1 raw2441step0; decide +kernel
      have hl : raw2441step0Labels = labelEmbedding1 ∘ raw2441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2441step0 raw2441step0Labels raw2441step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw2442 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2442step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2442 raw2442Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw2442 raw2442Labels = mixedMoment B raw2442step0 raw2442step0Labels := by
      have ha : raw2442step0 = (fun i j => raw2442 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2442step0 raw2442; decide +kernel
      have hl : raw2442step0Labels = raw2442Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2442 raw2442Labels permutation152 permutation4
    mixedMoment B raw2442step0 raw2442step0Labels = mixedMoment B raw2442step1 raw2442step1Labels := by
      have ha : raw2442step1 = raw2442step0 := by apply Matrix.ext; unfold raw2442step1 raw2442step0; decide +kernel
      have hl : raw2442step0Labels = labelEmbedding7 ∘ raw2442step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2442step0 raw2442step0Labels raw2442step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5386 node5386Labels := by rfl

def raw2443 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2443 raw2443Labels = mixedMoment B node3735 node3735Labels := by
  calc
    mixedMoment B raw2443 raw2443Labels = mixedMoment B raw2443step0 raw2443step0Labels := by
      have ha : raw2443step0 = (fun i j => raw2443 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2443step0 raw2443; decide +kernel
      have hl : raw2443step0Labels = raw2443Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2443 raw2443Labels permutation152 permutation4
    _ = mixedMoment B node3735 node3735Labels := by rfl

def raw2444 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw2444Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2444step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2444step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2444 raw2444Labels = mixedMoment B node3890 node3890Labels := by
  calc
    mixedMoment B raw2444 raw2444Labels = mixedMoment B raw2444step0 raw2444step0Labels := by
      have ha : raw2444step0 = (fun i j => raw2444 (permutation281 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2444step0 raw2444; decide +kernel
      have hl : raw2444step0Labels = raw2444Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2444 raw2444Labels permutation281 permutation3
    mixedMoment B raw2444step0 raw2444step0Labels = mixedMoment B raw2444step1 raw2444step1Labels := by
      have ha : raw2444step1 = -raw2444step0 := by apply Matrix.ext; change ∀ i j, raw2444step1 i j = -(raw2444step0 i j); unfold raw2444step1 raw2444step0; decide +kernel
      have hl : raw2444step1Labels = raw2444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2444step1 raw2444step1Labels = mixedMoment B raw2444step2 raw2444step2Labels := by
      have ha : raw2444step2 = raw2444step1 := by apply Matrix.ext; unfold raw2444step2 raw2444step1; decide +kernel
      have hl : raw2444step1Labels = labelEmbedding1 ∘ raw2444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2444step1 raw2444step1Labels raw2444step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3890 node3890Labels := by rfl

def raw2445 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2445step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2445step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2445 raw2445Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw2445 raw2445Labels = mixedMoment B raw2445step0 raw2445step0Labels := by
      have ha : raw2445step0 = (fun i j => raw2445 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2445step0 raw2445; decide +kernel
      have hl : raw2445step0Labels = raw2445Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2445 raw2445Labels permutation32 permutation4
    mixedMoment B raw2445step0 raw2445step0Labels = mixedMoment B raw2445step1 raw2445step1Labels := by
      have ha : raw2445step1 = raw2445step0 := by apply Matrix.ext; unfold raw2445step1 raw2445step0; decide +kernel
      have hl : raw2445step0Labels = labelEmbedding7 ∘ raw2445step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2445step0 raw2445step0Labels raw2445step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw2446 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2446 raw2446Labels = mixedMoment B node3736 node3736Labels := by
  calc
    mixedMoment B raw2446 raw2446Labels = mixedMoment B raw2446step0 raw2446step0Labels := by
      have ha : raw2446step0 = (fun i j => raw2446 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2446step0 raw2446; decide +kernel
      have hl : raw2446step0Labels = raw2446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2446 raw2446Labels permutation32 permutation4
    _ = mixedMoment B node3736 node3736Labels := by rfl

def raw2447 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2447Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw2447step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2447 raw2447Labels = mixedMoment B node3891 node3891Labels := by
  calc
    mixedMoment B raw2447 raw2447Labels = mixedMoment B raw2447step0 raw2447step0Labels := by
      have ha : raw2447step0 = (fun i j => raw2447 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2447step0 raw2447; decide +kernel
      have hl : raw2447step0Labels = raw2447Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2447 raw2447Labels permutation32 permutation6
    mixedMoment B raw2447step0 raw2447step0Labels = mixedMoment B raw2447step1 raw2447step1Labels := by
      have ha : raw2447step1 = -raw2447step0 := by apply Matrix.ext; change ∀ i j, raw2447step1 i j = -(raw2447step0 i j); unfold raw2447step1 raw2447step0; decide +kernel
      have hl : raw2447step1Labels = raw2447step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2447step1 raw2447step1Labels = mixedMoment B raw2447step2 raw2447step2Labels := by
      have ha : raw2447step2 = raw2447step1 := by apply Matrix.ext; unfold raw2447step2 raw2447step1; decide +kernel
      have hl : raw2447step1Labels = labelEmbedding1 ∘ raw2447step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2447step1 raw2447step1Labels raw2447step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3891 node3891Labels := by rfl

def raw2448 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2448step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2448 raw2448Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw2448 raw2448Labels = mixedMoment B raw2448step0 raw2448step0Labels := by
      have ha : raw2448step0 = (fun i j => raw2448 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2448step0 raw2448; decide +kernel
      have hl : raw2448step0Labels = raw2448Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2448 raw2448Labels permutation32 permutation4
    mixedMoment B raw2448step0 raw2448step0Labels = mixedMoment B raw2448step1 raw2448step1Labels := by
      have ha : raw2448step1 = raw2448step0 := by apply Matrix.ext; unfold raw2448step1 raw2448step0; decide +kernel
      have hl : raw2448step0Labels = labelEmbedding7 ∘ raw2448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2448step0 raw2448step0Labels raw2448step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw2449 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2449 raw2449Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw2449 raw2449Labels = mixedMoment B raw2449step0 raw2449step0Labels := by
      have ha : raw2449step0 = (fun i j => raw2449 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2449step0 raw2449; decide +kernel
      have hl : raw2449step0Labels = raw2449Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2449 raw2449Labels permutation32 permutation4
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw2450 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2450Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2450step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2450 raw2450Labels = mixedMoment B node3892 node3892Labels := by
  calc
    mixedMoment B raw2450 raw2450Labels = mixedMoment B raw2450step0 raw2450step0Labels := by
      have ha : raw2450step0 = (fun i j => raw2450 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2450step0 raw2450; decide +kernel
      have hl : raw2450step0Labels = raw2450Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2450 raw2450Labels permutation58 permutation3
    mixedMoment B raw2450step0 raw2450step0Labels = mixedMoment B raw2450step1 raw2450step1Labels := by
      have ha : raw2450step1 = -raw2450step0 := by apply Matrix.ext; change ∀ i j, raw2450step1 i j = -(raw2450step0 i j); unfold raw2450step1 raw2450step0; decide +kernel
      have hl : raw2450step1Labels = raw2450step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2450step1 raw2450step1Labels = mixedMoment B raw2450step2 raw2450step2Labels := by
      have ha : raw2450step2 = raw2450step1 := by apply Matrix.ext; unfold raw2450step2 raw2450step1; decide +kernel
      have hl : raw2450step1Labels = labelEmbedding1 ∘ raw2450step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2450step1 raw2450step1Labels raw2450step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3892 node3892Labels := by rfl

def raw2451 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2451step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2451step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2451step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2451 raw2451Labels = mixedMoment B node5389 node5389Labels := by
  calc
    mixedMoment B raw2451 raw2451Labels = mixedMoment B raw2451step0 raw2451step0Labels := by
      have ha : raw2451step0 = (fun i j => raw2451 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2451step0 raw2451; decide +kernel
      have hl : raw2451step0Labels = raw2451Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2451 raw2451Labels permutation8 permutation4
    mixedMoment B raw2451step0 raw2451step0Labels = mixedMoment B raw2451step1 raw2451step1Labels := by
      have ha : raw2451step1 = raw2451step0 := by apply Matrix.ext; unfold raw2451step1 raw2451step0; decide +kernel
      have hl : raw2451step0Labels = labelEmbedding7 ∘ raw2451step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2451step0 raw2451step0Labels raw2451step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5389 node5389Labels := by rfl

def raw2452 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2452step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw2452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2452 raw2452Labels = mixedMoment B node3740 node3740Labels := by
  calc
    mixedMoment B raw2452 raw2452Labels = mixedMoment B raw2452step0 raw2452step0Labels := by
      have ha : raw2452step0 = (fun i j => raw2452 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2452step0 raw2452; decide +kernel
      have hl : raw2452step0Labels = raw2452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2452 raw2452Labels permutation8 permutation4
    _ = mixedMoment B node3740 node3740Labels := by rfl

def raw2453 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-2, 2, 0], ![0, 2, -2]]
def raw2453Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2453step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]
def raw2453step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![0, 2, -2], ![2, 0, -2]]
def raw2453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2453 raw2453Labels = mixedMoment B node3893 node3893Labels := by
  calc
    mixedMoment B raw2453 raw2453Labels = mixedMoment B raw2453step0 raw2453step0Labels := by
      have ha : raw2453step0 = (fun i j => raw2453 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2453step0 raw2453; decide +kernel
      have hl : raw2453step0Labels = raw2453Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2453 raw2453Labels permutation24 permutation3
    mixedMoment B raw2453step0 raw2453step0Labels = mixedMoment B raw2453step1 raw2453step1Labels := by
      have ha : raw2453step1 = raw2453step0 := by apply Matrix.ext; unfold raw2453step1 raw2453step0; decide +kernel
      have hl : raw2453step0Labels = labelEmbedding1 ∘ raw2453step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2453step0 raw2453step0Labels raw2453step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3893 node3893Labels := by rfl

def raw2454 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2454step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2454step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2454 raw2454Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw2454 raw2454Labels = mixedMoment B raw2454step0 raw2454step0Labels := by
      have ha : raw2454step0 = (fun i j => raw2454 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2454step0 raw2454; decide +kernel
      have hl : raw2454step0Labels = raw2454Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2454 raw2454Labels permutation8 permutation4
    mixedMoment B raw2454step0 raw2454step0Labels = mixedMoment B raw2454step1 raw2454step1Labels := by
      have ha : raw2454step1 = raw2454step0 := by apply Matrix.ext; unfold raw2454step1 raw2454step0; decide +kernel
      have hl : raw2454step0Labels = labelEmbedding7 ∘ raw2454step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2454step0 raw2454step0Labels raw2454step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5390 node5390Labels := by rfl

def raw2455 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2455step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2455 raw2455Labels = mixedMoment B node3741 node3741Labels := by
  calc
    mixedMoment B raw2455 raw2455Labels = mixedMoment B raw2455step0 raw2455step0Labels := by
      have ha : raw2455step0 = (fun i j => raw2455 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2455step0 raw2455; decide +kernel
      have hl : raw2455step0Labels = raw2455Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2455 raw2455Labels permutation8 permutation4
    _ = mixedMoment B node3741 node3741Labels := by rfl

def raw2456 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -2, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2456Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2456step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw2456step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw2456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2]]
def raw2456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2456 raw2456Labels = mixedMoment B node3894 node3894Labels := by
  calc
    mixedMoment B raw2456 raw2456Labels = mixedMoment B raw2456step0 raw2456step0Labels := by
      have ha : raw2456step0 = (fun i j => raw2456 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2456step0 raw2456; decide +kernel
      have hl : raw2456step0Labels = raw2456Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2456 raw2456Labels permutation14 permutation3
    mixedMoment B raw2456step0 raw2456step0Labels = mixedMoment B raw2456step1 raw2456step1Labels := by
      have ha : raw2456step1 = -raw2456step0 := by apply Matrix.ext; change ∀ i j, raw2456step1 i j = -(raw2456step0 i j); unfold raw2456step1 raw2456step0; decide +kernel
      have hl : raw2456step1Labels = raw2456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2456step1 raw2456step1Labels = mixedMoment B raw2456step2 raw2456step2Labels := by
      have ha : raw2456step2 = raw2456step1 := by apply Matrix.ext; unfold raw2456step2 raw2456step1; decide +kernel
      have hl : raw2456step1Labels = labelEmbedding1 ∘ raw2456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2456step1 raw2456step1Labels raw2456step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3894 node3894Labels := by rfl

def raw2457 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2457step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2457step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2457 raw2457Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw2457 raw2457Labels = mixedMoment B raw2457step0 raw2457step0Labels := by
      have ha : raw2457step0 = (fun i j => raw2457 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2457step0 raw2457; decide +kernel
      have hl : raw2457step0Labels = raw2457Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2457 raw2457Labels permutation152 permutation4
    mixedMoment B raw2457step0 raw2457step0Labels = mixedMoment B raw2457step1 raw2457step1Labels := by
      have ha : raw2457step1 = raw2457step0 := by apply Matrix.ext; unfold raw2457step1 raw2457step0; decide +kernel
      have hl : raw2457step0Labels = labelEmbedding7 ∘ raw2457step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2457step0 raw2457step0Labels raw2457step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

def raw2458 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw2458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2458 raw2458Labels = mixedMoment B node3776 node3776Labels := by
  calc
    mixedMoment B raw2458 raw2458Labels = mixedMoment B raw2458step0 raw2458step0Labels := by
      have ha : raw2458step0 = (fun i j => raw2458 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2458step0 raw2458; decide +kernel
      have hl : raw2458step0Labels = raw2458Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2458 raw2458Labels permutation152 permutation4
    _ = mixedMoment B node3776 node3776Labels := by rfl

def raw2459 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw2459Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw2459step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw2459step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw2459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2459 raw2459Labels = mixedMoment B node3778 node3778Labels := by
  calc
    mixedMoment B raw2459 raw2459Labels = mixedMoment B raw2459step0 raw2459step0Labels := by
      have ha : raw2459step0 = (fun i j => raw2459 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2459step0 raw2459; decide +kernel
      have hl : raw2459step0Labels = raw2459Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2459 raw2459Labels permutation155 permutation6
    mixedMoment B raw2459step0 raw2459step0Labels = mixedMoment B raw2459step1 raw2459step1Labels := by
      have ha : raw2459step1 = -raw2459step0 := by apply Matrix.ext; change ∀ i j, raw2459step1 i j = -(raw2459step0 i j); unfold raw2459step1 raw2459step0; decide +kernel
      have hl : raw2459step1Labels = raw2459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2459step1 raw2459step1Labels = mixedMoment B raw2459step2 raw2459step2Labels := by
      have ha : raw2459step2 = raw2459step1 := by apply Matrix.ext; unfold raw2459step2 raw2459step1; decide +kernel
      have hl : raw2459step1Labels = labelEmbedding1 ∘ raw2459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2459step1 raw2459step1Labels raw2459step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3778 node3778Labels := by rfl

def raw2460 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2460step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2460 raw2460Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw2460 raw2460Labels = mixedMoment B raw2460step0 raw2460step0Labels := by
      have ha : raw2460step0 = (fun i j => raw2460 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2460step0 raw2460; decide +kernel
      have hl : raw2460step0Labels = raw2460Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2460 raw2460Labels permutation152 permutation4
    mixedMoment B raw2460step0 raw2460step0Labels = mixedMoment B raw2460step1 raw2460step1Labels := by
      have ha : raw2460step1 = raw2460step0 := by apply Matrix.ext; unfold raw2460step1 raw2460step0; decide +kernel
      have hl : raw2460step0Labels = labelEmbedding7 ∘ raw2460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2460step0 raw2460step0Labels raw2460step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw2461 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2461 raw2461Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw2461 raw2461Labels = mixedMoment B raw2461step0 raw2461step0Labels := by
      have ha : raw2461step0 = (fun i j => raw2461 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2461step0 raw2461; decide +kernel
      have hl : raw2461step0Labels = raw2461Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2461 raw2461Labels permutation152 permutation4
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw2462 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2462Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw2462step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2462step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2462step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw2462step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2462 raw2462Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw2462 raw2462Labels = mixedMoment B raw2462step0 raw2462step0Labels := by
      have ha : raw2462step0 = (fun i j => raw2462 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2462step0 raw2462; decide +kernel
      have hl : raw2462step0Labels = raw2462Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2462 raw2462Labels permutation152 permutation6
    mixedMoment B raw2462step0 raw2462step0Labels = mixedMoment B raw2462step1 raw2462step1Labels := by
      have ha : raw2462step1 = -raw2462step0 := by apply Matrix.ext; change ∀ i j, raw2462step1 i j = -(raw2462step0 i j); unfold raw2462step1 raw2462step0; decide +kernel
      have hl : raw2462step1Labels = raw2462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2462step1 raw2462step1Labels = mixedMoment B raw2462step2 raw2462step2Labels := by
      have ha : raw2462step2 = raw2462step1 := by apply Matrix.ext; unfold raw2462step2 raw2462step1; decide +kernel
      have hl : raw2462step1Labels = labelEmbedding1 ∘ raw2462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2462step1 raw2462step1Labels raw2462step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

def raw2463 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2463step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2463 raw2463Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw2463 raw2463Labels = mixedMoment B raw2463step0 raw2463step0Labels := by
      have ha : raw2463step0 = (fun i j => raw2463 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2463step0 raw2463; decide +kernel
      have hl : raw2463step0Labels = raw2463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2463 raw2463Labels permutation152 permutation4
    mixedMoment B raw2463step0 raw2463step0Labels = mixedMoment B raw2463step1 raw2463step1Labels := by
      have ha : raw2463step1 = raw2463step0 := by apply Matrix.ext; unfold raw2463step1 raw2463step0; decide +kernel
      have hl : raw2463step0Labels = labelEmbedding7 ∘ raw2463step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2463step0 raw2463step0Labels raw2463step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw2464 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw2464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2464 raw2464Labels = mixedMoment B node3781 node3781Labels := by
  calc
    mixedMoment B raw2464 raw2464Labels = mixedMoment B raw2464step0 raw2464step0Labels := by
      have ha : raw2464step0 = (fun i j => raw2464 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2464step0 raw2464; decide +kernel
      have hl : raw2464step0Labels = raw2464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2464 raw2464Labels permutation152 permutation4
    _ = mixedMoment B node3781 node3781Labels := by rfl

def raw2465 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw2465Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2465step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2465step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2465step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw2465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2465 raw2465Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw2465 raw2465Labels = mixedMoment B raw2465step0 raw2465step0Labels := by
      have ha : raw2465step0 = (fun i j => raw2465 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2465step0 raw2465; decide +kernel
      have hl : raw2465step0Labels = raw2465Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2465 raw2465Labels permutation153 permutation6
    mixedMoment B raw2465step0 raw2465step0Labels = mixedMoment B raw2465step1 raw2465step1Labels := by
      have ha : raw2465step1 = -raw2465step0 := by apply Matrix.ext; change ∀ i j, raw2465step1 i j = -(raw2465step0 i j); unfold raw2465step1 raw2465step0; decide +kernel
      have hl : raw2465step1Labels = raw2465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2465step1 raw2465step1Labels = mixedMoment B raw2465step2 raw2465step2Labels := by
      have ha : raw2465step2 = raw2465step1 := by apply Matrix.ext; unfold raw2465step2 raw2465step1; decide +kernel
      have hl : raw2465step1Labels = labelEmbedding1 ∘ raw2465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2465step1 raw2465step1Labels raw2465step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw2466 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2466step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2466 raw2466Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw2466 raw2466Labels = mixedMoment B raw2466step0 raw2466step0Labels := by
      have ha : raw2466step0 = (fun i j => raw2466 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2466step0 raw2466; decide +kernel
      have hl : raw2466step0Labels = raw2466Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2466 raw2466Labels permutation152 permutation4
    mixedMoment B raw2466step0 raw2466step0Labels = mixedMoment B raw2466step1 raw2466step1Labels := by
      have ha : raw2466step1 = raw2466step0 := by apply Matrix.ext; unfold raw2466step1 raw2466step0; decide +kernel
      have hl : raw2466step0Labels = labelEmbedding7 ∘ raw2466step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2466step0 raw2466step0Labels raw2466step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw2467 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2467 raw2467Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw2467 raw2467Labels = mixedMoment B raw2467step0 raw2467step0Labels := by
      have ha : raw2467step0 = (fun i j => raw2467 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2467step0 raw2467; decide +kernel
      have hl : raw2467step0Labels = raw2467Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2467 raw2467Labels permutation152 permutation4
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw2468 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2468Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw2468step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2468step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2468step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw2468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2468 raw2468Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw2468 raw2468Labels = mixedMoment B raw2468step0 raw2468step0Labels := by
      have ha : raw2468step0 = (fun i j => raw2468 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2468step0 raw2468; decide +kernel
      have hl : raw2468step0Labels = raw2468Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2468 raw2468Labels permutation156 permutation6
    mixedMoment B raw2468step0 raw2468step0Labels = mixedMoment B raw2468step1 raw2468step1Labels := by
      have ha : raw2468step1 = -raw2468step0 := by apply Matrix.ext; change ∀ i j, raw2468step1 i j = -(raw2468step0 i j); unfold raw2468step1 raw2468step0; decide +kernel
      have hl : raw2468step1Labels = raw2468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2468step1 raw2468step1Labels = mixedMoment B raw2468step2 raw2468step2Labels := by
      have ha : raw2468step2 = raw2468step1 := by apply Matrix.ext; unfold raw2468step2 raw2468step1; decide +kernel
      have hl : raw2468step1Labels = labelEmbedding1 ∘ raw2468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2468step1 raw2468step1Labels raw2468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw2469 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2469step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2469 raw2469Labels = mixedMoment B node5398 node5398Labels := by
  calc
    mixedMoment B raw2469 raw2469Labels = mixedMoment B raw2469step0 raw2469step0Labels := by
      have ha : raw2469step0 = (fun i j => raw2469 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2469step0 raw2469; decide +kernel
      have hl : raw2469step0Labels = raw2469Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2469 raw2469Labels permutation152 permutation4
    mixedMoment B raw2469step0 raw2469step0Labels = mixedMoment B raw2469step1 raw2469step1Labels := by
      have ha : raw2469step1 = raw2469step0 := by apply Matrix.ext; unfold raw2469step1 raw2469step0; decide +kernel
      have hl : raw2469step0Labels = labelEmbedding7 ∘ raw2469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2469step0 raw2469step0Labels raw2469step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5398 node5398Labels := by rfl

def raw2470 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2470 raw2470Labels = mixedMoment B node3784 node3784Labels := by
  calc
    mixedMoment B raw2470 raw2470Labels = mixedMoment B raw2470step0 raw2470step0Labels := by
      have ha : raw2470step0 = (fun i j => raw2470 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2470step0 raw2470; decide +kernel
      have hl : raw2470step0Labels = raw2470Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2470 raw2470Labels permutation152 permutation4
    _ = mixedMoment B node3784 node3784Labels := by rfl

def raw2471 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw2471Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2471step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw2471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2471 raw2471Labels = mixedMoment B node3784 node3784Labels := by
  calc
    mixedMoment B raw2471 raw2471Labels = mixedMoment B raw2471step0 raw2471step0Labels := by
      have ha : raw2471step0 = (fun i j => raw2471 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2471step0 raw2471; decide +kernel
      have hl : raw2471step0Labels = raw2471Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2471 raw2471Labels permutation682 permutation6
    mixedMoment B raw2471step0 raw2471step0Labels = mixedMoment B raw2471step1 raw2471step1Labels := by
      have ha : raw2471step1 = raw2471step0 := by apply Matrix.ext; unfold raw2471step1 raw2471step0; decide +kernel
      have hl : raw2471step0Labels = labelEmbedding1 ∘ raw2471step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2471step0 raw2471step0Labels raw2471step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3784 node3784Labels := by rfl

def raw2472 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2472step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2472 raw2472Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw2472 raw2472Labels = mixedMoment B raw2472step0 raw2472step0Labels := by
      have ha : raw2472step0 = (fun i j => raw2472 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2472step0 raw2472; decide +kernel
      have hl : raw2472step0Labels = raw2472Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2472 raw2472Labels permutation152 permutation4
    mixedMoment B raw2472step0 raw2472step0Labels = mixedMoment B raw2472step1 raw2472step1Labels := by
      have ha : raw2472step1 = raw2472step0 := by apply Matrix.ext; unfold raw2472step1 raw2472step0; decide +kernel
      have hl : raw2472step0Labels = labelEmbedding7 ∘ raw2472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2472step0 raw2472step0Labels raw2472step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw2473 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2473 raw2473Labels = mixedMoment B node3786 node3786Labels := by
  calc
    mixedMoment B raw2473 raw2473Labels = mixedMoment B raw2473step0 raw2473step0Labels := by
      have ha : raw2473step0 = (fun i j => raw2473 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2473step0 raw2473; decide +kernel
      have hl : raw2473step0Labels = raw2473Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2473 raw2473Labels permutation152 permutation4
    _ = mixedMoment B node3786 node3786Labels := by rfl

def raw2474 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2474Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw2474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2474step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2474step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2474 raw2474Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw2474 raw2474Labels = mixedMoment B raw2474step0 raw2474step0Labels := by
      have ha : raw2474step0 = (fun i j => raw2474 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2474step0 raw2474; decide +kernel
      have hl : raw2474step0Labels = raw2474Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2474 raw2474Labels permutation160 permutation6
    mixedMoment B raw2474step0 raw2474step0Labels = mixedMoment B raw2474step1 raw2474step1Labels := by
      have ha : raw2474step1 = -raw2474step0 := by apply Matrix.ext; change ∀ i j, raw2474step1 i j = -(raw2474step0 i j); unfold raw2474step1 raw2474step0; decide +kernel
      have hl : raw2474step1Labels = raw2474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2474step1 raw2474step1Labels = mixedMoment B raw2474step2 raw2474step2Labels := by
      have ha : raw2474step2 = raw2474step1 := by apply Matrix.ext; unfold raw2474step2 raw2474step1; decide +kernel
      have hl : raw2474step1Labels = labelEmbedding1 ∘ raw2474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2474step1 raw2474step1Labels raw2474step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw2475 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2475step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2475 raw2475Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw2475 raw2475Labels = mixedMoment B raw2475step0 raw2475step0Labels := by
      have ha : raw2475step0 = (fun i j => raw2475 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2475step0 raw2475; decide +kernel
      have hl : raw2475step0Labels = raw2475Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2475 raw2475Labels permutation152 permutation4
    mixedMoment B raw2475step0 raw2475step0Labels = mixedMoment B raw2475step1 raw2475step1Labels := by
      have ha : raw2475step1 = raw2475step0 := by apply Matrix.ext; unfold raw2475step1 raw2475step0; decide +kernel
      have hl : raw2475step0Labels = labelEmbedding7 ∘ raw2475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2475step0 raw2475step0Labels raw2475step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw2476 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2476 raw2476Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw2476 raw2476Labels = mixedMoment B raw2476step0 raw2476step0Labels := by
      have ha : raw2476step0 = (fun i j => raw2476 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2476step0 raw2476; decide +kernel
      have hl : raw2476step0Labels = raw2476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2476 raw2476Labels permutation152 permutation4
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw2477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2477Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2477step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2477step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2477step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2477 raw2477Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw2477 raw2477Labels = mixedMoment B raw2477step0 raw2477step0Labels := by
      have ha : raw2477step0 = (fun i j => raw2477 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2477step0 raw2477; decide +kernel
      have hl : raw2477step0Labels = raw2477Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2477 raw2477Labels permutation158 permutation6
    mixedMoment B raw2477step0 raw2477step0Labels = mixedMoment B raw2477step1 raw2477step1Labels := by
      have ha : raw2477step1 = -raw2477step0 := by apply Matrix.ext; change ∀ i j, raw2477step1 i j = -(raw2477step0 i j); unfold raw2477step1 raw2477step0; decide +kernel
      have hl : raw2477step1Labels = raw2477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2477step1 raw2477step1Labels = mixedMoment B raw2477step2 raw2477step2Labels := by
      have ha : raw2477step2 = raw2477step1 := by apply Matrix.ext; unfold raw2477step2 raw2477step1; decide +kernel
      have hl : raw2477step1Labels = labelEmbedding1 ∘ raw2477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2477step1 raw2477step1Labels raw2477step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw2478 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2478step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2478step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2478 raw2478Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw2478 raw2478Labels = mixedMoment B raw2478step0 raw2478step0Labels := by
      have ha : raw2478step0 = (fun i j => raw2478 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2478step0 raw2478; decide +kernel
      have hl : raw2478step0Labels = raw2478Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2478 raw2478Labels permutation152 permutation4
    mixedMoment B raw2478step0 raw2478step0Labels = mixedMoment B raw2478step1 raw2478step1Labels := by
      have ha : raw2478step1 = raw2478step0 := by apply Matrix.ext; unfold raw2478step1 raw2478step0; decide +kernel
      have hl : raw2478step0Labels = labelEmbedding7 ∘ raw2478step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2478step0 raw2478step0Labels raw2478step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw2479 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2479 raw2479Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw2479 raw2479Labels = mixedMoment B raw2479step0 raw2479step0Labels := by
      have ha : raw2479step0 = (fun i j => raw2479 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2479step0 raw2479; decide +kernel
      have hl : raw2479step0Labels = raw2479Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2479 raw2479Labels permutation152 permutation4
    _ = mixedMoment B node3789 node3789Labels := by rfl

def raw2480 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2480Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2480step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2480step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2480step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2480step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2480 raw2480Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw2480 raw2480Labels = mixedMoment B raw2480step0 raw2480step0Labels := by
      have ha : raw2480step0 = (fun i j => raw2480 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2480step0 raw2480; decide +kernel
      have hl : raw2480step0Labels = raw2480Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2480 raw2480Labels permutation170 permutation6
    mixedMoment B raw2480step0 raw2480step0Labels = mixedMoment B raw2480step1 raw2480step1Labels := by
      have ha : raw2480step1 = -raw2480step0 := by apply Matrix.ext; change ∀ i j, raw2480step1 i j = -(raw2480step0 i j); unfold raw2480step1 raw2480step0; decide +kernel
      have hl : raw2480step1Labels = raw2480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2480step1 raw2480step1Labels = mixedMoment B raw2480step2 raw2480step2Labels := by
      have ha : raw2480step2 = raw2480step1 := by apply Matrix.ext; unfold raw2480step2 raw2480step1; decide +kernel
      have hl : raw2480step1Labels = labelEmbedding1 ∘ raw2480step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2480step1 raw2480step1Labels raw2480step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

def raw2481 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2481step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2481 raw2481Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw2481 raw2481Labels = mixedMoment B raw2481step0 raw2481step0Labels := by
      have ha : raw2481step0 = (fun i j => raw2481 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2481step0 raw2481; decide +kernel
      have hl : raw2481step0Labels = raw2481Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2481 raw2481Labels permutation32 permutation4
    mixedMoment B raw2481step0 raw2481step0Labels = mixedMoment B raw2481step1 raw2481step1Labels := by
      have ha : raw2481step1 = raw2481step0 := by apply Matrix.ext; unfold raw2481step1 raw2481step0; decide +kernel
      have hl : raw2481step0Labels = labelEmbedding7 ∘ raw2481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2481step0 raw2481step0Labels raw2481step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw2482 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw2482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2482 raw2482Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw2482 raw2482Labels = mixedMoment B raw2482step0 raw2482step0Labels := by
      have ha : raw2482step0 = (fun i j => raw2482 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2482step0 raw2482; decide +kernel
      have hl : raw2482step0Labels = raw2482Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2482 raw2482Labels permutation32 permutation4
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw2483 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw2483Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2483step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2483step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2483 raw2483Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw2483 raw2483Labels = mixedMoment B raw2483step0 raw2483step0Labels := by
      have ha : raw2483step0 = (fun i j => raw2483 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2483step0 raw2483; decide +kernel
      have hl : raw2483step0Labels = raw2483Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2483 raw2483Labels permutation32 permutation6
    mixedMoment B raw2483step0 raw2483step0Labels = mixedMoment B raw2483step1 raw2483step1Labels := by
      have ha : raw2483step1 = -raw2483step0 := by apply Matrix.ext; change ∀ i j, raw2483step1 i j = -(raw2483step0 i j); unfold raw2483step1 raw2483step0; decide +kernel
      have hl : raw2483step1Labels = raw2483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2483step1 raw2483step1Labels = mixedMoment B raw2483step2 raw2483step2Labels := by
      have ha : raw2483step2 = raw2483step1 := by apply Matrix.ext; unfold raw2483step2 raw2483step1; decide +kernel
      have hl : raw2483step1Labels = labelEmbedding1 ∘ raw2483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2483step1 raw2483step1Labels raw2483step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

def raw2484 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2484step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2484 raw2484Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw2484 raw2484Labels = mixedMoment B raw2484step0 raw2484step0Labels := by
      have ha : raw2484step0 = (fun i j => raw2484 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2484step0 raw2484; decide +kernel
      have hl : raw2484step0Labels = raw2484Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2484 raw2484Labels permutation152 permutation4
    mixedMoment B raw2484step0 raw2484step0Labels = mixedMoment B raw2484step1 raw2484step1Labels := by
      have ha : raw2484step1 = raw2484step0 := by apply Matrix.ext; unfold raw2484step1 raw2484step0; decide +kernel
      have hl : raw2484step0Labels = labelEmbedding7 ∘ raw2484step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2484step0 raw2484step0Labels raw2484step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw2485 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2485 raw2485Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw2485 raw2485Labels = mixedMoment B raw2485step0 raw2485step0Labels := by
      have ha : raw2485step0 = (fun i j => raw2485 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2485step0 raw2485; decide +kernel
      have hl : raw2485step0Labels = raw2485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2485 raw2485Labels permutation152 permutation4
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw2486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2486Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw2486step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2486step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2486 raw2486Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw2486 raw2486Labels = mixedMoment B raw2486step0 raw2486step0Labels := by
      have ha : raw2486step0 = (fun i j => raw2486 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2486step0 raw2486; decide +kernel
      have hl : raw2486step0Labels = raw2486Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2486 raw2486Labels permutation164 permutation6
    mixedMoment B raw2486step0 raw2486step0Labels = mixedMoment B raw2486step1 raw2486step1Labels := by
      have ha : raw2486step1 = -raw2486step0 := by apply Matrix.ext; change ∀ i j, raw2486step1 i j = -(raw2486step0 i j); unfold raw2486step1 raw2486step0; decide +kernel
      have hl : raw2486step1Labels = raw2486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2486step1 raw2486step1Labels = mixedMoment B raw2486step2 raw2486step2Labels := by
      have ha : raw2486step2 = raw2486step1 := by apply Matrix.ext; unfold raw2486step2 raw2486step1; decide +kernel
      have hl : raw2486step1Labels = labelEmbedding1 ∘ raw2486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2486step1 raw2486step1Labels raw2486step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw2487 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2487step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2487step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2487step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2487 raw2487Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw2487 raw2487Labels = mixedMoment B raw2487step0 raw2487step0Labels := by
      have ha : raw2487step0 = (fun i j => raw2487 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2487step0 raw2487; decide +kernel
      have hl : raw2487step0Labels = raw2487Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2487 raw2487Labels permutation152 permutation4
    mixedMoment B raw2487step0 raw2487step0Labels = mixedMoment B raw2487step1 raw2487step1Labels := by
      have ha : raw2487step1 = raw2487step0 := by apply Matrix.ext; unfold raw2487step1 raw2487step0; decide +kernel
      have hl : raw2487step0Labels = labelEmbedding7 ∘ raw2487step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2487step0 raw2487step0Labels raw2487step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw2488 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2488 raw2488Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw2488 raw2488Labels = mixedMoment B raw2488step0 raw2488step0Labels := by
      have ha : raw2488step0 = (fun i j => raw2488 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2488step0 raw2488; decide +kernel
      have hl : raw2488step0Labels = raw2488Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2488 raw2488Labels permutation152 permutation4
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw2489 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2489Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw2489step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2489step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2489step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2489step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2489 raw2489Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw2489 raw2489Labels = mixedMoment B raw2489step0 raw2489step0Labels := by
      have ha : raw2489step0 = (fun i j => raw2489 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2489step0 raw2489; decide +kernel
      have hl : raw2489step0Labels = raw2489Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2489 raw2489Labels permutation170 permutation6
    mixedMoment B raw2489step0 raw2489step0Labels = mixedMoment B raw2489step1 raw2489step1Labels := by
      have ha : raw2489step1 = -raw2489step0 := by apply Matrix.ext; change ∀ i j, raw2489step1 i j = -(raw2489step0 i j); unfold raw2489step1 raw2489step0; decide +kernel
      have hl : raw2489step1Labels = raw2489step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2489step1 raw2489step1Labels = mixedMoment B raw2489step2 raw2489step2Labels := by
      have ha : raw2489step2 = raw2489step1 := by apply Matrix.ext; unfold raw2489step2 raw2489step1; decide +kernel
      have hl : raw2489step1Labels = labelEmbedding1 ∘ raw2489step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2489step1 raw2489step1Labels raw2489step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw2490 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2490step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2490step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2490 raw2490Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw2490 raw2490Labels = mixedMoment B raw2490step0 raw2490step0Labels := by
      have ha : raw2490step0 = (fun i j => raw2490 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2490step0 raw2490; decide +kernel
      have hl : raw2490step0Labels = raw2490Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2490 raw2490Labels permutation32 permutation4
    mixedMoment B raw2490step0 raw2490step0Labels = mixedMoment B raw2490step1 raw2490step1Labels := by
      have ha : raw2490step1 = raw2490step0 := by apply Matrix.ext; unfold raw2490step1 raw2490step0; decide +kernel
      have hl : raw2490step0Labels = labelEmbedding7 ∘ raw2490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2490step0 raw2490step0Labels raw2490step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw2491 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2491 raw2491Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw2491 raw2491Labels = mixedMoment B raw2491step0 raw2491step0Labels := by
      have ha : raw2491step0 = (fun i j => raw2491 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2491step0 raw2491; decide +kernel
      have hl : raw2491step0Labels = raw2491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2491 raw2491Labels permutation32 permutation4
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw2492 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw2492Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw2492step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw2492step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw2492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2492 raw2492Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw2492 raw2492Labels = mixedMoment B raw2492step0 raw2492step0Labels := by
      have ha : raw2492step0 = (fun i j => raw2492 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2492step0 raw2492; decide +kernel
      have hl : raw2492step0Labels = raw2492Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2492 raw2492Labels permutation36 permutation6
    mixedMoment B raw2492step0 raw2492step0Labels = mixedMoment B raw2492step1 raw2492step1Labels := by
      have ha : raw2492step1 = -raw2492step0 := by apply Matrix.ext; change ∀ i j, raw2492step1 i j = -(raw2492step0 i j); unfold raw2492step1 raw2492step0; decide +kernel
      have hl : raw2492step1Labels = raw2492step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2492step1 raw2492step1Labels = mixedMoment B raw2492step2 raw2492step2Labels := by
      have ha : raw2492step2 = raw2492step1 := by apply Matrix.ext; unfold raw2492step2 raw2492step1; decide +kernel
      have hl : raw2492step1Labels = labelEmbedding1 ∘ raw2492step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2492step1 raw2492step1Labels raw2492step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw2493 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw2493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2493step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2493 raw2493Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw2493 raw2493Labels = mixedMoment B raw2493step0 raw2493step0Labels := by
      have ha : raw2493step0 = (fun i j => raw2493 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2493step0 raw2493; decide +kernel
      have hl : raw2493step0Labels = raw2493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2493 raw2493Labels permutation32 permutation4
    mixedMoment B raw2493step0 raw2493step0Labels = mixedMoment B raw2493step1 raw2493step1Labels := by
      have ha : raw2493step1 = raw2493step0 := by apply Matrix.ext; unfold raw2493step1 raw2493step0; decide +kernel
      have hl : raw2493step0Labels = labelEmbedding7 ∘ raw2493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2493step0 raw2493step0Labels raw2493step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw2494 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw2494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2494 raw2494Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2494 raw2494Labels = mixedMoment B raw2494step0 raw2494step0Labels := by
      have ha : raw2494step0 = (fun i j => raw2494 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2494step0 raw2494; decide +kernel
      have hl : raw2494step0Labels = raw2494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2494 raw2494Labels permutation32 permutation4
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw2495 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![-2, 2, 0]]
def raw2495Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw2495step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw2495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2495 raw2495Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw2495 raw2495Labels = mixedMoment B raw2495step0 raw2495step0Labels := by
      have ha : raw2495step0 = (fun i j => raw2495 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2495step0 raw2495; decide +kernel
      have hl : raw2495step0Labels = raw2495Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2495 raw2495Labels permutation37 permutation6
    mixedMoment B raw2495step0 raw2495step0Labels = mixedMoment B raw2495step1 raw2495step1Labels := by
      have ha : raw2495step1 = -raw2495step0 := by apply Matrix.ext; change ∀ i j, raw2495step1 i j = -(raw2495step0 i j); unfold raw2495step1 raw2495step0; decide +kernel
      have hl : raw2495step1Labels = raw2495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2495step1 raw2495step1Labels = mixedMoment B raw2495step2 raw2495step2Labels := by
      have ha : raw2495step2 = raw2495step1 := by apply Matrix.ext; unfold raw2495step2 raw2495step1; decide +kernel
      have hl : raw2495step1Labels = labelEmbedding1 ∘ raw2495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2495step1 raw2495step1Labels raw2495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw2496 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2496step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2496step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2496 raw2496Labels = mixedMoment B node5415 node5415Labels := by
  calc
    mixedMoment B raw2496 raw2496Labels = mixedMoment B raw2496step0 raw2496step0Labels := by
      have ha : raw2496step0 = (fun i j => raw2496 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2496step0 raw2496; decide +kernel
      have hl : raw2496step0Labels = raw2496Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2496 raw2496Labels permutation152 permutation4
    mixedMoment B raw2496step0 raw2496step0Labels = mixedMoment B raw2496step1 raw2496step1Labels := by
      have ha : raw2496step1 = raw2496step0 := by apply Matrix.ext; unfold raw2496step1 raw2496step0; decide +kernel
      have hl : raw2496step0Labels = labelEmbedding7 ∘ raw2496step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2496step0 raw2496step0Labels raw2496step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5415 node5415Labels := by rfl

def raw2497 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw2497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2497 raw2497Labels = mixedMoment B node3820 node3820Labels := by
  calc
    mixedMoment B raw2497 raw2497Labels = mixedMoment B raw2497step0 raw2497step0Labels := by
      have ha : raw2497step0 = (fun i j => raw2497 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2497step0 raw2497; decide +kernel
      have hl : raw2497step0Labels = raw2497Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2497 raw2497Labels permutation152 permutation4
    _ = mixedMoment B node3820 node3820Labels := by rfl

def raw2498 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw2498Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw2498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2498 raw2498Labels = mixedMoment B node3895 node3895Labels := by
  calc
    mixedMoment B raw2498 raw2498Labels = mixedMoment B raw2498step0 raw2498step0Labels := by
      have ha : raw2498step0 = (fun i j => raw2498 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2498step0 raw2498; decide +kernel
      have hl : raw2498step0Labels = raw2498Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2498 raw2498Labels permutation662 permutation6
    mixedMoment B raw2498step0 raw2498step0Labels = mixedMoment B raw2498step1 raw2498step1Labels := by
      have ha : raw2498step1 = raw2498step0 := by apply Matrix.ext; unfold raw2498step1 raw2498step0; decide +kernel
      have hl : raw2498step0Labels = labelEmbedding1 ∘ raw2498step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2498step0 raw2498step0Labels raw2498step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3895 node3895Labels := by rfl

def raw2499 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2499step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2499step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2499 raw2499Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw2499 raw2499Labels = mixedMoment B raw2499step0 raw2499step0Labels := by
      have ha : raw2499step0 = (fun i j => raw2499 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2499step0 raw2499; decide +kernel
      have hl : raw2499step0Labels = raw2499Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2499 raw2499Labels permutation152 permutation4
    mixedMoment B raw2499step0 raw2499step0Labels = mixedMoment B raw2499step1 raw2499step1Labels := by
      have ha : raw2499step1 = raw2499step0 := by apply Matrix.ext; unfold raw2499step1 raw2499step0; decide +kernel
      have hl : raw2499step0Labels = labelEmbedding7 ∘ raw2499step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2499step0 raw2499step0Labels raw2499step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw2500 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw2500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2500 raw2500Labels = mixedMoment B node3821 node3821Labels := by
  calc
    mixedMoment B raw2500 raw2500Labels = mixedMoment B raw2500step0 raw2500step0Labels := by
      have ha : raw2500step0 = (fun i j => raw2500 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2500step0 raw2500; decide +kernel
      have hl : raw2500step0Labels = raw2500Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2500 raw2500Labels permutation152 permutation4
    _ = mixedMoment B node3821 node3821Labels := by rfl

def raw2501 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw2501Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw2501step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw2501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2501 raw2501Labels = mixedMoment B node3896 node3896Labels := by
  calc
    mixedMoment B raw2501 raw2501Labels = mixedMoment B raw2501step0 raw2501step0Labels := by
      have ha : raw2501step0 = (fun i j => raw2501 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2501step0 raw2501; decide +kernel
      have hl : raw2501step0Labels = raw2501Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2501 raw2501Labels permutation152 permutation6
    mixedMoment B raw2501step0 raw2501step0Labels = mixedMoment B raw2501step1 raw2501step1Labels := by
      have ha : raw2501step1 = -raw2501step0 := by apply Matrix.ext; change ∀ i j, raw2501step1 i j = -(raw2501step0 i j); unfold raw2501step1 raw2501step0; decide +kernel
      have hl : raw2501step1Labels = raw2501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2501step1 raw2501step1Labels = mixedMoment B raw2501step2 raw2501step2Labels := by
      have ha : raw2501step2 = raw2501step1 := by apply Matrix.ext; unfold raw2501step2 raw2501step1; decide +kernel
      have hl : raw2501step1Labels = labelEmbedding1 ∘ raw2501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2501step1 raw2501step1Labels raw2501step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3896 node3896Labels := by rfl

def raw2502 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2502step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2502step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2502 raw2502Labels = mixedMoment B node5417 node5417Labels := by
  calc
    mixedMoment B raw2502 raw2502Labels = mixedMoment B raw2502step0 raw2502step0Labels := by
      have ha : raw2502step0 = (fun i j => raw2502 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2502step0 raw2502; decide +kernel
      have hl : raw2502step0Labels = raw2502Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2502 raw2502Labels permutation152 permutation4
    mixedMoment B raw2502step0 raw2502step0Labels = mixedMoment B raw2502step1 raw2502step1Labels := by
      have ha : raw2502step1 = raw2502step0 := by apply Matrix.ext; unfold raw2502step1 raw2502step0; decide +kernel
      have hl : raw2502step0Labels = labelEmbedding7 ∘ raw2502step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2502step0 raw2502step0Labels raw2502step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5417 node5417Labels := by rfl

def raw2503 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2503Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2503 raw2503Labels = mixedMoment B node3823 node3823Labels := by
  calc
    mixedMoment B raw2503 raw2503Labels = mixedMoment B raw2503step0 raw2503step0Labels := by
      have ha : raw2503step0 = (fun i j => raw2503 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2503step0 raw2503; decide +kernel
      have hl : raw2503step0Labels = raw2503Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2503 raw2503Labels permutation152 permutation4
    _ = mixedMoment B node3823 node3823Labels := by rfl

def raw2504 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2504Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw2504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2504 raw2504Labels = mixedMoment B node3897 node3897Labels := by
  calc
    mixedMoment B raw2504 raw2504Labels = mixedMoment B raw2504step0 raw2504step0Labels := by
      have ha : raw2504step0 = (fun i j => raw2504 (permutation659 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2504step0 raw2504; decide +kernel
      have hl : raw2504step0Labels = raw2504Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2504 raw2504Labels permutation659 permutation3
    mixedMoment B raw2504step0 raw2504step0Labels = mixedMoment B raw2504step1 raw2504step1Labels := by
      have ha : raw2504step1 = raw2504step0 := by apply Matrix.ext; unfold raw2504step1 raw2504step0; decide +kernel
      have hl : raw2504step0Labels = labelEmbedding1 ∘ raw2504step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2504step0 raw2504step0Labels raw2504step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3897 node3897Labels := by rfl

def raw2505 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2505step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2505 raw2505Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw2505 raw2505Labels = mixedMoment B raw2505step0 raw2505step0Labels := by
      have ha : raw2505step0 = (fun i j => raw2505 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2505step0 raw2505; decide +kernel
      have hl : raw2505step0Labels = raw2505Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2505 raw2505Labels permutation32 permutation4
    mixedMoment B raw2505step0 raw2505step0Labels = mixedMoment B raw2505step1 raw2505step1Labels := by
      have ha : raw2505step1 = raw2505step0 := by apply Matrix.ext; unfold raw2505step1 raw2505step0; decide +kernel
      have hl : raw2505step0Labels = labelEmbedding7 ∘ raw2505step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2505step0 raw2505step0Labels raw2505step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw2506 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw2506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2506 raw2506Labels = mixedMoment B node3824 node3824Labels := by
  calc
    mixedMoment B raw2506 raw2506Labels = mixedMoment B raw2506step0 raw2506step0Labels := by
      have ha : raw2506step0 = (fun i j => raw2506 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2506step0 raw2506; decide +kernel
      have hl : raw2506step0Labels = raw2506Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2506 raw2506Labels permutation32 permutation4
    _ = mixedMoment B node3824 node3824Labels := by rfl

def raw2507 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, 2, -1]]
def raw2507Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw2507step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw2507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2507 raw2507Labels = mixedMoment B node3898 node3898Labels := by
  calc
    mixedMoment B raw2507 raw2507Labels = mixedMoment B raw2507step0 raw2507step0Labels := by
      have ha : raw2507step0 = (fun i j => raw2507 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2507step0 raw2507; decide +kernel
      have hl : raw2507step0Labels = raw2507Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2507 raw2507Labels permutation32 permutation6
    mixedMoment B raw2507step0 raw2507step0Labels = mixedMoment B raw2507step1 raw2507step1Labels := by
      have ha : raw2507step1 = -raw2507step0 := by apply Matrix.ext; change ∀ i j, raw2507step1 i j = -(raw2507step0 i j); unfold raw2507step1 raw2507step0; decide +kernel
      have hl : raw2507step1Labels = raw2507step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2507step1 raw2507step1Labels = mixedMoment B raw2507step2 raw2507step2Labels := by
      have ha : raw2507step2 = raw2507step1 := by apply Matrix.ext; unfold raw2507step2 raw2507step1; decide +kernel
      have hl : raw2507step1Labels = labelEmbedding1 ∘ raw2507step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2507step1 raw2507step1Labels raw2507step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3898 node3898Labels := by rfl

def raw2508 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2508step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw2508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2508 raw2508Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw2508 raw2508Labels = mixedMoment B raw2508step0 raw2508step0Labels := by
      have ha : raw2508step0 = (fun i j => raw2508 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2508step0 raw2508; decide +kernel
      have hl : raw2508step0Labels = raw2508Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2508 raw2508Labels permutation152 permutation5
    mixedMoment B raw2508step0 raw2508step0Labels = mixedMoment B raw2508step1 raw2508step1Labels := by
      have ha : raw2508step1 = raw2508step0 := by apply Matrix.ext; unfold raw2508step1 raw2508step0; decide +kernel
      have hl : raw2508step0Labels = labelEmbedding8 ∘ raw2508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2508step0 raw2508step0Labels raw2508step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw2509 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw2509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw2509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2509 raw2509Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw2509 raw2509Labels = mixedMoment B raw2509step0 raw2509step0Labels := by
      have ha : raw2509step0 = (fun i j => raw2509 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2509step0 raw2509; decide +kernel
      have hl : raw2509step0Labels = raw2509Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2509 raw2509Labels permutation662 permutation4
    mixedMoment B raw2509step0 raw2509step0Labels = mixedMoment B raw2509step1 raw2509step1Labels := by
      have ha : raw2509step1 = -raw2509step0 := by apply Matrix.ext; change ∀ i j, raw2509step1 i j = -(raw2509step0 i j); unfold raw2509step1 raw2509step0; decide +kernel
      have hl : raw2509step1Labels = raw2509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

def raw2510 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2510Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw2510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2510step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw2510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2510 raw2510Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw2510 raw2510Labels = mixedMoment B raw2510step0 raw2510step0Labels := by
      have ha : raw2510step0 = (fun i j => raw2510 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2510step0 raw2510; decide +kernel
      have hl : raw2510step0Labels = raw2510Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2510 raw2510Labels permutation160 permutation3
    mixedMoment B raw2510step0 raw2510step0Labels = mixedMoment B raw2510step1 raw2510step1Labels := by
      have ha : raw2510step1 = -raw2510step0 := by apply Matrix.ext; change ∀ i j, raw2510step1 i j = -(raw2510step0 i j); unfold raw2510step1 raw2510step0; decide +kernel
      have hl : raw2510step1Labels = raw2510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2510step1 raw2510step1Labels = mixedMoment B raw2510step2 raw2510step2Labels := by
      have ha : raw2510step2 = raw2510step1 := by apply Matrix.ext; unfold raw2510step2 raw2510step1; decide +kernel
      have hl : raw2510step1Labels = labelEmbedding1 ∘ raw2510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2510step1 raw2510step1Labels raw2510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3900 node3900Labels := by rfl

def raw2511 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2511step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2511step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2511 raw2511Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw2511 raw2511Labels = mixedMoment B raw2511step0 raw2511step0Labels := by
      have ha : raw2511step0 = (fun i j => raw2511 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2511step0 raw2511; decide +kernel
      have hl : raw2511step0Labels = raw2511Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2511 raw2511Labels permutation152 permutation4
    mixedMoment B raw2511step0 raw2511step0Labels = mixedMoment B raw2511step1 raw2511step1Labels := by
      have ha : raw2511step1 = raw2511step0 := by apply Matrix.ext; unfold raw2511step1 raw2511step0; decide +kernel
      have hl : raw2511step0Labels = labelEmbedding7 ∘ raw2511step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2511step0 raw2511step0Labels raw2511step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw2512 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2512 raw2512Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw2512 raw2512Labels = mixedMoment B raw2512step0 raw2512step0Labels := by
      have ha : raw2512step0 = (fun i j => raw2512 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2512step0 raw2512; decide +kernel
      have hl : raw2512step0Labels = raw2512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2512 raw2512Labels permutation152 permutation4
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw2513 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw2513Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw2513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2513 raw2513Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw2513 raw2513Labels = mixedMoment B raw2513step0 raw2513step0Labels := by
      have ha : raw2513step0 = (fun i j => raw2513 (permutation662 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2513step0 raw2513; decide +kernel
      have hl : raw2513step0Labels = raw2513Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2513 raw2513Labels permutation662 permutation6
    mixedMoment B raw2513step0 raw2513step0Labels = mixedMoment B raw2513step1 raw2513step1Labels := by
      have ha : raw2513step1 = raw2513step0 := by apply Matrix.ext; unfold raw2513step1 raw2513step0; decide +kernel
      have hl : raw2513step0Labels = labelEmbedding1 ∘ raw2513step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2513step0 raw2513step0Labels raw2513step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw2514 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2514step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2514step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2514 raw2514Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw2514 raw2514Labels = mixedMoment B raw2514step0 raw2514step0Labels := by
      have ha : raw2514step0 = (fun i j => raw2514 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2514step0 raw2514; decide +kernel
      have hl : raw2514step0Labels = raw2514Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2514 raw2514Labels permutation152 permutation4
    mixedMoment B raw2514step0 raw2514step0Labels = mixedMoment B raw2514step1 raw2514step1Labels := by
      have ha : raw2514step1 = raw2514step0 := by apply Matrix.ext; unfold raw2514step1 raw2514step0; decide +kernel
      have hl : raw2514step0Labels = labelEmbedding7 ∘ raw2514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2514step0 raw2514step0Labels raw2514step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw2515 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw2515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2515 raw2515Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw2515 raw2515Labels = mixedMoment B raw2515step0 raw2515step0Labels := by
      have ha : raw2515step0 = (fun i j => raw2515 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2515step0 raw2515; decide +kernel
      have hl : raw2515step0Labels = raw2515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2515 raw2515Labels permutation152 permutation4
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw2516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw2516Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw2516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2516step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw2516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2516 raw2516Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw2516 raw2516Labels = mixedMoment B raw2516step0 raw2516step0Labels := by
      have ha : raw2516step0 = (fun i j => raw2516 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2516step0 raw2516; decide +kernel
      have hl : raw2516step0Labels = raw2516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2516 raw2516Labels permutation176 permutation6
    mixedMoment B raw2516step0 raw2516step0Labels = mixedMoment B raw2516step1 raw2516step1Labels := by
      have ha : raw2516step1 = -raw2516step0 := by apply Matrix.ext; change ∀ i j, raw2516step1 i j = -(raw2516step0 i j); unfold raw2516step1 raw2516step0; decide +kernel
      have hl : raw2516step1Labels = raw2516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2516step1 raw2516step1Labels = mixedMoment B raw2516step2 raw2516step2Labels := by
      have ha : raw2516step2 = raw2516step1 := by apply Matrix.ext; unfold raw2516step2 raw2516step1; decide +kernel
      have hl : raw2516step1Labels = labelEmbedding1 ∘ raw2516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2516step1 raw2516step1Labels raw2516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw2517 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2517step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2517step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2517 raw2517Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw2517 raw2517Labels = mixedMoment B raw2517step0 raw2517step0Labels := by
      have ha : raw2517step0 = (fun i j => raw2517 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2517step0 raw2517; decide +kernel
      have hl : raw2517step0Labels = raw2517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2517 raw2517Labels permutation32 permutation4
    mixedMoment B raw2517step0 raw2517step0Labels = mixedMoment B raw2517step1 raw2517step1Labels := by
      have ha : raw2517step1 = raw2517step0 := by apply Matrix.ext; unfold raw2517step1 raw2517step0; decide +kernel
      have hl : raw2517step0Labels = labelEmbedding7 ∘ raw2517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2517step0 raw2517step0Labels raw2517step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw2518 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2518 raw2518Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2518 raw2518Labels = mixedMoment B raw2518step0 raw2518step0Labels := by
      have ha : raw2518step0 = (fun i j => raw2518 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2518step0 raw2518; decide +kernel
      have hl : raw2518step0Labels = raw2518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2518 raw2518Labels permutation32 permutation4
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw2519 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw2519Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw2519step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw2519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2519 raw2519Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw2519 raw2519Labels = mixedMoment B raw2519step0 raw2519step0Labels := by
      have ha : raw2519step0 = (fun i j => raw2519 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2519step0 raw2519; decide +kernel
      have hl : raw2519step0Labels = raw2519Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2519 raw2519Labels permutation39 permutation6
    mixedMoment B raw2519step0 raw2519step0Labels = mixedMoment B raw2519step1 raw2519step1Labels := by
      have ha : raw2519step1 = -raw2519step0 := by apply Matrix.ext; change ∀ i j, raw2519step1 i j = -(raw2519step0 i j); unfold raw2519step1 raw2519step0; decide +kernel
      have hl : raw2519step1Labels = raw2519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2519step1 raw2519step1Labels = mixedMoment B raw2519step2 raw2519step2Labels := by
      have ha : raw2519step2 = raw2519step1 := by apply Matrix.ext; unfold raw2519step2 raw2519step1; decide +kernel
      have hl : raw2519step1Labels = labelEmbedding1 ∘ raw2519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2519step1 raw2519step1Labels raw2519step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw2520 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2520step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2520step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2520 raw2520Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw2520 raw2520Labels = mixedMoment B raw2520step0 raw2520step0Labels := by
      have ha : raw2520step0 = (fun i j => raw2520 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2520step0 raw2520; decide +kernel
      have hl : raw2520step0Labels = raw2520Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2520 raw2520Labels permutation152 permutation4
    mixedMoment B raw2520step0 raw2520step0Labels = mixedMoment B raw2520step1 raw2520step1Labels := by
      have ha : raw2520step1 = raw2520step0 := by apply Matrix.ext; unfold raw2520step1 raw2520step0; decide +kernel
      have hl : raw2520step0Labels = labelEmbedding7 ∘ raw2520step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2520step0 raw2520step0Labels raw2520step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw2521 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2521 raw2521Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw2521 raw2521Labels = mixedMoment B raw2521step0 raw2521step0Labels := by
      have ha : raw2521step0 = (fun i j => raw2521 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2521step0 raw2521; decide +kernel
      have hl : raw2521step0Labels = raw2521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2521 raw2521Labels permutation152 permutation4
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw2522 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2522Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw2522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw2522step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2522 raw2522Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw2522 raw2522Labels = mixedMoment B raw2522step0 raw2522step0Labels := by
      have ha : raw2522step0 = (fun i j => raw2522 (permutation200 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2522step0 raw2522; decide +kernel
      have hl : raw2522step0Labels = raw2522Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2522 raw2522Labels permutation200 permutation6
    mixedMoment B raw2522step0 raw2522step0Labels = mixedMoment B raw2522step1 raw2522step1Labels := by
      have ha : raw2522step1 = -raw2522step0 := by apply Matrix.ext; change ∀ i j, raw2522step1 i j = -(raw2522step0 i j); unfold raw2522step1 raw2522step0; decide +kernel
      have hl : raw2522step1Labels = raw2522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2522step1 raw2522step1Labels = mixedMoment B raw2522step2 raw2522step2Labels := by
      have ha : raw2522step2 = raw2522step1 := by apply Matrix.ext; unfold raw2522step2 raw2522step1; decide +kernel
      have hl : raw2522step1Labels = labelEmbedding1 ∘ raw2522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2522step1 raw2522step1Labels raw2522step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw2523 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2523step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2523 raw2523Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw2523 raw2523Labels = mixedMoment B raw2523step0 raw2523step0Labels := by
      have ha : raw2523step0 = (fun i j => raw2523 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2523step0 raw2523; decide +kernel
      have hl : raw2523step0Labels = raw2523Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2523 raw2523Labels permutation32 permutation4
    mixedMoment B raw2523step0 raw2523step0Labels = mixedMoment B raw2523step1 raw2523step1Labels := by
      have ha : raw2523step1 = raw2523step0 := by apply Matrix.ext; unfold raw2523step1 raw2523step0; decide +kernel
      have hl : raw2523step0Labels = labelEmbedding7 ∘ raw2523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2523step0 raw2523step0Labels raw2523step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw2524 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2524 raw2524Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2524 raw2524Labels = mixedMoment B raw2524step0 raw2524step0Labels := by
      have ha : raw2524step0 = (fun i j => raw2524 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2524step0 raw2524; decide +kernel
      have hl : raw2524step0Labels = raw2524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2524 raw2524Labels permutation32 permutation4
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw2525 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2525Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2525step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2525step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2525 raw2525Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw2525 raw2525Labels = mixedMoment B raw2525step0 raw2525step0Labels := by
      have ha : raw2525step0 = (fun i j => raw2525 (permutation143 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2525step0 raw2525; decide +kernel
      have hl : raw2525step0Labels = raw2525Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2525 raw2525Labels permutation143 permutation6
    mixedMoment B raw2525step0 raw2525step0Labels = mixedMoment B raw2525step1 raw2525step1Labels := by
      have ha : raw2525step1 = raw2525step0 := by apply Matrix.ext; unfold raw2525step1 raw2525step0; decide +kernel
      have hl : raw2525step0Labels = labelEmbedding1 ∘ raw2525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2525step0 raw2525step0Labels raw2525step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw2526 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2526step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2526 raw2526Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw2526 raw2526Labels = mixedMoment B raw2526step0 raw2526step0Labels := by
      have ha : raw2526step0 = (fun i j => raw2526 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2526step0 raw2526; decide +kernel
      have hl : raw2526step0Labels = raw2526Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2526 raw2526Labels permutation152 permutation4
    mixedMoment B raw2526step0 raw2526step0Labels = mixedMoment B raw2526step1 raw2526step1Labels := by
      have ha : raw2526step1 = raw2526step0 := by apply Matrix.ext; unfold raw2526step1 raw2526step0; decide +kernel
      have hl : raw2526step0Labels = labelEmbedding7 ∘ raw2526step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2526step0 raw2526step0Labels raw2526step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw2527 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2527step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2527 raw2527Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw2527 raw2527Labels = mixedMoment B raw2527step0 raw2527step0Labels := by
      have ha : raw2527step0 = (fun i j => raw2527 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2527step0 raw2527; decide +kernel
      have hl : raw2527step0Labels = raw2527Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2527 raw2527Labels permutation152 permutation4
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw2528 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2528Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw2528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2528step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw2528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2528 raw2528Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw2528 raw2528Labels = mixedMoment B raw2528step0 raw2528step0Labels := by
      have ha : raw2528step0 = (fun i j => raw2528 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2528step0 raw2528; decide +kernel
      have hl : raw2528step0Labels = raw2528Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2528 raw2528Labels permutation160 permutation6
    mixedMoment B raw2528step0 raw2528step0Labels = mixedMoment B raw2528step1 raw2528step1Labels := by
      have ha : raw2528step1 = -raw2528step0 := by apply Matrix.ext; change ∀ i j, raw2528step1 i j = -(raw2528step0 i j); unfold raw2528step1 raw2528step0; decide +kernel
      have hl : raw2528step1Labels = raw2528step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2528step1 raw2528step1Labels = mixedMoment B raw2528step2 raw2528step2Labels := by
      have ha : raw2528step2 = raw2528step1 := by apply Matrix.ext; unfold raw2528step2 raw2528step1; decide +kernel
      have hl : raw2528step1Labels = labelEmbedding1 ∘ raw2528step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2528step1 raw2528step1Labels raw2528step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3901 node3901Labels := by rfl

def raw2529 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2529step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2529step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2529 raw2529Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw2529 raw2529Labels = mixedMoment B raw2529step0 raw2529step0Labels := by
      have ha : raw2529step0 = (fun i j => raw2529 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2529step0 raw2529; decide +kernel
      have hl : raw2529step0Labels = raw2529Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2529 raw2529Labels permutation32 permutation4
    mixedMoment B raw2529step0 raw2529step0Labels = mixedMoment B raw2529step1 raw2529step1Labels := by
      have ha : raw2529step1 = raw2529step0 := by apply Matrix.ext; unfold raw2529step1 raw2529step0; decide +kernel
      have hl : raw2529step0Labels = labelEmbedding7 ∘ raw2529step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2529step0 raw2529step0Labels raw2529step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw2530 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2530 raw2530Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw2530 raw2530Labels = mixedMoment B raw2530step0 raw2530step0Labels := by
      have ha : raw2530step0 = (fun i j => raw2530 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2530step0 raw2530; decide +kernel
      have hl : raw2530step0Labels = raw2530Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2530 raw2530Labels permutation32 permutation4
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw2531 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2531Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw2531step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw2531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2531 raw2531Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw2531 raw2531Labels = mixedMoment B raw2531step0 raw2531step0Labels := by
      have ha : raw2531step0 = (fun i j => raw2531 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2531step0 raw2531; decide +kernel
      have hl : raw2531step0Labels = raw2531Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2531 raw2531Labels permutation34 permutation6
    mixedMoment B raw2531step0 raw2531step0Labels = mixedMoment B raw2531step1 raw2531step1Labels := by
      have ha : raw2531step1 = -raw2531step0 := by apply Matrix.ext; change ∀ i j, raw2531step1 i j = -(raw2531step0 i j); unfold raw2531step1 raw2531step0; decide +kernel
      have hl : raw2531step1Labels = raw2531step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2531step1 raw2531step1Labels = mixedMoment B raw2531step2 raw2531step2Labels := by
      have ha : raw2531step2 = raw2531step1 := by apply Matrix.ext; unfold raw2531step2 raw2531step1; decide +kernel
      have hl : raw2531step1Labels = labelEmbedding1 ∘ raw2531step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2531step1 raw2531step1Labels raw2531step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3903 node3903Labels := by rfl

def raw2532 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2532step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2532 raw2532Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw2532 raw2532Labels = mixedMoment B raw2532step0 raw2532step0Labels := by
      have ha : raw2532step0 = (fun i j => raw2532 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2532step0 raw2532; decide +kernel
      have hl : raw2532step0Labels = raw2532Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2532 raw2532Labels permutation32 permutation4
    mixedMoment B raw2532step0 raw2532step0Labels = mixedMoment B raw2532step1 raw2532step1Labels := by
      have ha : raw2532step1 = raw2532step0 := by apply Matrix.ext; unfold raw2532step1 raw2532step0; decide +kernel
      have hl : raw2532step0Labels = labelEmbedding7 ∘ raw2532step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2532step0 raw2532step0Labels raw2532step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw2533 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw2533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2533 raw2533Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw2533 raw2533Labels = mixedMoment B raw2533step0 raw2533step0Labels := by
      have ha : raw2533step0 = (fun i j => raw2533 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2533step0 raw2533; decide +kernel
      have hl : raw2533step0Labels = raw2533Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2533 raw2533Labels permutation32 permutation4
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw2534 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw2534Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw2534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2534 raw2534Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw2534 raw2534Labels = mixedMoment B raw2534step0 raw2534step0Labels := by
      have ha : raw2534step0 = (fun i j => raw2534 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2534step0 raw2534; decide +kernel
      have hl : raw2534step0Labels = raw2534Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2534 raw2534Labels permutation147 permutation3
    mixedMoment B raw2534step0 raw2534step0Labels = mixedMoment B raw2534step1 raw2534step1Labels := by
      have ha : raw2534step1 = raw2534step0 := by apply Matrix.ext; unfold raw2534step1 raw2534step0; decide +kernel
      have hl : raw2534step0Labels = labelEmbedding1 ∘ raw2534step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2534step0 raw2534step0Labels raw2534step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3906 node3906Labels := by rfl

def raw2535 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2535step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2535 raw2535Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw2535 raw2535Labels = mixedMoment B raw2535step0 raw2535step0Labels := by
      have ha : raw2535step0 = (fun i j => raw2535 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2535step0 raw2535; decide +kernel
      have hl : raw2535step0Labels = raw2535Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2535 raw2535Labels permutation152 permutation5
    mixedMoment B raw2535step0 raw2535step0Labels = mixedMoment B raw2535step1 raw2535step1Labels := by
      have ha : raw2535step1 = raw2535step0 := by apply Matrix.ext; unfold raw2535step1 raw2535step0; decide +kernel
      have hl : raw2535step0Labels = labelEmbedding8 ∘ raw2535step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2535step0 raw2535step0Labels raw2535step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw2536 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2536step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2536 raw2536Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw2536 raw2536Labels = mixedMoment B raw2536step0 raw2536step0Labels := by
      have ha : raw2536step0 = (fun i j => raw2536 (permutation373 i) (permutation2 j)) := by apply Matrix.ext; unfold raw2536step0 raw2536; decide +kernel
      have hl : raw2536step0Labels = raw2536Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2536 raw2536Labels permutation373 permutation2
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw2537 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2537Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw2537step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2537step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw2537step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2537 raw2537Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw2537 raw2537Labels = mixedMoment B raw2537step0 raw2537step0Labels := by
      have ha : raw2537step0 = (fun i j => raw2537 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2537step0 raw2537; decide +kernel
      have hl : raw2537step0Labels = raw2537Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2537 raw2537Labels permutation161 permutation3
    mixedMoment B raw2537step0 raw2537step0Labels = mixedMoment B raw2537step1 raw2537step1Labels := by
      have ha : raw2537step1 = -raw2537step0 := by apply Matrix.ext; change ∀ i j, raw2537step1 i j = -(raw2537step0 i j); unfold raw2537step1 raw2537step0; decide +kernel
      have hl : raw2537step1Labels = raw2537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2537step1 raw2537step1Labels = mixedMoment B raw2537step2 raw2537step2Labels := by
      have ha : raw2537step2 = raw2537step1 := by apply Matrix.ext; unfold raw2537step2 raw2537step1; decide +kernel
      have hl : raw2537step1Labels = labelEmbedding1 ∘ raw2537step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2537step1 raw2537step1Labels raw2537step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw2538 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2538step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2538 raw2538Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw2538 raw2538Labels = mixedMoment B raw2538step0 raw2538step0Labels := by
      have ha : raw2538step0 = (fun i j => raw2538 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2538step0 raw2538; decide +kernel
      have hl : raw2538step0Labels = raw2538Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2538 raw2538Labels permutation32 permutation4
    mixedMoment B raw2538step0 raw2538step0Labels = mixedMoment B raw2538step1 raw2538step1Labels := by
      have ha : raw2538step1 = raw2538step0 := by apply Matrix.ext; unfold raw2538step1 raw2538step0; decide +kernel
      have hl : raw2538step0Labels = labelEmbedding7 ∘ raw2538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2538step0 raw2538step0Labels raw2538step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw2539 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw2539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2539 raw2539Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw2539 raw2539Labels = mixedMoment B raw2539step0 raw2539step0Labels := by
      have ha : raw2539step0 = (fun i j => raw2539 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2539step0 raw2539; decide +kernel
      have hl : raw2539step0Labels = raw2539Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2539 raw2539Labels permutation32 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw2540 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2]]
def raw2540Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw2540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw2540step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2540 raw2540Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw2540 raw2540Labels = mixedMoment B raw2540step0 raw2540step0Labels := by
      have ha : raw2540step0 = (fun i j => raw2540 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2540step0 raw2540; decide +kernel
      have hl : raw2540step0Labels = raw2540Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2540 raw2540Labels permutation38 permutation6
    mixedMoment B raw2540step0 raw2540step0Labels = mixedMoment B raw2540step1 raw2540step1Labels := by
      have ha : raw2540step1 = -raw2540step0 := by apply Matrix.ext; change ∀ i j, raw2540step1 i j = -(raw2540step0 i j); unfold raw2540step1 raw2540step0; decide +kernel
      have hl : raw2540step1Labels = raw2540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2540step1 raw2540step1Labels = mixedMoment B raw2540step2 raw2540step2Labels := by
      have ha : raw2540step2 = raw2540step1 := by apply Matrix.ext; unfold raw2540step2 raw2540step1; decide +kernel
      have hl : raw2540step1Labels = labelEmbedding1 ∘ raw2540step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2540step1 raw2540step1Labels raw2540step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw2541 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2541step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2541 raw2541Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw2541 raw2541Labels = mixedMoment B raw2541step0 raw2541step0Labels := by
      have ha : raw2541step0 = (fun i j => raw2541 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2541step0 raw2541; decide +kernel
      have hl : raw2541step0Labels = raw2541Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2541 raw2541Labels permutation32 permutation4
    mixedMoment B raw2541step0 raw2541step0Labels = mixedMoment B raw2541step1 raw2541step1Labels := by
      have ha : raw2541step1 = raw2541step0 := by apply Matrix.ext; unfold raw2541step1 raw2541step0; decide +kernel
      have hl : raw2541step0Labels = labelEmbedding7 ∘ raw2541step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2541step0 raw2541step0Labels raw2541step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw2542 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2542Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw2542step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2542 raw2542Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw2542 raw2542Labels = mixedMoment B raw2542step0 raw2542step0Labels := by
      have ha : raw2542step0 = (fun i j => raw2542 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2542step0 raw2542; decide +kernel
      have hl : raw2542step0Labels = raw2542Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2542 raw2542Labels permutation32 permutation4
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw2543 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2]]
def raw2543Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw2543step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw2543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2543 raw2543Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw2543 raw2543Labels = mixedMoment B raw2543step0 raw2543step0Labels := by
      have ha : raw2543step0 = (fun i j => raw2543 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2543step0 raw2543; decide +kernel
      have hl : raw2543step0Labels = raw2543Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2543 raw2543Labels permutation32 permutation6
    mixedMoment B raw2543step0 raw2543step0Labels = mixedMoment B raw2543step1 raw2543step1Labels := by
      have ha : raw2543step1 = -raw2543step0 := by apply Matrix.ext; change ∀ i j, raw2543step1 i j = -(raw2543step0 i j); unfold raw2543step1 raw2543step0; decide +kernel
      have hl : raw2543step1Labels = raw2543step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2543step1 raw2543step1Labels = mixedMoment B raw2543step2 raw2543step2Labels := by
      have ha : raw2543step2 = raw2543step1 := by apply Matrix.ext; unfold raw2543step2 raw2543step1; decide +kernel
      have hl : raw2543step1Labels = labelEmbedding1 ∘ raw2543step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2543step1 raw2543step1Labels raw2543step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw2544 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0]]
def raw2544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2544step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2544step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2544 raw2544Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw2544 raw2544Labels = mixedMoment B raw2544step0 raw2544step0Labels := by
      have ha : raw2544step0 = (fun i j => raw2544 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2544step0 raw2544; decide +kernel
      have hl : raw2544step0Labels = raw2544Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2544 raw2544Labels permutation8 permutation4
    mixedMoment B raw2544step0 raw2544step0Labels = mixedMoment B raw2544step1 raw2544step1Labels := by
      have ha : raw2544step1 = raw2544step0 := by apply Matrix.ext; unfold raw2544step1 raw2544step0; decide +kernel
      have hl : raw2544step0Labels = labelEmbedding7 ∘ raw2544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2544step0 raw2544step0Labels raw2544step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw2545 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0]]
def raw2545Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2545step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw2545step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2545 raw2545Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw2545 raw2545Labels = mixedMoment B raw2545step0 raw2545step0Labels := by
      have ha : raw2545step0 = (fun i j => raw2545 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2545step0 raw2545; decide +kernel
      have hl : raw2545step0Labels = raw2545Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2545 raw2545Labels permutation8 permutation4
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw2546 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![-2, 2, 0]]
def raw2546Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw2546step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw2546step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw2546step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2546 raw2546Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw2546 raw2546Labels = mixedMoment B raw2546step0 raw2546step0Labels := by
      have ha : raw2546step0 = (fun i j => raw2546 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2546step0 raw2546; decide +kernel
      have hl : raw2546step0Labels = raw2546Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2546 raw2546Labels permutation9 permutation6
    mixedMoment B raw2546step0 raw2546step0Labels = mixedMoment B raw2546step1 raw2546step1Labels := by
      have ha : raw2546step1 = -raw2546step0 := by apply Matrix.ext; change ∀ i j, raw2546step1 i j = -(raw2546step0 i j); unfold raw2546step1 raw2546step0; decide +kernel
      have hl : raw2546step1Labels = raw2546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2546step1 raw2546step1Labels = mixedMoment B raw2546step2 raw2546step2Labels := by
      have ha : raw2546step2 = raw2546step1 := by apply Matrix.ext; unfold raw2546step2 raw2546step1; decide +kernel
      have hl : raw2546step1Labels = labelEmbedding1 ∘ raw2546step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2546step1 raw2546step1Labels raw2546step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw2547 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2547step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw2547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw2547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2547 raw2547Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw2547 raw2547Labels = mixedMoment B raw2547step0 raw2547step0Labels := by
      have ha : raw2547step0 = (fun i j => raw2547 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw2547step0 raw2547; decide +kernel
      have hl : raw2547step0Labels = raw2547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2547 raw2547Labels permutation152 permutation5
    mixedMoment B raw2547step0 raw2547step0Labels = mixedMoment B raw2547step1 raw2547step1Labels := by
      have ha : raw2547step1 = raw2547step0 := by apply Matrix.ext; unfold raw2547step1 raw2547step0; decide +kernel
      have hl : raw2547step0Labels = labelEmbedding8 ∘ raw2547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2547step0 raw2547step0Labels raw2547step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw2548 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw2548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2548 raw2548Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw2548 raw2548Labels = mixedMoment B raw2548step0 raw2548step0Labels := by
      have ha : raw2548step0 = (fun i j => raw2548 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2548step0 raw2548; decide +kernel
      have hl : raw2548step0Labels = raw2548Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2548 raw2548Labels permutation152 permutation4
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw2549 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw2549Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw2549step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw2549step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2549step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw2549step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2549 raw2549Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw2549 raw2549Labels = mixedMoment B raw2549step0 raw2549step0Labels := by
      have ha : raw2549step0 = (fun i j => raw2549 (permutation216 i) (permutation3 j)) := by apply Matrix.ext; unfold raw2549step0 raw2549; decide +kernel
      have hl : raw2549step0Labels = raw2549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2549 raw2549Labels permutation216 permutation3
    mixedMoment B raw2549step0 raw2549step0Labels = mixedMoment B raw2549step1 raw2549step1Labels := by
      have ha : raw2549step1 = -raw2549step0 := by apply Matrix.ext; change ∀ i j, raw2549step1 i j = -(raw2549step0 i j); unfold raw2549step1 raw2549step0; decide +kernel
      have hl : raw2549step1Labels = raw2549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2549step1 raw2549step1Labels = mixedMoment B raw2549step2 raw2549step2Labels := by
      have ha : raw2549step2 = raw2549step1 := by apply Matrix.ext; unfold raw2549step2 raw2549step1; decide +kernel
      have hl : raw2549step1Labels = labelEmbedding1 ∘ raw2549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2549step1 raw2549step1Labels raw2549step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw2550 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2550step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2550 raw2550Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw2550 raw2550Labels = mixedMoment B raw2550step0 raw2550step0Labels := by
      have ha : raw2550step0 = (fun i j => raw2550 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2550step0 raw2550; decide +kernel
      have hl : raw2550step0Labels = raw2550Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2550 raw2550Labels permutation32 permutation4
    mixedMoment B raw2550step0 raw2550step0Labels = mixedMoment B raw2550step1 raw2550step1Labels := by
      have ha : raw2550step1 = raw2550step0 := by apply Matrix.ext; unfold raw2550step1 raw2550step0; decide +kernel
      have hl : raw2550step0Labels = labelEmbedding7 ∘ raw2550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2550step0 raw2550step0Labels raw2550step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw2551 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2551 raw2551Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw2551 raw2551Labels = mixedMoment B raw2551step0 raw2551step0Labels := by
      have ha : raw2551step0 = (fun i j => raw2551 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2551step0 raw2551; decide +kernel
      have hl : raw2551step0Labels = raw2551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2551 raw2551Labels permutation32 permutation4
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw2552 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1]]
def raw2552Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw2552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2552step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2552step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2552step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw2552step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2552 raw2552Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw2552 raw2552Labels = mixedMoment B raw2552step0 raw2552step0Labels := by
      have ha : raw2552step0 = (fun i j => raw2552 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2552step0 raw2552; decide +kernel
      have hl : raw2552step0Labels = raw2552Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2552 raw2552Labels permutation38 permutation6
    mixedMoment B raw2552step0 raw2552step0Labels = mixedMoment B raw2552step1 raw2552step1Labels := by
      have ha : raw2552step1 = -raw2552step0 := by apply Matrix.ext; change ∀ i j, raw2552step1 i j = -(raw2552step0 i j); unfold raw2552step1 raw2552step0; decide +kernel
      have hl : raw2552step1Labels = raw2552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2552step1 raw2552step1Labels = mixedMoment B raw2552step2 raw2552step2Labels := by
      have ha : raw2552step2 = raw2552step1 := by apply Matrix.ext; unfold raw2552step2 raw2552step1; decide +kernel
      have hl : raw2552step1Labels = labelEmbedding1 ∘ raw2552step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2552step1 raw2552step1Labels raw2552step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw2553 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2553step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2553step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2553step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2553 raw2553Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw2553 raw2553Labels = mixedMoment B raw2553step0 raw2553step0Labels := by
      have ha : raw2553step0 = (fun i j => raw2553 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2553step0 raw2553; decide +kernel
      have hl : raw2553step0Labels = raw2553Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2553 raw2553Labels permutation8 permutation4
    mixedMoment B raw2553step0 raw2553step0Labels = mixedMoment B raw2553step1 raw2553step1Labels := by
      have ha : raw2553step1 = raw2553step0 := by apply Matrix.ext; unfold raw2553step1 raw2553step0; decide +kernel
      have hl : raw2553step0Labels = labelEmbedding7 ∘ raw2553step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2553step0 raw2553step0Labels raw2553step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

def raw2554 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2554step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2554 raw2554Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw2554 raw2554Labels = mixedMoment B raw2554step0 raw2554step0Labels := by
      have ha : raw2554step0 = (fun i j => raw2554 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2554step0 raw2554; decide +kernel
      have hl : raw2554step0Labels = raw2554Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2554 raw2554Labels permutation8 permutation4
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw2555 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw2555Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2555step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2555step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2555step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw2555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2555 raw2555Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw2555 raw2555Labels = mixedMoment B raw2555step0 raw2555step0Labels := by
      have ha : raw2555step0 = (fun i j => raw2555 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2555step0 raw2555; decide +kernel
      have hl : raw2555step0Labels = raw2555Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2555 raw2555Labels permutation29 permutation6
    mixedMoment B raw2555step0 raw2555step0Labels = mixedMoment B raw2555step1 raw2555step1Labels := by
      have ha : raw2555step1 = raw2555step0 := by apply Matrix.ext; unfold raw2555step1 raw2555step0; decide +kernel
      have hl : raw2555step0Labels = labelEmbedding1 ∘ raw2555step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2555step0 raw2555step0Labels raw2555step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw2556 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2556step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2556 raw2556Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw2556 raw2556Labels = mixedMoment B raw2556step0 raw2556step0Labels := by
      have ha : raw2556step0 = (fun i j => raw2556 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2556step0 raw2556; decide +kernel
      have hl : raw2556step0Labels = raw2556Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2556 raw2556Labels permutation32 permutation4
    mixedMoment B raw2556step0 raw2556step0Labels = mixedMoment B raw2556step1 raw2556step1Labels := by
      have ha : raw2556step1 = raw2556step0 := by apply Matrix.ext; unfold raw2556step1 raw2556step0; decide +kernel
      have hl : raw2556step0Labels = labelEmbedding7 ∘ raw2556step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2556step0 raw2556step0Labels raw2556step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw2557 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw2557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw2557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2557 raw2557Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw2557 raw2557Labels = mixedMoment B raw2557step0 raw2557step0Labels := by
      have ha : raw2557step0 = (fun i j => raw2557 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2557step0 raw2557; decide +kernel
      have hl : raw2557step0Labels = raw2557Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2557 raw2557Labels permutation32 permutation4
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw2558 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1]]
def raw2558Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw2558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw2558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2558step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw2558step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw2558step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical2558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2558 raw2558Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw2558 raw2558Labels = mixedMoment B raw2558step0 raw2558step0Labels := by
      have ha : raw2558step0 = (fun i j => raw2558 (permutation40 i) (permutation6 j)) := by apply Matrix.ext; unfold raw2558step0 raw2558; decide +kernel
      have hl : raw2558step0Labels = raw2558Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2558 raw2558Labels permutation40 permutation6
    mixedMoment B raw2558step0 raw2558step0Labels = mixedMoment B raw2558step1 raw2558step1Labels := by
      have ha : raw2558step1 = -raw2558step0 := by apply Matrix.ext; change ∀ i j, raw2558step1 i j = -(raw2558step0 i j); unfold raw2558step1 raw2558step0; decide +kernel
      have hl : raw2558step1Labels = raw2558step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw2558step1 raw2558step1Labels = mixedMoment B raw2558step2 raw2558step2Labels := by
      have ha : raw2558step2 = raw2558step1 := by apply Matrix.ext; unfold raw2558step2 raw2558step1; decide +kernel
      have hl : raw2558step1Labels = labelEmbedding1 ∘ raw2558step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2558step1 raw2558step1Labels raw2558step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw2559 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw2559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw2559step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2559step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw2559step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw2559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical2559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw2559 raw2559Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw2559 raw2559Labels = mixedMoment B raw2559step0 raw2559step0Labels := by
      have ha : raw2559step0 = (fun i j => raw2559 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw2559step0 raw2559; decide +kernel
      have hl : raw2559step0Labels = raw2559Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw2559 raw2559Labels permutation8 permutation4
    mixedMoment B raw2559step0 raw2559step0Labels = mixedMoment B raw2559step1 raw2559step1Labels := by
      have ha : raw2559step1 = raw2559step0 := by apply Matrix.ext; unfold raw2559step1 raw2559step0; decide +kernel
      have hl : raw2559step0Labels = labelEmbedding7 ∘ raw2559step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw2559step0 raw2559step0Labels raw2559step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
