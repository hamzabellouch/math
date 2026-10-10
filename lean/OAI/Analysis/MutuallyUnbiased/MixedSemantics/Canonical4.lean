import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes7
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw512 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw512 raw512Labels = mixedMoment B node3823 node3823Labels := by
  calc
    mixedMoment B raw512 raw512Labels = mixedMoment B raw512step0 raw512step0Labels := by
      have ha : raw512step0 = (fun i j => raw512 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw512step0 raw512; decide +kernel
      have hl : raw512step0Labels = raw512Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw512 raw512Labels permutation152 permutation5
    mixedMoment B raw512step0 raw512step0Labels = mixedMoment B raw512step1 raw512step1Labels := by
      have ha : raw512step1 = raw512step0 := by apply Matrix.ext; unfold raw512step1 raw512step0; decide +kernel
      have hl : raw512step0Labels = labelEmbedding1 ∘ raw512step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw512step0 raw512step0Labels raw512step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3823 node3823Labels := by rfl

def raw513 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw513Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw513step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw513step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw513 raw513Labels = mixedMoment B node473 node473Labels := by
  calc
    mixedMoment B raw513 raw513Labels = mixedMoment B raw513step0 raw513step0Labels := by
      have ha : raw513step0 = (fun i j => raw513 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw513step0 raw513; decide +kernel
      have hl : raw513step0Labels = raw513Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw513 raw513Labels permutation662 permutation4
    mixedMoment B raw513step0 raw513step0Labels = mixedMoment B raw513step1 raw513step1Labels := by
      have ha : raw513step1 = -raw513step0 := by apply Matrix.ext; change ∀ i j, raw513step1 i j = -(raw513step0 i j); unfold raw513step1 raw513step0; decide +kernel
      have hl : raw513step1Labels = raw513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node473 node473Labels := by rfl

def raw514 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw514 raw514Labels = mixedMoment B node3824 node3824Labels := by
  calc
    mixedMoment B raw514 raw514Labels = mixedMoment B raw514step0 raw514step0Labels := by
      have ha : raw514step0 = (fun i j => raw514 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw514step0 raw514; decide +kernel
      have hl : raw514step0Labels = raw514Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw514 raw514Labels permutation32 permutation5
    mixedMoment B raw514step0 raw514step0Labels = mixedMoment B raw514step1 raw514step1Labels := by
      have ha : raw514step1 = raw514step0 := by apply Matrix.ext; unfold raw514step1 raw514step0; decide +kernel
      have hl : raw514step0Labels = labelEmbedding1 ∘ raw514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw514step0 raw514step0Labels raw514step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3824 node3824Labels := by rfl

def raw515 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw515Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw515step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw515 raw515Labels = mixedMoment B node474 node474Labels := by
  calc
    mixedMoment B raw515 raw515Labels = mixedMoment B raw515step0 raw515step0Labels := by
      have ha : raw515step0 = (fun i j => raw515 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw515step0 raw515; decide +kernel
      have hl : raw515step0Labels = raw515Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw515 raw515Labels permutation32 permutation5
    _ = mixedMoment B node474 node474Labels := by rfl

def raw516 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw516 raw516Labels = mixedMoment B node3829 node3829Labels := by
  calc
    mixedMoment B raw516 raw516Labels = mixedMoment B raw516step0 raw516step0Labels := by
      have ha : raw516step0 = (fun i j => raw516 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw516step0 raw516; decide +kernel
      have hl : raw516step0Labels = raw516Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw516 raw516Labels permutation152 permutation5
    mixedMoment B raw516step0 raw516step0Labels = mixedMoment B raw516step1 raw516step1Labels := by
      have ha : raw516step1 = raw516step0 := by apply Matrix.ext; unfold raw516step1 raw516step0; decide +kernel
      have hl : raw516step0Labels = labelEmbedding1 ∘ raw516step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw516step0 raw516step0Labels raw516step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3829 node3829Labels := by rfl

def raw517 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw517Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw517step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw517 raw517Labels = mixedMoment B node477 node477Labels := by
  calc
    mixedMoment B raw517 raw517Labels = mixedMoment B raw517step0 raw517step0Labels := by
      have ha : raw517step0 = (fun i j => raw517 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw517step0 raw517; decide +kernel
      have hl : raw517step0Labels = raw517Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw517 raw517Labels permutation152 permutation5
    _ = mixedMoment B node477 node477Labels := by rfl

def raw518 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw518step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw518 raw518Labels = mixedMoment B node3830 node3830Labels := by
  calc
    mixedMoment B raw518 raw518Labels = mixedMoment B raw518step0 raw518step0Labels := by
      have ha : raw518step0 = (fun i j => raw518 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw518step0 raw518; decide +kernel
      have hl : raw518step0Labels = raw518Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw518 raw518Labels permutation152 permutation5
    mixedMoment B raw518step0 raw518step0Labels = mixedMoment B raw518step1 raw518step1Labels := by
      have ha : raw518step1 = raw518step0 := by apply Matrix.ext; unfold raw518step1 raw518step0; decide +kernel
      have hl : raw518step0Labels = labelEmbedding1 ∘ raw518step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw518step0 raw518step0Labels raw518step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3830 node3830Labels := by rfl

def raw519 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw519Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw519step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw519step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw519 raw519Labels = mixedMoment B node455 node455Labels := by
  calc
    mixedMoment B raw519 raw519Labels = mixedMoment B raw519step0 raw519step0Labels := by
      have ha : raw519step0 = (fun i j => raw519 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw519step0 raw519; decide +kernel
      have hl : raw519step0Labels = raw519Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw519 raw519Labels permutation662 permutation4
    mixedMoment B raw519step0 raw519step0Labels = mixedMoment B raw519step1 raw519step1Labels := by
      have ha : raw519step1 = -raw519step0 := by apply Matrix.ext; change ∀ i j, raw519step1 i j = -(raw519step0 i j); unfold raw519step1 raw519step0; decide +kernel
      have hl : raw519step1Labels = raw519step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node455 node455Labels := by rfl

def raw520 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw520 raw520Labels = mixedMoment B node3831 node3831Labels := by
  calc
    mixedMoment B raw520 raw520Labels = mixedMoment B raw520step0 raw520step0Labels := by
      have ha : raw520step0 = (fun i j => raw520 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw520step0 raw520; decide +kernel
      have hl : raw520step0Labels = raw520Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw520 raw520Labels permutation32 permutation5
    mixedMoment B raw520step0 raw520step0Labels = mixedMoment B raw520step1 raw520step1Labels := by
      have ha : raw520step1 = raw520step0 := by apply Matrix.ext; unfold raw520step1 raw520step0; decide +kernel
      have hl : raw520step0Labels = labelEmbedding1 ∘ raw520step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw520step0 raw520step0Labels raw520step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3831 node3831Labels := by rfl

def raw521 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, -1, 2], ![0, 2, -2], ![-1, 2, -1]]
def raw521Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw521step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw521step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw521 raw521Labels = mixedMoment B node438 node438Labels := by
  calc
    mixedMoment B raw521 raw521Labels = mixedMoment B raw521step0 raw521step0Labels := by
      have ha : raw521step0 = (fun i j => raw521 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw521step0 raw521; decide +kernel
      have hl : raw521step0Labels = raw521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw521 raw521Labels permutation125 permutation4
    mixedMoment B raw521step0 raw521step0Labels = mixedMoment B raw521step1 raw521step1Labels := by
      have ha : raw521step1 = -raw521step0 := by apply Matrix.ext; change ∀ i j, raw521step1 i j = -(raw521step0 i j); unfold raw521step1 raw521step0; decide +kernel
      have hl : raw521step1Labels = raw521step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node438 node438Labels := by rfl

def raw522 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw522step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw522step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw522 raw522Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw522 raw522Labels = mixedMoment B raw522step0 raw522step0Labels := by
      have ha : raw522step0 = (fun i j => raw522 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw522step0 raw522; decide +kernel
      have hl : raw522step0Labels = raw522Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw522 raw522Labels permutation152 permutation5
    mixedMoment B raw522step0 raw522step0Labels = mixedMoment B raw522step1 raw522step1Labels := by
      have ha : raw522step1 = raw522step0 := by apply Matrix.ext; unfold raw522step1 raw522step0; decide +kernel
      have hl : raw522step0Labels = labelEmbedding1 ∘ raw522step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw522step0 raw522step0Labels raw522step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw523 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw523Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw523step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw523step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw523 raw523Labels = mixedMoment B node462 node462Labels := by
  calc
    mixedMoment B raw523 raw523Labels = mixedMoment B raw523step0 raw523step0Labels := by
      have ha : raw523step0 = (fun i j => raw523 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw523step0 raw523; decide +kernel
      have hl : raw523step0Labels = raw523Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw523 raw523Labels permutation682 permutation4
    mixedMoment B raw523step0 raw523step0Labels = mixedMoment B raw523step1 raw523step1Labels := by
      have ha : raw523step1 = -raw523step0 := by apply Matrix.ext; change ∀ i j, raw523step1 i j = -(raw523step0 i j); unfold raw523step1 raw523step0; decide +kernel
      have hl : raw523step1Labels = raw523step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node462 node462Labels := by rfl

def raw524 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw524step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw524step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw524 raw524Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw524 raw524Labels = mixedMoment B raw524step0 raw524step0Labels := by
      have ha : raw524step0 = (fun i j => raw524 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw524step0 raw524; decide +kernel
      have hl : raw524step0Labels = raw524Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw524 raw524Labels permutation152 permutation5
    mixedMoment B raw524step0 raw524step0Labels = mixedMoment B raw524step1 raw524step1Labels := by
      have ha : raw524step1 = raw524step0 := by apply Matrix.ext; unfold raw524step1 raw524step0; decide +kernel
      have hl : raw524step0Labels = labelEmbedding1 ∘ raw524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw524step0 raw524step0Labels raw524step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw525 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw525Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw525step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw525 raw525Labels = mixedMoment B node488 node488Labels := by
  calc
    mixedMoment B raw525 raw525Labels = mixedMoment B raw525step0 raw525step0Labels := by
      have ha : raw525step0 = (fun i j => raw525 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw525step0 raw525; decide +kernel
      have hl : raw525step0Labels = raw525Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw525 raw525Labels permutation152 permutation5
    _ = mixedMoment B node488 node488Labels := by rfl

def raw526 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw526step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw526step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw526 raw526Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw526 raw526Labels = mixedMoment B raw526step0 raw526step0Labels := by
      have ha : raw526step0 = (fun i j => raw526 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw526step0 raw526; decide +kernel
      have hl : raw526step0Labels = raw526Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw526 raw526Labels permutation32 permutation5
    mixedMoment B raw526step0 raw526step0Labels = mixedMoment B raw526step1 raw526step1Labels := by
      have ha : raw526step1 = raw526step0 := by apply Matrix.ext; unfold raw526step1 raw526step0; decide +kernel
      have hl : raw526step0Labels = labelEmbedding1 ∘ raw526step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw526step0 raw526step0Labels raw526step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw527 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw527Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw527step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw527 raw527Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw527 raw527Labels = mixedMoment B raw527step0 raw527step0Labels := by
      have ha : raw527step0 = (fun i j => raw527 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw527step0 raw527; decide +kernel
      have hl : raw527step0Labels = raw527Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw527 raw527Labels permutation32 permutation5
    _ = mixedMoment B node489 node489Labels := by rfl

def raw528 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw528 raw528Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw528 raw528Labels = mixedMoment B raw528step0 raw528step0Labels := by
      have ha : raw528step0 = (fun i j => raw528 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw528step0 raw528; decide +kernel
      have hl : raw528step0Labels = raw528Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw528 raw528Labels permutation32 permutation5
    mixedMoment B raw528step0 raw528step0Labels = mixedMoment B raw528step1 raw528step1Labels := by
      have ha : raw528step1 = raw528step0 := by apply Matrix.ext; unfold raw528step1 raw528step0; decide +kernel
      have hl : raw528step0Labels = labelEmbedding1 ∘ raw528step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw528step0 raw528step0Labels raw528step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw529 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw529Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw529step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw529step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw529 raw529Labels = mixedMoment B node490 node490Labels := by
  calc
    mixedMoment B raw529 raw529Labels = mixedMoment B raw529step0 raw529step0Labels := by
      have ha : raw529step0 = (fun i j => raw529 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw529step0 raw529; decide +kernel
      have hl : raw529step0Labels = raw529Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw529 raw529Labels permutation151 permutation4
    mixedMoment B raw529step0 raw529step0Labels = mixedMoment B raw529step1 raw529step1Labels := by
      have ha : raw529step1 = -raw529step0 := by apply Matrix.ext; change ∀ i j, raw529step1 i j = -(raw529step0 i j); unfold raw529step1 raw529step0; decide +kernel
      have hl : raw529step1Labels = raw529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node490 node490Labels := by rfl

def raw530 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw530step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw530step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw530 raw530Labels = mixedMoment B node3855 node3855Labels := by
  calc
    mixedMoment B raw530 raw530Labels = mixedMoment B raw530step0 raw530step0Labels := by
      have ha : raw530step0 = (fun i j => raw530 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw530step0 raw530; decide +kernel
      have hl : raw530step0Labels = raw530Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw530 raw530Labels permutation152 permutation5
    mixedMoment B raw530step0 raw530step0Labels = mixedMoment B raw530step1 raw530step1Labels := by
      have ha : raw530step1 = raw530step0 := by apply Matrix.ext; unfold raw530step1 raw530step0; decide +kernel
      have hl : raw530step0Labels = labelEmbedding1 ∘ raw530step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw530step0 raw530step0Labels raw530step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3855 node3855Labels := by rfl

def raw531 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw531Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw531step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw531 raw531Labels = mixedMoment B node492 node492Labels := by
  calc
    mixedMoment B raw531 raw531Labels = mixedMoment B raw531step0 raw531step0Labels := by
      have ha : raw531step0 = (fun i j => raw531 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw531step0 raw531; decide +kernel
      have hl : raw531step0Labels = raw531Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw531 raw531Labels permutation152 permutation5
    _ = mixedMoment B node492 node492Labels := by rfl

def raw532 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw532 raw532Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw532 raw532Labels = mixedMoment B raw532step0 raw532step0Labels := by
      have ha : raw532step0 = (fun i j => raw532 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw532step0 raw532; decide +kernel
      have hl : raw532step0Labels = raw532Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw532 raw532Labels permutation32 permutation5
    mixedMoment B raw532step0 raw532step0Labels = mixedMoment B raw532step1 raw532step1Labels := by
      have ha : raw532step1 = raw532step0 := by apply Matrix.ext; unfold raw532step1 raw532step0; decide +kernel
      have hl : raw532step0Labels = labelEmbedding1 ∘ raw532step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw532step0 raw532step0Labels raw532step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw533 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2]]
def raw533Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw533step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw533step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw533 raw533Labels = mixedMoment B node468 node468Labels := by
  calc
    mixedMoment B raw533 raw533Labels = mixedMoment B raw533step0 raw533step0Labels := by
      have ha : raw533step0 = (fun i j => raw533 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw533step0 raw533; decide +kernel
      have hl : raw533step0Labels = raw533Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw533 raw533Labels permutation151 permutation4
    mixedMoment B raw533step0 raw533step0Labels = mixedMoment B raw533step1 raw533step1Labels := by
      have ha : raw533step1 = -raw533step0 := by apply Matrix.ext; change ∀ i j, raw533step1 i j = -(raw533step0 i j); unfold raw533step1 raw533step0; decide +kernel
      have hl : raw533step1Labels = raw533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node468 node468Labels := by rfl

def raw534 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw534step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw534 raw534Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw534 raw534Labels = mixedMoment B raw534step0 raw534step0Labels := by
      have ha : raw534step0 = (fun i j => raw534 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw534step0 raw534; decide +kernel
      have hl : raw534step0Labels = raw534Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw534 raw534Labels permutation32 permutation5
    mixedMoment B raw534step0 raw534step0Labels = mixedMoment B raw534step1 raw534step1Labels := by
      have ha : raw534step1 = raw534step0 := by apply Matrix.ext; unfold raw534step1 raw534step0; decide +kernel
      have hl : raw534step0Labels = labelEmbedding1 ∘ raw534step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw534step0 raw534step0Labels raw534step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw535 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw535Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw535step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw535 raw535Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw535 raw535Labels = mixedMoment B raw535step0 raw535step0Labels := by
      have ha : raw535step0 = (fun i j => raw535 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw535step0 raw535; decide +kernel
      have hl : raw535step0Labels = raw535Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw535 raw535Labels permutation32 permutation5
    _ = mixedMoment B node494 node494Labels := by rfl

def raw536 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2]]
def raw536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw536step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw536step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw536step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw536step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw536 raw536Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw536 raw536Labels = mixedMoment B raw536step0 raw536step0Labels := by
      have ha : raw536step0 = (fun i j => raw536 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw536step0 raw536; decide +kernel
      have hl : raw536step0Labels = raw536Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw536 raw536Labels permutation8 permutation5
    mixedMoment B raw536step0 raw536step0Labels = mixedMoment B raw536step1 raw536step1Labels := by
      have ha : raw536step1 = raw536step0 := by apply Matrix.ext; unfold raw536step1 raw536step0; decide +kernel
      have hl : raw536step0Labels = labelEmbedding1 ∘ raw536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw536step0 raw536step0Labels raw536step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw537 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2]]
def raw537Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw537step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw537step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw537 raw537Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw537 raw537Labels = mixedMoment B raw537step0 raw537step0Labels := by
      have ha : raw537step0 = (fun i j => raw537 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw537step0 raw537; decide +kernel
      have hl : raw537step0Labels = raw537Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw537 raw537Labels permutation8 permutation5
    _ = mixedMoment B node496 node496Labels := by rfl

def raw538 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw538step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw538step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw538 raw538Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw538 raw538Labels = mixedMoment B raw538step0 raw538step0Labels := by
      have ha : raw538step0 = (fun i j => raw538 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw538step0 raw538; decide +kernel
      have hl : raw538step0Labels = raw538Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw538 raw538Labels permutation152 permutation5
    mixedMoment B raw538step0 raw538step0Labels = mixedMoment B raw538step1 raw538step1Labels := by
      have ha : raw538step1 = raw538step0 := by apply Matrix.ext; unfold raw538step1 raw538step0; decide +kernel
      have hl : raw538step0Labels = labelEmbedding1 ∘ raw538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw538step0 raw538step0Labels raw538step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3882 node3882Labels := by rfl

def raw539 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw539Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw539step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw539 raw539Labels = mixedMoment B node499 node499Labels := by
  calc
    mixedMoment B raw539 raw539Labels = mixedMoment B raw539step0 raw539step0Labels := by
      have ha : raw539step0 = (fun i j => raw539 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw539step0 raw539; decide +kernel
      have hl : raw539step0Labels = raw539Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw539 raw539Labels permutation152 permutation5
    _ = mixedMoment B node499 node499Labels := by rfl

def raw540 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw540step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw540step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw540 raw540Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw540 raw540Labels = mixedMoment B raw540step0 raw540step0Labels := by
      have ha : raw540step0 = (fun i j => raw540 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw540step0 raw540; decide +kernel
      have hl : raw540step0Labels = raw540Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw540 raw540Labels permutation32 permutation5
    mixedMoment B raw540step0 raw540step0Labels = mixedMoment B raw540step1 raw540step1Labels := by
      have ha : raw540step1 = raw540step0 := by apply Matrix.ext; unfold raw540step1 raw540step0; decide +kernel
      have hl : raw540step0Labels = labelEmbedding1 ∘ raw540step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw540step0 raw540step0Labels raw540step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw541 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw541Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw541step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw541step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw541 raw541Labels = mixedMoment B node467 node467Labels := by
  calc
    mixedMoment B raw541 raw541Labels = mixedMoment B raw541step0 raw541step0Labels := by
      have ha : raw541step0 = (fun i j => raw541 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw541step0 raw541; decide +kernel
      have hl : raw541step0Labels = raw541Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw541 raw541Labels permutation151 permutation4
    mixedMoment B raw541step0 raw541step0Labels = mixedMoment B raw541step1 raw541step1Labels := by
      have ha : raw541step1 = -raw541step0 := by apply Matrix.ext; change ∀ i j, raw541step1 i j = -(raw541step0 i j); unfold raw541step1 raw541step0; decide +kernel
      have hl : raw541step1Labels = raw541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node467 node467Labels := by rfl

def raw542 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw542step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw542step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw542 raw542Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw542 raw542Labels = mixedMoment B raw542step0 raw542step0Labels := by
      have ha : raw542step0 = (fun i j => raw542 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw542step0 raw542; decide +kernel
      have hl : raw542step0Labels = raw542Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw542 raw542Labels permutation32 permutation5
    mixedMoment B raw542step0 raw542step0Labels = mixedMoment B raw542step1 raw542step1Labels := by
      have ha : raw542step1 = raw542step0 := by apply Matrix.ext; unfold raw542step1 raw542step0; decide +kernel
      have hl : raw542step0Labels = labelEmbedding1 ∘ raw542step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw542step0 raw542step0Labels raw542step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw543 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw543Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw543step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw543 raw543Labels = mixedMoment B node502 node502Labels := by
  calc
    mixedMoment B raw543 raw543Labels = mixedMoment B raw543step0 raw543step0Labels := by
      have ha : raw543step0 = (fun i j => raw543 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw543step0 raw543; decide +kernel
      have hl : raw543step0Labels = raw543Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw543 raw543Labels permutation32 permutation5
    _ = mixedMoment B node502 node502Labels := by rfl

def raw544 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1]]
def raw544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw544step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw544step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw544 raw544Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw544 raw544Labels = mixedMoment B raw544step0 raw544step0Labels := by
      have ha : raw544step0 = (fun i j => raw544 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw544step0 raw544; decide +kernel
      have hl : raw544step0Labels = raw544Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw544 raw544Labels permutation8 permutation5
    mixedMoment B raw544step0 raw544step0Labels = mixedMoment B raw544step1 raw544step1Labels := by
      have ha : raw544step1 = raw544step0 := by apply Matrix.ext; unfold raw544step1 raw544step0; decide +kernel
      have hl : raw544step0Labels = labelEmbedding1 ∘ raw544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw544step0 raw544step0Labels raw544step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw545 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1]]
def raw545Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw545step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw545step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw545 raw545Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw545 raw545Labels = mixedMoment B raw545step0 raw545step0Labels := by
      have ha : raw545step0 = (fun i j => raw545 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw545step0 raw545; decide +kernel
      have hl : raw545step0Labels = raw545Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw545 raw545Labels permutation8 permutation5
    _ = mixedMoment B node503 node503Labels := by rfl

def raw546 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2]]
def raw546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw546step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw546step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw546step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw546 raw546Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw546 raw546Labels = mixedMoment B raw546step0 raw546step0Labels := by
      have ha : raw546step0 = (fun i j => raw546 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw546step0 raw546; decide +kernel
      have hl : raw546step0Labels = raw546Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw546 raw546Labels permutation8 permutation5
    mixedMoment B raw546step0 raw546step0Labels = mixedMoment B raw546step1 raw546step1Labels := by
      have ha : raw546step1 = raw546step0 := by apply Matrix.ext; unfold raw546step1 raw546step0; decide +kernel
      have hl : raw546step0Labels = labelEmbedding1 ∘ raw546step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw546step0 raw546step0Labels raw546step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw547 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2]]
def raw547Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw547step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw547step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw547step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw547 raw547Labels = mixedMoment B node496 node496Labels := by
  calc
    mixedMoment B raw547 raw547Labels = mixedMoment B raw547step0 raw547step0Labels := by
      have ha : raw547step0 = (fun i j => raw547 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw547step0 raw547; decide +kernel
      have hl : raw547step0Labels = raw547Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw547 raw547Labels permutation31 permutation4
    mixedMoment B raw547step0 raw547step0Labels = mixedMoment B raw547step1 raw547step1Labels := by
      have ha : raw547step1 = -raw547step0 := by apply Matrix.ext; change ∀ i j, raw547step1 i j = -(raw547step0 i j); unfold raw547step1 raw547step0; decide +kernel
      have hl : raw547step1Labels = raw547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node496 node496Labels := by rfl

def raw548 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1]]
def raw548Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw548step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw548step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw548step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw548 raw548Labels = mixedMoment B node3911 node3911Labels := by
  calc
    mixedMoment B raw548 raw548Labels = mixedMoment B raw548step0 raw548step0Labels := by
      have ha : raw548step0 = (fun i j => raw548 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw548step0 raw548; decide +kernel
      have hl : raw548step0Labels = raw548Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw548 raw548Labels permutation32 permutation5
    mixedMoment B raw548step0 raw548step0Labels = mixedMoment B raw548step1 raw548step1Labels := by
      have ha : raw548step1 = raw548step0 := by apply Matrix.ext; unfold raw548step1 raw548step0; decide +kernel
      have hl : raw548step0Labels = labelEmbedding1 ∘ raw548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw548step0 raw548step0Labels raw548step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3911 node3911Labels := by rfl

def raw549 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1]]
def raw549Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw549step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw549step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw549 raw549Labels = mixedMoment B node504 node504Labels := by
  calc
    mixedMoment B raw549 raw549Labels = mixedMoment B raw549step0 raw549step0Labels := by
      have ha : raw549step0 = (fun i j => raw549 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw549step0 raw549; decide +kernel
      have hl : raw549step0Labels = raw549Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw549 raw549Labels permutation48 permutation3
    mixedMoment B raw549step0 raw549step0Labels = mixedMoment B raw549step1 raw549step1Labels := by
      have ha : raw549step1 = -raw549step0 := by apply Matrix.ext; change ∀ i j, raw549step1 i j = -(raw549step0 i j); unfold raw549step1 raw549step0; decide +kernel
      have hl : raw549step1Labels = raw549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node504 node504Labels := by rfl

def raw550 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2]]
def raw550Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw550step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw550step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw550step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw550 raw550Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw550 raw550Labels = mixedMoment B raw550step0 raw550step0Labels := by
      have ha : raw550step0 = (fun i j => raw550 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw550step0 raw550; decide +kernel
      have hl : raw550step0Labels = raw550Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw550 raw550Labels permutation8 permutation5
    mixedMoment B raw550step0 raw550step0Labels = mixedMoment B raw550step1 raw550step1Labels := by
      have ha : raw550step1 = raw550step0 := by apply Matrix.ext; unfold raw550step1 raw550step0; decide +kernel
      have hl : raw550step0Labels = labelEmbedding1 ∘ raw550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw550step0 raw550step0Labels raw550step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw551 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2]]
def raw551Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw551step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw551step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw551step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw551 raw551Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw551 raw551Labels = mixedMoment B raw551step0 raw551step0Labels := by
      have ha : raw551step0 = (fun i j => raw551 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw551step0 raw551; decide +kernel
      have hl : raw551step0Labels = raw551Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw551 raw551Labels permutation29 permutation4
    mixedMoment B raw551step0 raw551step0Labels = mixedMoment B raw551step1 raw551step1Labels := by
      have ha : raw551step1 = -raw551step0 := by apply Matrix.ext; change ∀ i j, raw551step1 i j = -(raw551step0 i j); unfold raw551step1 raw551step0; decide +kernel
      have hl : raw551step1Labels = raw551step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node505 node505Labels := by rfl

def raw552 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1]]
def raw552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw552step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw552step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw552 raw552Labels = mixedMoment B node3915 node3915Labels := by
  calc
    mixedMoment B raw552 raw552Labels = mixedMoment B raw552step0 raw552step0Labels := by
      have ha : raw552step0 = (fun i j => raw552 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw552step0 raw552; decide +kernel
      have hl : raw552step0Labels = raw552Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw552 raw552Labels permutation8 permutation5
    mixedMoment B raw552step0 raw552step0Labels = mixedMoment B raw552step1 raw552step1Labels := by
      have ha : raw552step1 = raw552step0 := by apply Matrix.ext; unfold raw552step1 raw552step0; decide +kernel
      have hl : raw552step0Labels = labelEmbedding1 ∘ raw552step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw552step0 raw552step0Labels raw552step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3915 node3915Labels := by rfl

def raw553 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1]]
def raw553Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw553step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw553step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw553 raw553Labels = mixedMoment B node505 node505Labels := by
  calc
    mixedMoment B raw553 raw553Labels = mixedMoment B raw553step0 raw553step0Labels := by
      have ha : raw553step0 = (fun i j => raw553 (permutation17 i) (permutation2 j)) := by apply Matrix.ext; unfold raw553step0 raw553; decide +kernel
      have hl : raw553step0Labels = raw553Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw553 raw553Labels permutation17 permutation2
    _ = mixedMoment B node505 node505Labels := by rfl

def raw554 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -2, 0], ![-2, 0, 2], ![0, 2, -2]]
def raw554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw554step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw554step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw554step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw554 raw554Labels = mixedMoment B node3916 node3916Labels := by
  calc
    mixedMoment B raw554 raw554Labels = mixedMoment B raw554step0 raw554step0Labels := by
      have ha : raw554step0 = (fun i j => raw554 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw554step0 raw554; decide +kernel
      have hl : raw554step0Labels = raw554Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw554 raw554Labels permutation2 permutation5
    mixedMoment B raw554step0 raw554step0Labels = mixedMoment B raw554step1 raw554step1Labels := by
      have ha : raw554step1 = raw554step0 := by apply Matrix.ext; unfold raw554step1 raw554step0; decide +kernel
      have hl : raw554step0Labels = labelEmbedding1 ∘ raw554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw554step0 raw554step0Labels raw554step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3916 node3916Labels := by rfl

def raw555 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -2, 0], ![-2, 0, 2], ![0, 2, -2]]
def raw555Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw555step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![2, -2, 0]]
def raw555step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw555 raw555Labels = mixedMoment B node507 node507Labels := by
  calc
    mixedMoment B raw555 raw555Labels = mixedMoment B raw555step0 raw555step0Labels := by
      have ha : raw555step0 = (fun i j => raw555 (permutation5 i) (permutation2 j)) := by apply Matrix.ext; unfold raw555step0 raw555; decide +kernel
      have hl : raw555step0Labels = raw555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw555 raw555Labels permutation5 permutation2
    _ = mixedMoment B node507 node507Labels := by rfl

def raw556 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw556step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw556 raw556Labels = mixedMoment B node3919 node3919Labels := by
  calc
    mixedMoment B raw556 raw556Labels = mixedMoment B raw556step0 raw556step0Labels := by
      have ha : raw556step0 = (fun i j => raw556 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw556step0 raw556; decide +kernel
      have hl : raw556step0Labels = raw556Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw556 raw556Labels permutation152 permutation5
    mixedMoment B raw556step0 raw556step0Labels = mixedMoment B raw556step1 raw556step1Labels := by
      have ha : raw556step1 = raw556step0 := by apply Matrix.ext; unfold raw556step1 raw556step0; decide +kernel
      have hl : raw556step0Labels = labelEmbedding1 ∘ raw556step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw556step0 raw556step0Labels raw556step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3919 node3919Labels := by rfl

def raw557 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![-1, 2, -1]]
def raw557Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw557step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw557step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw557 raw557Labels = mixedMoment B node425 node425Labels := by
  calc
    mixedMoment B raw557 raw557Labels = mixedMoment B raw557step0 raw557step0Labels := by
      have ha : raw557step0 = (fun i j => raw557 (permutation588 i) (permutation4 j)) := by apply Matrix.ext; unfold raw557step0 raw557; decide +kernel
      have hl : raw557step0Labels = raw557Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw557 raw557Labels permutation588 permutation4
    mixedMoment B raw557step0 raw557step0Labels = mixedMoment B raw557step1 raw557step1Labels := by
      have ha : raw557step1 = -raw557step0 := by apply Matrix.ext; change ∀ i j, raw557step1 i j = -(raw557step0 i j); unfold raw557step1 raw557step0; decide +kernel
      have hl : raw557step1Labels = raw557step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node425 node425Labels := by rfl

def raw558 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw558 raw558Labels = mixedMoment B node3925 node3925Labels := by
  calc
    mixedMoment B raw558 raw558Labels = mixedMoment B raw558step0 raw558step0Labels := by
      have ha : raw558step0 = (fun i j => raw558 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw558step0 raw558; decide +kernel
      have hl : raw558step0Labels = raw558Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw558 raw558Labels permutation152 permutation5
    mixedMoment B raw558step0 raw558step0Labels = mixedMoment B raw558step1 raw558step1Labels := by
      have ha : raw558step1 = raw558step0 := by apply Matrix.ext; unfold raw558step1 raw558step0; decide +kernel
      have hl : raw558step0Labels = labelEmbedding1 ∘ raw558step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw558step0 raw558step0Labels raw558step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3925 node3925Labels := by rfl

def raw559 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw559Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw559step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw559step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw559 raw559Labels = mixedMoment B node453 node453Labels := by
  calc
    mixedMoment B raw559 raw559Labels = mixedMoment B raw559step0 raw559step0Labels := by
      have ha : raw559step0 = (fun i j => raw559 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw559step0 raw559; decide +kernel
      have hl : raw559step0Labels = raw559Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw559 raw559Labels permutation663 permutation4
    mixedMoment B raw559step0 raw559step0Labels = mixedMoment B raw559step1 raw559step1Labels := by
      have ha : raw559step1 = -raw559step0 := by apply Matrix.ext; change ∀ i j, raw559step1 i j = -(raw559step0 i j); unfold raw559step1 raw559step0; decide +kernel
      have hl : raw559step1Labels = raw559step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node453 node453Labels := by rfl

def raw560 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw560step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw560 raw560Labels = mixedMoment B node3926 node3926Labels := by
  calc
    mixedMoment B raw560 raw560Labels = mixedMoment B raw560step0 raw560step0Labels := by
      have ha : raw560step0 = (fun i j => raw560 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw560step0 raw560; decide +kernel
      have hl : raw560step0Labels = raw560Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw560 raw560Labels permutation32 permutation5
    mixedMoment B raw560step0 raw560step0Labels = mixedMoment B raw560step1 raw560step1Labels := by
      have ha : raw560step1 = raw560step0 := by apply Matrix.ext; unfold raw560step1 raw560step0; decide +kernel
      have hl : raw560step0Labels = labelEmbedding1 ∘ raw560step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw560step0 raw560step0Labels raw560step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3926 node3926Labels := by rfl

def raw561 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 2, -1]]
def raw561Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw561step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw561step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw561step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw561 raw561Labels = mixedMoment B node433 node433Labels := by
  calc
    mixedMoment B raw561 raw561Labels = mixedMoment B raw561step0 raw561step0Labels := by
      have ha : raw561step0 = (fun i j => raw561 (permutation126 i) (permutation4 j)) := by apply Matrix.ext; unfold raw561step0 raw561; decide +kernel
      have hl : raw561step0Labels = raw561Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw561 raw561Labels permutation126 permutation4
    mixedMoment B raw561step0 raw561step0Labels = mixedMoment B raw561step1 raw561step1Labels := by
      have ha : raw561step1 = -raw561step0 := by apply Matrix.ext; change ∀ i j, raw561step1 i j = -(raw561step0 i j); unfold raw561step1 raw561step0; decide +kernel
      have hl : raw561step1Labels = raw561step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node433 node433Labels := by rfl

def raw562 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw562 raw562Labels = mixedMoment B node3930 node3930Labels := by
  calc
    mixedMoment B raw562 raw562Labels = mixedMoment B raw562step0 raw562step0Labels := by
      have ha : raw562step0 = (fun i j => raw562 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw562step0 raw562; decide +kernel
      have hl : raw562step0Labels = raw562Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw562 raw562Labels permutation152 permutation5
    mixedMoment B raw562step0 raw562step0Labels = mixedMoment B raw562step1 raw562step1Labels := by
      have ha : raw562step1 = raw562step0 := by apply Matrix.ext; unfold raw562step1 raw562step0; decide +kernel
      have hl : raw562step0Labels = labelEmbedding1 ∘ raw562step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw562step0 raw562step0Labels raw562step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3930 node3930Labels := by rfl

def raw563 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw563Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw563step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw563 raw563Labels = mixedMoment B node508 node508Labels := by
  calc
    mixedMoment B raw563 raw563Labels = mixedMoment B raw563step0 raw563step0Labels := by
      have ha : raw563step0 = (fun i j => raw563 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw563step0 raw563; decide +kernel
      have hl : raw563step0Labels = raw563Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw563 raw563Labels permutation168 permutation4
    _ = mixedMoment B node508 node508Labels := by rfl

def raw564 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw564Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw564step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw564 raw564Labels = mixedMoment B node3931 node3931Labels := by
  calc
    mixedMoment B raw564 raw564Labels = mixedMoment B raw564step0 raw564step0Labels := by
      have ha : raw564step0 = (fun i j => raw564 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw564step0 raw564; decide +kernel
      have hl : raw564step0Labels = raw564Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw564 raw564Labels permutation32 permutation5
    mixedMoment B raw564step0 raw564step0Labels = mixedMoment B raw564step1 raw564step1Labels := by
      have ha : raw564step1 = raw564step0 := by apply Matrix.ext; unfold raw564step1 raw564step0; decide +kernel
      have hl : raw564step0Labels = labelEmbedding1 ∘ raw564step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw564step0 raw564step0Labels raw564step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3931 node3931Labels := by rfl

def raw565 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw565Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw565step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw565 raw565Labels = mixedMoment B node509 node509Labels := by
  calc
    mixedMoment B raw565 raw565Labels = mixedMoment B raw565step0 raw565step0Labels := by
      have ha : raw565step0 = (fun i j => raw565 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw565step0 raw565; decide +kernel
      have hl : raw565step0Labels = raw565Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw565 raw565Labels permutation34 permutation4
    _ = mixedMoment B node509 node509Labels := by rfl

def raw566 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw566Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw566step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw566step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw566step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw566 raw566Labels = mixedMoment B node3932 node3932Labels := by
  calc
    mixedMoment B raw566 raw566Labels = mixedMoment B raw566step0 raw566step0Labels := by
      have ha : raw566step0 = (fun i j => raw566 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw566step0 raw566; decide +kernel
      have hl : raw566step0Labels = raw566Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw566 raw566Labels permutation32 permutation5
    mixedMoment B raw566step0 raw566step0Labels = mixedMoment B raw566step1 raw566step1Labels := by
      have ha : raw566step1 = raw566step0 := by apply Matrix.ext; unfold raw566step1 raw566step0; decide +kernel
      have hl : raw566step0Labels = labelEmbedding1 ∘ raw566step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw566step0 raw566step0Labels raw566step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3932 node3932Labels := by rfl

def raw567 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw567Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw567step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw567step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw567step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw567step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw567 raw567Labels = mixedMoment B node460 node460Labels := by
  calc
    mixedMoment B raw567 raw567Labels = mixedMoment B raw567step0 raw567step0Labels := by
      have ha : raw567step0 = (fun i j => raw567 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw567step0 raw567; decide +kernel
      have hl : raw567step0Labels = raw567Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw567 raw567Labels permutation144 permutation4
    mixedMoment B raw567step0 raw567step0Labels = mixedMoment B raw567step1 raw567step1Labels := by
      have ha : raw567step1 = -raw567step0 := by apply Matrix.ext; change ∀ i j, raw567step1 i j = -(raw567step0 i j); unfold raw567step1 raw567step0; decide +kernel
      have hl : raw567step1Labels = raw567step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node460 node460Labels := by rfl

def raw568 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw568Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw568 raw568Labels = mixedMoment B node3933 node3933Labels := by
  calc
    mixedMoment B raw568 raw568Labels = mixedMoment B raw568step0 raw568step0Labels := by
      have ha : raw568step0 = (fun i j => raw568 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw568step0 raw568; decide +kernel
      have hl : raw568step0Labels = raw568Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw568 raw568Labels permutation32 permutation5
    mixedMoment B raw568step0 raw568step0Labels = mixedMoment B raw568step1 raw568step1Labels := by
      have ha : raw568step1 = raw568step0 := by apply Matrix.ext; unfold raw568step1 raw568step0; decide +kernel
      have hl : raw568step0Labels = labelEmbedding1 ∘ raw568step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw568step0 raw568step0Labels raw568step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3933 node3933Labels := by rfl

def raw569 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw569Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw569step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw569step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw569 raw569Labels = mixedMoment B node474 node474Labels := by
  calc
    mixedMoment B raw569 raw569Labels = mixedMoment B raw569step0 raw569step0Labels := by
      have ha : raw569step0 = (fun i j => raw569 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw569step0 raw569; decide +kernel
      have hl : raw569step0Labels = raw569Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw569 raw569Labels permutation144 permutation4
    mixedMoment B raw569step0 raw569step0Labels = mixedMoment B raw569step1 raw569step1Labels := by
      have ha : raw569step1 = -raw569step0 := by apply Matrix.ext; change ∀ i j, raw569step1 i j = -(raw569step0 i j); unfold raw569step1 raw569step0; decide +kernel
      have hl : raw569step1Labels = raw569step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node474 node474Labels := by rfl

def raw570 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw570Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw570step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw570step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw570 raw570Labels = mixedMoment B node3934 node3934Labels := by
  calc
    mixedMoment B raw570 raw570Labels = mixedMoment B raw570step0 raw570step0Labels := by
      have ha : raw570step0 = (fun i j => raw570 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw570step0 raw570; decide +kernel
      have hl : raw570step0Labels = raw570Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw570 raw570Labels permutation8 permutation5
    mixedMoment B raw570step0 raw570step0Labels = mixedMoment B raw570step1 raw570step1Labels := by
      have ha : raw570step1 = raw570step0 := by apply Matrix.ext; unfold raw570step1 raw570step0; decide +kernel
      have hl : raw570step0Labels = labelEmbedding1 ∘ raw570step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw570step0 raw570step0Labels raw570step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3934 node3934Labels := by rfl

def raw571 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 2, -1]]
def raw571Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw571step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw571step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw571 raw571Labels = mixedMoment B node510 node510Labels := by
  calc
    mixedMoment B raw571 raw571Labels = mixedMoment B raw571step0 raw571step0Labels := by
      have ha : raw571step0 = (fun i j => raw571 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw571step0 raw571; decide +kernel
      have hl : raw571step0Labels = raw571Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw571 raw571Labels permutation8 permutation4
    _ = mixedMoment B node510 node510Labels := by rfl

def raw572 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw572Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw572step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw572 raw572Labels = mixedMoment B node3936 node3936Labels := by
  calc
    mixedMoment B raw572 raw572Labels = mixedMoment B raw572step0 raw572step0Labels := by
      have ha : raw572step0 = (fun i j => raw572 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw572step0 raw572; decide +kernel
      have hl : raw572step0Labels = raw572Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw572 raw572Labels permutation152 permutation5
    mixedMoment B raw572step0 raw572step0Labels = mixedMoment B raw572step1 raw572step1Labels := by
      have ha : raw572step1 = raw572step0 := by apply Matrix.ext; unfold raw572step1 raw572step0; decide +kernel
      have hl : raw572step0Labels = labelEmbedding1 ∘ raw572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw572step0 raw572step0Labels raw572step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3936 node3936Labels := by rfl

def raw573 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw573Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw573step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw573 raw573Labels = mixedMoment B node430 node430Labels := by
  calc
    mixedMoment B raw573 raw573Labels = mixedMoment B raw573step0 raw573step0Labels := by
      have ha : raw573step0 = (fun i j => raw573 (permutation267 i) (permutation4 j)) := by apply Matrix.ext; unfold raw573step0 raw573; decide +kernel
      have hl : raw573step0Labels = raw573Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw573 raw573Labels permutation267 permutation4
    _ = mixedMoment B node430 node430Labels := by rfl

def raw574 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw574Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw574 raw574Labels = mixedMoment B node3937 node3937Labels := by
  calc
    mixedMoment B raw574 raw574Labels = mixedMoment B raw574step0 raw574step0Labels := by
      have ha : raw574step0 = (fun i j => raw574 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw574step0 raw574; decide +kernel
      have hl : raw574step0Labels = raw574Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw574 raw574Labels permutation152 permutation5
    mixedMoment B raw574step0 raw574step0Labels = mixedMoment B raw574step1 raw574step1Labels := by
      have ha : raw574step1 = raw574step0 := by apply Matrix.ext; unfold raw574step1 raw574step0; decide +kernel
      have hl : raw574step0Labels = labelEmbedding1 ∘ raw574step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw574step0 raw574step0Labels raw574step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3937 node3937Labels := by rfl

def raw575 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw575Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw575step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw575 raw575Labels = mixedMoment B node429 node429Labels := by
  calc
    mixedMoment B raw575 raw575Labels = mixedMoment B raw575step0 raw575step0Labels := by
      have ha : raw575step0 = (fun i j => raw575 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw575step0 raw575; decide +kernel
      have hl : raw575step0Labels = raw575Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw575 raw575Labels permutation265 permutation4
    _ = mixedMoment B node429 node429Labels := by rfl

def raw576 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw576Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw576 raw576Labels = mixedMoment B node3938 node3938Labels := by
  calc
    mixedMoment B raw576 raw576Labels = mixedMoment B raw576step0 raw576step0Labels := by
      have ha : raw576step0 = (fun i j => raw576 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw576step0 raw576; decide +kernel
      have hl : raw576step0Labels = raw576Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw576 raw576Labels permutation152 permutation5
    mixedMoment B raw576step0 raw576step0Labels = mixedMoment B raw576step1 raw576step1Labels := by
      have ha : raw576step1 = raw576step0 := by apply Matrix.ext; unfold raw576step1 raw576step0; decide +kernel
      have hl : raw576step0Labels = labelEmbedding1 ∘ raw576step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw576step0 raw576step0Labels raw576step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3938 node3938Labels := by rfl

def raw577 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw577Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw577step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw577 raw577Labels = mixedMoment B node436 node436Labels := by
  calc
    mixedMoment B raw577 raw577Labels = mixedMoment B raw577step0 raw577step0Labels := by
      have ha : raw577step0 = (fun i j => raw577 (permutation282 i) (permutation4 j)) := by apply Matrix.ext; unfold raw577step0 raw577; decide +kernel
      have hl : raw577step0Labels = raw577Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw577 raw577Labels permutation282 permutation4
    _ = mixedMoment B node436 node436Labels := by rfl

def raw578 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw578Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw578step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw578 raw578Labels = mixedMoment B node3939 node3939Labels := by
  calc
    mixedMoment B raw578 raw578Labels = mixedMoment B raw578step0 raw578step0Labels := by
      have ha : raw578step0 = (fun i j => raw578 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw578step0 raw578; decide +kernel
      have hl : raw578step0Labels = raw578Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw578 raw578Labels permutation32 permutation5
    mixedMoment B raw578step0 raw578step0Labels = mixedMoment B raw578step1 raw578step1Labels := by
      have ha : raw578step1 = raw578step0 := by apply Matrix.ext; unfold raw578step1 raw578step0; decide +kernel
      have hl : raw578step0Labels = labelEmbedding1 ∘ raw578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw578step0 raw578step0Labels raw578step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3939 node3939Labels := by rfl

def raw579 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -2, 2], ![1, 1, -2], ![-1, 1, 0], ![-1, 2, -1]]
def raw579Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw579step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw579step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw579 raw579Labels = mixedMoment B node437 node437Labels := by
  calc
    mixedMoment B raw579 raw579Labels = mixedMoment B raw579step0 raw579step0Labels := by
      have ha : raw579step0 = (fun i j => raw579 (permutation58 i) (permutation4 j)) := by apply Matrix.ext; unfold raw579step0 raw579; decide +kernel
      have hl : raw579step0Labels = raw579Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw579 raw579Labels permutation58 permutation4
    _ = mixedMoment B node437 node437Labels := by rfl

def raw580 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw580Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw580step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw580step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw580step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw580 raw580Labels = mixedMoment B node3965 node3965Labels := by
  calc
    mixedMoment B raw580 raw580Labels = mixedMoment B raw580step0 raw580step0Labels := by
      have ha : raw580step0 = (fun i j => raw580 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw580step0 raw580; decide +kernel
      have hl : raw580step0Labels = raw580Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw580 raw580Labels permutation152 permutation5
    mixedMoment B raw580step0 raw580step0Labels = mixedMoment B raw580step1 raw580step1Labels := by
      have ha : raw580step1 = raw580step0 := by apply Matrix.ext; unfold raw580step1 raw580step0; decide +kernel
      have hl : raw580step0Labels = labelEmbedding1 ∘ raw580step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw580step0 raw580step0Labels raw580step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3965 node3965Labels := by rfl

def raw581 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 2, -1]]
def raw581Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw581step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw581 raw581Labels = mixedMoment B node517 node517Labels := by
  calc
    mixedMoment B raw581 raw581Labels = mixedMoment B raw581step0 raw581step0Labels := by
      have ha : raw581step0 = (fun i j => raw581 (permutation178 i) (permutation4 j)) := by apply Matrix.ext; unfold raw581step0 raw581; decide +kernel
      have hl : raw581step0Labels = raw581Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw581 raw581Labels permutation178 permutation4
    _ = mixedMoment B node517 node517Labels := by rfl

def raw582 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw582Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw582step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw582step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw582 raw582Labels = mixedMoment B node3966 node3966Labels := by
  calc
    mixedMoment B raw582 raw582Labels = mixedMoment B raw582step0 raw582step0Labels := by
      have ha : raw582step0 = (fun i j => raw582 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw582step0 raw582; decide +kernel
      have hl : raw582step0Labels = raw582Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw582 raw582Labels permutation152 permutation5
    mixedMoment B raw582step0 raw582step0Labels = mixedMoment B raw582step1 raw582step1Labels := by
      have ha : raw582step1 = raw582step0 := by apply Matrix.ext; unfold raw582step1 raw582step0; decide +kernel
      have hl : raw582step0Labels = labelEmbedding1 ∘ raw582step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw582step0 raw582step0Labels raw582step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3966 node3966Labels := by rfl

def raw583 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw583Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw583step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw583step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw583 raw583Labels = mixedMoment B node457 node457Labels := by
  calc
    mixedMoment B raw583 raw583Labels = mixedMoment B raw583step0 raw583step0Labels := by
      have ha : raw583step0 = (fun i j => raw583 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw583step0 raw583; decide +kernel
      have hl : raw583step0Labels = raw583Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw583 raw583Labels permutation662 permutation4
    mixedMoment B raw583step0 raw583step0Labels = mixedMoment B raw583step1 raw583step1Labels := by
      have ha : raw583step1 = -raw583step0 := by apply Matrix.ext; change ∀ i j, raw583step1 i j = -(raw583step0 i j); unfold raw583step1 raw583step0; decide +kernel
      have hl : raw583step1Labels = raw583step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node457 node457Labels := by rfl

def raw584 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw584Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw584step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw584step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw584 raw584Labels = mixedMoment B node3967 node3967Labels := by
  calc
    mixedMoment B raw584 raw584Labels = mixedMoment B raw584step0 raw584step0Labels := by
      have ha : raw584step0 = (fun i j => raw584 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw584step0 raw584; decide +kernel
      have hl : raw584step0Labels = raw584Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw584 raw584Labels permutation152 permutation5
    mixedMoment B raw584step0 raw584step0Labels = mixedMoment B raw584step1 raw584step1Labels := by
      have ha : raw584step1 = raw584step0 := by apply Matrix.ext; unfold raw584step1 raw584step0; decide +kernel
      have hl : raw584step0Labels = labelEmbedding1 ∘ raw584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw584step0 raw584step0Labels raw584step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3967 node3967Labels := by rfl

def raw585 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw585Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw585step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw585step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw585 raw585Labels = mixedMoment B node472 node472Labels := by
  calc
    mixedMoment B raw585 raw585Labels = mixedMoment B raw585step0 raw585step0Labels := by
      have ha : raw585step0 = (fun i j => raw585 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw585step0 raw585; decide +kernel
      have hl : raw585step0Labels = raw585Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw585 raw585Labels permutation662 permutation4
    mixedMoment B raw585step0 raw585step0Labels = mixedMoment B raw585step1 raw585step1Labels := by
      have ha : raw585step1 = -raw585step0 := by apply Matrix.ext; change ∀ i j, raw585step1 i j = -(raw585step0 i j); unfold raw585step1 raw585step0; decide +kernel
      have hl : raw585step1Labels = raw585step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node472 node472Labels := by rfl

def raw586 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw586Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw586step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw586step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw586 raw586Labels = mixedMoment B node3969 node3969Labels := by
  calc
    mixedMoment B raw586 raw586Labels = mixedMoment B raw586step0 raw586step0Labels := by
      have ha : raw586step0 = (fun i j => raw586 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw586step0 raw586; decide +kernel
      have hl : raw586step0Labels = raw586Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw586 raw586Labels permutation152 permutation5
    mixedMoment B raw586step0 raw586step0Labels = mixedMoment B raw586step1 raw586step1Labels := by
      have ha : raw586step1 = raw586step0 := by apply Matrix.ext; unfold raw586step1 raw586step0; decide +kernel
      have hl : raw586step0Labels = labelEmbedding1 ∘ raw586step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw586step0 raw586step0Labels raw586step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3969 node3969Labels := by rfl

def raw587 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw587Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw587step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw587 raw587Labels = mixedMoment B node511 node511Labels := by
  calc
    mixedMoment B raw587 raw587Labels = mixedMoment B raw587step0 raw587step0Labels := by
      have ha : raw587step0 = (fun i j => raw587 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw587step0 raw587; decide +kernel
      have hl : raw587step0Labels = raw587Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw587 raw587Labels permutation176 permutation4
    _ = mixedMoment B node511 node511Labels := by rfl

def raw588 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw588Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw588step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw588step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw588 raw588Labels = mixedMoment B node3970 node3970Labels := by
  calc
    mixedMoment B raw588 raw588Labels = mixedMoment B raw588step0 raw588step0Labels := by
      have ha : raw588step0 = (fun i j => raw588 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw588step0 raw588; decide +kernel
      have hl : raw588step0Labels = raw588Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw588 raw588Labels permutation152 permutation5
    mixedMoment B raw588step0 raw588step0Labels = mixedMoment B raw588step1 raw588step1Labels := by
      have ha : raw588step1 = raw588step0 := by apply Matrix.ext; unfold raw588step1 raw588step0; decide +kernel
      have hl : raw588step0Labels = labelEmbedding1 ∘ raw588step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw588step0 raw588step0Labels raw588step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3970 node3970Labels := by rfl

def raw589 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw589Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw589step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw589step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw589 raw589Labels = mixedMoment B node454 node454Labels := by
  calc
    mixedMoment B raw589 raw589Labels = mixedMoment B raw589step0 raw589step0Labels := by
      have ha : raw589step0 = (fun i j => raw589 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw589step0 raw589; decide +kernel
      have hl : raw589step0Labels = raw589Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw589 raw589Labels permutation662 permutation4
    mixedMoment B raw589step0 raw589step0Labels = mixedMoment B raw589step1 raw589step1Labels := by
      have ha : raw589step1 = -raw589step0 := by apply Matrix.ext; change ∀ i j, raw589step1 i j = -(raw589step0 i j); unfold raw589step1 raw589step0; decide +kernel
      have hl : raw589step1Labels = raw589step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node454 node454Labels := by rfl

def raw590 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw590Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw590step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw590step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw590 raw590Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw590 raw590Labels = mixedMoment B raw590step0 raw590step0Labels := by
      have ha : raw590step0 = (fun i j => raw590 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw590step0 raw590; decide +kernel
      have hl : raw590step0Labels = raw590Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw590 raw590Labels permutation152 permutation5
    mixedMoment B raw590step0 raw590step0Labels = mixedMoment B raw590step1 raw590step1Labels := by
      have ha : raw590step1 = raw590step0 := by apply Matrix.ext; unfold raw590step1 raw590step0; decide +kernel
      have hl : raw590step0Labels = labelEmbedding1 ∘ raw590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw590step0 raw590step0Labels raw590step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw591 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2]]
def raw591Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw591step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw591step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw591 raw591Labels = mixedMoment B node461 node461Labels := by
  calc
    mixedMoment B raw591 raw591Labels = mixedMoment B raw591step0 raw591step0Labels := by
      have ha : raw591step0 = (fun i j => raw591 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw591step0 raw591; decide +kernel
      have hl : raw591step0Labels = raw591Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw591 raw591Labels permutation682 permutation4
    mixedMoment B raw591step0 raw591step0Labels = mixedMoment B raw591step1 raw591step1Labels := by
      have ha : raw591step1 = -raw591step0 := by apply Matrix.ext; change ∀ i j, raw591step1 i j = -(raw591step0 i j); unfold raw591step1 raw591step0; decide +kernel
      have hl : raw591step1Labels = raw591step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node461 node461Labels := by rfl

def raw592 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw592Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw592step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw592step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw592 raw592Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw592 raw592Labels = mixedMoment B raw592step0 raw592step0Labels := by
      have ha : raw592step0 = (fun i j => raw592 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw592step0 raw592; decide +kernel
      have hl : raw592step0Labels = raw592Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw592 raw592Labels permutation152 permutation5
    mixedMoment B raw592step0 raw592step0Labels = mixedMoment B raw592step1 raw592step1Labels := by
      have ha : raw592step1 = raw592step0 := by apply Matrix.ext; unfold raw592step1 raw592step0; decide +kernel
      have hl : raw592step0Labels = labelEmbedding1 ∘ raw592step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw592step0 raw592step0Labels raw592step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw593 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw593Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw593step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw593 raw593Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw593 raw593Labels = mixedMoment B raw593step0 raw593step0Labels := by
      have ha : raw593step0 = (fun i j => raw593 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw593step0 raw593; decide +kernel
      have hl : raw593step0Labels = raw593Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw593 raw593Labels permutation152 permutation5
    _ = mixedMoment B node520 node520Labels := by rfl

def raw594 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw594Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw594step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw594step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw594 raw594Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw594 raw594Labels = mixedMoment B raw594step0 raw594step0Labels := by
      have ha : raw594step0 = (fun i j => raw594 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw594step0 raw594; decide +kernel
      have hl : raw594step0Labels = raw594Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw594 raw594Labels permutation32 permutation5
    mixedMoment B raw594step0 raw594step0Labels = mixedMoment B raw594step1 raw594step1Labels := by
      have ha : raw594step1 = raw594step0 := by apply Matrix.ext; unfold raw594step1 raw594step0; decide +kernel
      have hl : raw594step0Labels = labelEmbedding1 ∘ raw594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw594step0 raw594step0Labels raw594step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw595 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1]]
def raw595Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw595step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw595step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw595 raw595Labels = mixedMoment B node521 node521Labels := by
  calc
    mixedMoment B raw595 raw595Labels = mixedMoment B raw595step0 raw595step0Labels := by
      have ha : raw595step0 = (fun i j => raw595 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw595step0 raw595; decide +kernel
      have hl : raw595step0Labels = raw595Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw595 raw595Labels permutation151 permutation4
    mixedMoment B raw595step0 raw595step0Labels = mixedMoment B raw595step1 raw595step1Labels := by
      have ha : raw595step1 = -raw595step0 := by apply Matrix.ext; change ∀ i j, raw595step1 i j = -(raw595step0 i j); unfold raw595step1 raw595step0; decide +kernel
      have hl : raw595step1Labels = raw595step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node521 node521Labels := by rfl

def raw596 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw596Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw596step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw596step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw596 raw596Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw596 raw596Labels = mixedMoment B raw596step0 raw596step0Labels := by
      have ha : raw596step0 = (fun i j => raw596 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw596step0 raw596; decide +kernel
      have hl : raw596step0Labels = raw596Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw596 raw596Labels permutation32 permutation5
    mixedMoment B raw596step0 raw596step0Labels = mixedMoment B raw596step1 raw596step1Labels := by
      have ha : raw596step1 = raw596step0 := by apply Matrix.ext; unfold raw596step1 raw596step0; decide +kernel
      have hl : raw596step0Labels = labelEmbedding1 ∘ raw596step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw596step0 raw596step0Labels raw596step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw597 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw597Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw597step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw597step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw597 raw597Labels = mixedMoment B node489 node489Labels := by
  calc
    mixedMoment B raw597 raw597Labels = mixedMoment B raw597step0 raw597step0Labels := by
      have ha : raw597step0 = (fun i j => raw597 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw597step0 raw597; decide +kernel
      have hl : raw597step0Labels = raw597Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw597 raw597Labels permutation151 permutation4
    mixedMoment B raw597step0 raw597step0Labels = mixedMoment B raw597step1 raw597step1Labels := by
      have ha : raw597step1 = -raw597step0 := by apply Matrix.ext; change ∀ i j, raw597step1 i j = -(raw597step0 i j); unfold raw597step1 raw597step0; decide +kernel
      have hl : raw597step1Labels = raw597step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node489 node489Labels := by rfl

def raw598 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw598Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw598step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw598step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw598 raw598Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw598 raw598Labels = mixedMoment B raw598step0 raw598step0Labels := by
      have ha : raw598step0 = (fun i j => raw598 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw598step0 raw598; decide +kernel
      have hl : raw598step0Labels = raw598Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw598 raw598Labels permutation32 permutation5
    mixedMoment B raw598step0 raw598step0Labels = mixedMoment B raw598step1 raw598step1Labels := by
      have ha : raw598step1 = raw598step0 := by apply Matrix.ext; unfold raw598step1 raw598step0; decide +kernel
      have hl : raw598step0Labels = labelEmbedding1 ∘ raw598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw598step0 raw598step0Labels raw598step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw599 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw599Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw599step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw599 raw599Labels = mixedMoment B node523 node523Labels := by
  calc
    mixedMoment B raw599 raw599Labels = mixedMoment B raw599step0 raw599step0Labels := by
      have ha : raw599step0 = (fun i j => raw599 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw599step0 raw599; decide +kernel
      have hl : raw599step0Labels = raw599Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw599 raw599Labels permutation32 permutation5
    _ = mixedMoment B node523 node523Labels := by rfl

def raw600 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2]]
def raw600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw600step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw600step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw600 raw600Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw600 raw600Labels = mixedMoment B raw600step0 raw600step0Labels := by
      have ha : raw600step0 = (fun i j => raw600 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw600step0 raw600; decide +kernel
      have hl : raw600step0Labels = raw600Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw600 raw600Labels permutation8 permutation5
    mixedMoment B raw600step0 raw600step0Labels = mixedMoment B raw600step1 raw600step1Labels := by
      have ha : raw600step1 = raw600step0 := by apply Matrix.ext; unfold raw600step1 raw600step0; decide +kernel
      have hl : raw600step0Labels = labelEmbedding1 ∘ raw600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw600step0 raw600step0Labels raw600step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw601 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, -1, 0], ![-2, 1, 1], ![0, 2, -2]]
def raw601Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw601step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw601step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw601step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw601step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw601 raw601Labels = mixedMoment B node503 node503Labels := by
  calc
    mixedMoment B raw601 raw601Labels = mixedMoment B raw601step0 raw601step0Labels := by
      have ha : raw601step0 = (fun i j => raw601 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw601step0 raw601; decide +kernel
      have hl : raw601step0Labels = raw601Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw601 raw601Labels permutation31 permutation4
    mixedMoment B raw601step0 raw601step0Labels = mixedMoment B raw601step1 raw601step1Labels := by
      have ha : raw601step1 = -raw601step0 := by apply Matrix.ext; change ∀ i j, raw601step1 i j = -(raw601step0 i j); unfold raw601step1 raw601step0; decide +kernel
      have hl : raw601step1Labels = raw601step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node503 node503Labels := by rfl

def raw602 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw602step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw602 raw602Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw602 raw602Labels = mixedMoment B raw602step0 raw602step0Labels := by
      have ha : raw602step0 = (fun i j => raw602 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw602step0 raw602; decide +kernel
      have hl : raw602step0Labels = raw602Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw602 raw602Labels permutation152 permutation5
    mixedMoment B raw602step0 raw602step0Labels = mixedMoment B raw602step1 raw602step1Labels := by
      have ha : raw602step1 = raw602step0 := by apply Matrix.ext; unfold raw602step1 raw602step0; decide +kernel
      have hl : raw602step0Labels = labelEmbedding1 ∘ raw602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw602step0 raw602step0Labels raw602step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw603 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw603Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw603step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw603step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw603 raw603Labels = mixedMoment B node479 node479Labels := by
  calc
    mixedMoment B raw603 raw603Labels = mixedMoment B raw603step0 raw603step0Labels := by
      have ha : raw603step0 = (fun i j => raw603 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw603step0 raw603; decide +kernel
      have hl : raw603step0Labels = raw603Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw603 raw603Labels permutation682 permutation4
    mixedMoment B raw603step0 raw603step0Labels = mixedMoment B raw603step1 raw603step1Labels := by
      have ha : raw603step1 = -raw603step0 := by apply Matrix.ext; change ∀ i j, raw603step1 i j = -(raw603step0 i j); unfold raw603step1 raw603step0; decide +kernel
      have hl : raw603step1Labels = raw603step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node479 node479Labels := by rfl

def raw604 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw604step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw604 raw604Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw604 raw604Labels = mixedMoment B raw604step0 raw604step0Labels := by
      have ha : raw604step0 = (fun i j => raw604 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw604step0 raw604; decide +kernel
      have hl : raw604step0Labels = raw604Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw604 raw604Labels permutation152 permutation5
    mixedMoment B raw604step0 raw604step0Labels = mixedMoment B raw604step1 raw604step1Labels := by
      have ha : raw604step1 = raw604step0 := by apply Matrix.ext; unfold raw604step1 raw604step0; decide +kernel
      have hl : raw604step0Labels = labelEmbedding1 ∘ raw604step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw604step0 raw604step0Labels raw604step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw605 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw605Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw605step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw605 raw605Labels = mixedMoment B node520 node520Labels := by
  calc
    mixedMoment B raw605 raw605Labels = mixedMoment B raw605step0 raw605step0Labels := by
      have ha : raw605step0 = (fun i j => raw605 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw605step0 raw605; decide +kernel
      have hl : raw605step0Labels = raw605Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw605 raw605Labels permutation155 permutation4
    _ = mixedMoment B node520 node520Labels := by rfl

def raw606 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw606step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw606 raw606Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw606 raw606Labels = mixedMoment B raw606step0 raw606step0Labels := by
      have ha : raw606step0 = (fun i j => raw606 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw606step0 raw606; decide +kernel
      have hl : raw606step0Labels = raw606Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw606 raw606Labels permutation32 permutation5
    mixedMoment B raw606step0 raw606step0Labels = mixedMoment B raw606step1 raw606step1Labels := by
      have ha : raw606step1 = raw606step0 := by apply Matrix.ext; unfold raw606step1 raw606step0; decide +kernel
      have hl : raw606step0Labels = labelEmbedding1 ∘ raw606step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw606step0 raw606step0Labels raw606step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw607 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![-2, 1, 1], ![0, 2, -2]]
def raw607Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw607step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw607 raw607Labels = mixedMoment B node493 node493Labels := by
  calc
    mixedMoment B raw607 raw607Labels = mixedMoment B raw607step0 raw607step0Labels := by
      have ha : raw607step0 = (fun i j => raw607 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw607step0 raw607; decide +kernel
      have hl : raw607step0Labels = raw607Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw607 raw607Labels permutation145 permutation6
    _ = mixedMoment B node493 node493Labels := by rfl

def raw608 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0]]
def raw608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw608 raw608Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw608 raw608Labels = mixedMoment B raw608step0 raw608step0Labels := by
      have ha : raw608step0 = (fun i j => raw608 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw608step0 raw608; decide +kernel
      have hl : raw608step0Labels = raw608Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw608 raw608Labels permutation152 permutation5
    mixedMoment B raw608step0 raw608step0Labels = mixedMoment B raw608step1 raw608step1Labels := by
      have ha : raw608step1 = raw608step0 := by apply Matrix.ext; unfold raw608step1 raw608step0; decide +kernel
      have hl : raw608step0Labels = labelEmbedding1 ∘ raw608step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw608step0 raw608step0Labels raw608step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw609 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0]]
def raw609Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw609step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw609 raw609Labels = mixedMoment B node519 node519Labels := by
  calc
    mixedMoment B raw609 raw609Labels = mixedMoment B raw609step0 raw609step0Labels := by
      have ha : raw609step0 = (fun i j => raw609 (permutation157 i) (permutation4 j)) := by apply Matrix.ext; unfold raw609step0 raw609; decide +kernel
      have hl : raw609step0Labels = raw609Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw609 raw609Labels permutation157 permutation4
    _ = mixedMoment B node519 node519Labels := by rfl

def raw610 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw610 raw610Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw610 raw610Labels = mixedMoment B raw610step0 raw610step0Labels := by
      have ha : raw610step0 = (fun i j => raw610 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw610step0 raw610; decide +kernel
      have hl : raw610step0Labels = raw610Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw610 raw610Labels permutation32 permutation5
    mixedMoment B raw610step0 raw610step0Labels = mixedMoment B raw610step1 raw610step1Labels := by
      have ha : raw610step1 = raw610step0 := by apply Matrix.ext; unfold raw610step1 raw610step0; decide +kernel
      have hl : raw610step0Labels = labelEmbedding1 ∘ raw610step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw610step0 raw610step0Labels raw610step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw611 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, 2, -1]]
def raw611Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw611step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw611step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw611 raw611Labels = mixedMoment B node514 node514Labels := by
  calc
    mixedMoment B raw611 raw611Labels = mixedMoment B raw611step0 raw611step0Labels := by
      have ha : raw611step0 = (fun i j => raw611 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw611step0 raw611; decide +kernel
      have hl : raw611step0Labels = raw611Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw611 raw611Labels permutation151 permutation4
    mixedMoment B raw611step0 raw611step0Labels = mixedMoment B raw611step1 raw611step1Labels := by
      have ha : raw611step1 = -raw611step0 := by apply Matrix.ext; change ∀ i j, raw611step1 i j = -(raw611step0 i j); unfold raw611step1 raw611step0; decide +kernel
      have hl : raw611step1Labels = raw611step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node514 node514Labels := by rfl

def raw612 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1]]
def raw612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw612 raw612Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw612 raw612Labels = mixedMoment B raw612step0 raw612step0Labels := by
      have ha : raw612step0 = (fun i j => raw612 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw612step0 raw612; decide +kernel
      have hl : raw612step0Labels = raw612Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw612 raw612Labels permutation32 permutation5
    mixedMoment B raw612step0 raw612step0Labels = mixedMoment B raw612step1 raw612step1Labels := by
      have ha : raw612step1 = raw612step0 := by apply Matrix.ext; unfold raw612step1 raw612step0; decide +kernel
      have hl : raw612step0Labels = labelEmbedding1 ∘ raw612step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw612step0 raw612step0Labels raw612step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw613 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![-2, 1, 1]]
def raw613Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw613step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw613 raw613Labels = mixedMoment B node522 node522Labels := by
  calc
    mixedMoment B raw613 raw613Labels = mixedMoment B raw613step0 raw613step0Labels := by
      have ha : raw613step0 = (fun i j => raw613 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw613step0 raw613; decide +kernel
      have hl : raw613step0Labels = raw613Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw613 raw613Labels permutation37 permutation4
    _ = mixedMoment B node522 node522Labels := by rfl

def raw614 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0]]
def raw614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw614 raw614Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw614 raw614Labels = mixedMoment B raw614step0 raw614step0Labels := by
      have ha : raw614step0 = (fun i j => raw614 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw614step0 raw614; decide +kernel
      have hl : raw614step0Labels = raw614Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw614 raw614Labels permutation32 permutation5
    mixedMoment B raw614step0 raw614step0Labels = mixedMoment B raw614step1 raw614step1Labels := by
      have ha : raw614step1 = raw614step0 := by apply Matrix.ext; unfold raw614step1 raw614step0; decide +kernel
      have hl : raw614step0Labels = labelEmbedding1 ∘ raw614step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw614step0 raw614step0Labels raw614step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw615 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0]]
def raw615Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw615step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw615 raw615Labels = mixedMoment B node523 node523Labels := by
  calc
    mixedMoment B raw615 raw615Labels = mixedMoment B raw615step0 raw615step0Labels := by
      have ha : raw615step0 = (fun i j => raw615 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw615step0 raw615; decide +kernel
      have hl : raw615step0Labels = raw615Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw615 raw615Labels permutation35 permutation4
    _ = mixedMoment B node523 node523Labels := by rfl

def raw616 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw616 raw616Labels = mixedMoment B node4002 node4002Labels := by
  calc
    mixedMoment B raw616 raw616Labels = mixedMoment B raw616step0 raw616step0Labels := by
      have ha : raw616step0 = (fun i j => raw616 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw616step0 raw616; decide +kernel
      have hl : raw616step0Labels = raw616Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw616 raw616Labels permutation152 permutation5
    mixedMoment B raw616step0 raw616step0Labels = mixedMoment B raw616step1 raw616step1Labels := by
      have ha : raw616step1 = raw616step0 := by apply Matrix.ext; unfold raw616step1 raw616step0; decide +kernel
      have hl : raw616step0Labels = labelEmbedding1 ∘ raw616step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw616step0 raw616step0Labels raw616step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4002 node4002Labels := by rfl

def raw617 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw617Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw617step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw617 raw617Labels = mixedMoment B node513 node513Labels := by
  calc
    mixedMoment B raw617 raw617Labels = mixedMoment B raw617step0 raw617step0Labels := by
      have ha : raw617step0 = (fun i j => raw617 (permutation156 i) (permutation4 j)) := by apply Matrix.ext; unfold raw617step0 raw617; decide +kernel
      have hl : raw617step0Labels = raw617Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw617 raw617Labels permutation156 permutation4
    _ = mixedMoment B node513 node513Labels := by rfl

def raw618 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw618 raw618Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw618 raw618Labels = mixedMoment B raw618step0 raw618step0Labels := by
      have ha : raw618step0 = (fun i j => raw618 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw618step0 raw618; decide +kernel
      have hl : raw618step0Labels = raw618Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw618 raw618Labels permutation32 permutation5
    mixedMoment B raw618step0 raw618step0Labels = mixedMoment B raw618step1 raw618step1Labels := by
      have ha : raw618step1 = raw618step0 := by apply Matrix.ext; unfold raw618step1 raw618step0; decide +kernel
      have hl : raw618step0Labels = labelEmbedding1 ∘ raw618step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw618step0 raw618step0Labels raw618step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw619 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 2, -2]]
def raw619Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw619step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw619step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw619 raw619Labels = mixedMoment B node483 node483Labels := by
  calc
    mixedMoment B raw619 raw619Labels = mixedMoment B raw619step0 raw619step0Labels := by
      have ha : raw619step0 = (fun i j => raw619 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw619step0 raw619; decide +kernel
      have hl : raw619step0Labels = raw619Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw619 raw619Labels permutation151 permutation4
    mixedMoment B raw619step0 raw619step0Labels = mixedMoment B raw619step1 raw619step1Labels := by
      have ha : raw619step1 = -raw619step0 := by apply Matrix.ext; change ∀ i j, raw619step1 i j = -(raw619step0 i j); unfold raw619step1 raw619step0; decide +kernel
      have hl : raw619step1Labels = raw619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node483 node483Labels := by rfl

def raw620 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw620step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw620step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw620step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw620 raw620Labels = mixedMoment B node4004 node4004Labels := by
  calc
    mixedMoment B raw620 raw620Labels = mixedMoment B raw620step0 raw620step0Labels := by
      have ha : raw620step0 = (fun i j => raw620 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw620step0 raw620; decide +kernel
      have hl : raw620step0Labels = raw620Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw620 raw620Labels permutation8 permutation5
    mixedMoment B raw620step0 raw620step0Labels = mixedMoment B raw620step1 raw620step1Labels := by
      have ha : raw620step1 = raw620step0 := by apply Matrix.ext; unfold raw620step1 raw620step0; decide +kernel
      have hl : raw620step0Labels = labelEmbedding1 ∘ raw620step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw620step0 raw620step0Labels raw620step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4004 node4004Labels := by rfl

def raw621 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, -1, 2], ![1, 1, -2], ![-1, 2, -1]]
def raw621Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw621step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw621step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw621 raw621Labels = mixedMoment B node516 node516Labels := by
  calc
    mixedMoment B raw621 raw621Labels = mixedMoment B raw621step0 raw621step0Labels := by
      have ha : raw621step0 = (fun i j => raw621 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw621step0 raw621; decide +kernel
      have hl : raw621step0Labels = raw621Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw621 raw621Labels permutation8 permutation4
    _ = mixedMoment B node516 node516Labels := by rfl

def raw622 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2]]
def raw622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw622 raw622Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw622 raw622Labels = mixedMoment B raw622step0 raw622step0Labels := by
      have ha : raw622step0 = (fun i j => raw622 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw622step0 raw622; decide +kernel
      have hl : raw622step0Labels = raw622Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw622 raw622Labels permutation32 permutation5
    mixedMoment B raw622step0 raw622step0Labels = mixedMoment B raw622step1 raw622step1Labels := by
      have ha : raw622step1 = raw622step0 := by apply Matrix.ext; unfold raw622step1 raw622step0; decide +kernel
      have hl : raw622step0Labels = labelEmbedding1 ∘ raw622step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw622step0 raw622step0Labels raw622step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw623 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2]]
def raw623Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw623step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw623 raw623Labels = mixedMoment B node494 node494Labels := by
  calc
    mixedMoment B raw623 raw623Labels = mixedMoment B raw623step0 raw623step0Labels := by
      have ha : raw623step0 = (fun i j => raw623 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw623step0 raw623; decide +kernel
      have hl : raw623step0Labels = raw623Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw623 raw623Labels permutation137 permutation6
    _ = mixedMoment B node494 node494Labels := by rfl

def raw624 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw624 raw624Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw624 raw624Labels = mixedMoment B raw624step0 raw624step0Labels := by
      have ha : raw624step0 = (fun i j => raw624 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw624step0 raw624; decide +kernel
      have hl : raw624step0Labels = raw624Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw624 raw624Labels permutation32 permutation5
    mixedMoment B raw624step0 raw624step0Labels = mixedMoment B raw624step1 raw624step1Labels := by
      have ha : raw624step1 = raw624step0 := by apply Matrix.ext; unfold raw624step1 raw624step0; decide +kernel
      have hl : raw624step0Labels = labelEmbedding1 ∘ raw624step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw624step0 raw624step0Labels raw624step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw625 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0]]
def raw625Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw625step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw625step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw625 raw625Labels = mixedMoment B node526 node526Labels := by
  calc
    mixedMoment B raw625 raw625Labels = mixedMoment B raw625step0 raw625step0Labels := by
      have ha : raw625step0 = (fun i j => raw625 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw625step0 raw625; decide +kernel
      have hl : raw625step0Labels = raw625Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw625 raw625Labels permutation39 permutation4
    _ = mixedMoment B node526 node526Labels := by rfl

def raw626 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 2, -1]]
def raw626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw626step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw626step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw626 raw626Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw626 raw626Labels = mixedMoment B raw626step0 raw626step0Labels := by
      have ha : raw626step0 = (fun i j => raw626 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw626step0 raw626; decide +kernel
      have hl : raw626step0Labels = raw626Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw626 raw626Labels permutation8 permutation5
    mixedMoment B raw626step0 raw626step0Labels = mixedMoment B raw626step1 raw626step1Labels := by
      have ha : raw626step1 = raw626step0 := by apply Matrix.ext; unfold raw626step1 raw626step0; decide +kernel
      have hl : raw626step0Labels = labelEmbedding1 ∘ raw626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw626step0 raw626step0Labels raw626step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4014 node4014Labels := by rfl

def raw627 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![-1, 0, 1], ![-1, 2, -1]]
def raw627Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw627step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw627step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw627 raw627Labels = mixedMoment B node527 node527Labels := by
  calc
    mixedMoment B raw627 raw627Labels = mixedMoment B raw627step0 raw627step0Labels := by
      have ha : raw627step0 = (fun i j => raw627 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw627step0 raw627; decide +kernel
      have hl : raw627step0Labels = raw627Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw627 raw627Labels permutation10 permutation4
    _ = mixedMoment B node527 node527Labels := by rfl

def raw628 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw628step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw628step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw628 raw628Labels = mixedMoment B node4015 node4015Labels := by
  calc
    mixedMoment B raw628 raw628Labels = mixedMoment B raw628step0 raw628step0Labels := by
      have ha : raw628step0 = (fun i j => raw628 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw628step0 raw628; decide +kernel
      have hl : raw628step0Labels = raw628Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw628 raw628Labels permutation8 permutation5
    mixedMoment B raw628step0 raw628step0Labels = mixedMoment B raw628step1 raw628step1Labels := by
      have ha : raw628step1 = raw628step0 := by apply Matrix.ext; unfold raw628step1 raw628step0; decide +kernel
      have hl : raw628step0Labels = labelEmbedding1 ∘ raw628step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw628step0 raw628step0Labels raw628step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw629 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 1, 1]]
def raw629Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw629step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw629step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw629 raw629Labels = mixedMoment B node528 node528Labels := by
  calc
    mixedMoment B raw629 raw629Labels = mixedMoment B raw629step0 raw629step0Labels := by
      have ha : raw629step0 = (fun i j => raw629 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw629step0 raw629; decide +kernel
      have hl : raw629step0Labels = raw629Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw629 raw629Labels permutation31 permutation3
    _ = mixedMoment B node528 node528Labels := by rfl

def raw630 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, 1, 0]]
def raw630Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw630step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw630step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw630step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw630 raw630Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw630 raw630Labels = mixedMoment B raw630step0 raw630step0Labels := by
      have ha : raw630step0 = (fun i j => raw630 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw630step0 raw630; decide +kernel
      have hl : raw630step0Labels = raw630Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw630 raw630Labels permutation8 permutation5
    mixedMoment B raw630step0 raw630step0Labels = mixedMoment B raw630step1 raw630step1Labels := by
      have ha : raw630step1 = raw630step0 := by apply Matrix.ext; unfold raw630step1 raw630step0; decide +kernel
      have hl : raw630step0Labels = labelEmbedding1 ∘ raw630step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw630step0 raw630step0Labels raw630step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw631 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -2, 1], ![-1, 0, 1], ![1, 1, -2], ![-1, 1, 0]]
def raw631Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw631step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw631step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw631 raw631Labels = mixedMoment B node528 node528Labels := by
  calc
    mixedMoment B raw631 raw631Labels = mixedMoment B raw631step0 raw631step0Labels := by
      have ha : raw631step0 = (fun i j => raw631 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw631step0 raw631; decide +kernel
      have hl : raw631step0Labels = raw631Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw631 raw631Labels permutation9 permutation4
    _ = mixedMoment B node528 node528Labels := by rfl

def raw632 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -2, 1], ![1, 1, -2], ![-2, 1, 1]]
def raw632Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw632step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw632step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw632step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw632 raw632Labels = mixedMoment B node4020 node4020Labels := by
  calc
    mixedMoment B raw632 raw632Labels = mixedMoment B raw632step0 raw632step0Labels := by
      have ha : raw632step0 = (fun i j => raw632 (permutation2 i) (permutation5 j)) := by apply Matrix.ext; unfold raw632step0 raw632; decide +kernel
      have hl : raw632step0Labels = raw632Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw632 raw632Labels permutation2 permutation5
    mixedMoment B raw632step0 raw632step0Labels = mixedMoment B raw632step1 raw632step1Labels := by
      have ha : raw632step1 = raw632step0 := by apply Matrix.ext; unfold raw632step1 raw632step0; decide +kernel
      have hl : raw632step0Labels = labelEmbedding1 ∘ raw632step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw632step0 raw632step0Labels raw632step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4020 node4020Labels := by rfl

def raw633 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -2, 1], ![1, 1, -2], ![-2, 1, 1]]
def raw633Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw633step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw633step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw633 raw633Labels = mixedMoment B node530 node530Labels := by
  calc
    mixedMoment B raw633 raw633Labels = mixedMoment B raw633step0 raw633step0Labels := by
      have ha : raw633step0 = (fun i j => raw633 (permutation6 i) (permutation2 j)) := by apply Matrix.ext; unfold raw633step0 raw633; decide +kernel
      have hl : raw633step0Labels = raw633Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw633 raw633Labels permutation6 permutation2
    _ = mixedMoment B node530 node530Labels := by rfl

def raw634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw634Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw634step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw634 raw634Labels = mixedMoment B node4023 node4023Labels := by
  calc
    mixedMoment B raw634 raw634Labels = mixedMoment B raw634step0 raw634step0Labels := by
      have ha : raw634step0 = (fun i j => raw634 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw634step0 raw634; decide +kernel
      have hl : raw634step0Labels = raw634Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw634 raw634Labels permutation152 permutation5
    mixedMoment B raw634step0 raw634step0Labels = mixedMoment B raw634step1 raw634step1Labels := by
      have ha : raw634step1 = raw634step0 := by apply Matrix.ext; unfold raw634step1 raw634step0; decide +kernel
      have hl : raw634step0Labels = labelEmbedding1 ∘ raw634step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw634step0 raw634step0Labels raw634step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4023 node4023Labels := by rfl

def raw635 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw635Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw635step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw635 raw635Labels = mixedMoment B node456 node456Labels := by
  calc
    mixedMoment B raw635 raw635Labels = mixedMoment B raw635step0 raw635step0Labels := by
      have ha : raw635step0 = (fun i j => raw635 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw635step0 raw635; decide +kernel
      have hl : raw635step0Labels = raw635Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw635 raw635Labels permutation176 permutation4
    _ = mixedMoment B node456 node456Labels := by rfl

def raw636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw636Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw636step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw636 raw636Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw636 raw636Labels = mixedMoment B raw636step0 raw636step0Labels := by
      have ha : raw636step0 = (fun i j => raw636 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw636step0 raw636; decide +kernel
      have hl : raw636step0Labels = raw636Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw636 raw636Labels permutation152 permutation5
    mixedMoment B raw636step0 raw636step0Labels = mixedMoment B raw636step1 raw636step1Labels := by
      have ha : raw636step1 = raw636step0 := by apply Matrix.ext; unfold raw636step1 raw636step0; decide +kernel
      have hl : raw636step0Labels = labelEmbedding1 ∘ raw636step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw636step0 raw636step0Labels raw636step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw637 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0]]
def raw637Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw637step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw637step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw637 raw637Labels = mixedMoment B node486 node486Labels := by
  calc
    mixedMoment B raw637 raw637Labels = mixedMoment B raw637step0 raw637step0Labels := by
      have ha : raw637step0 = (fun i j => raw637 (permutation194 i) (permutation6 j)) := by apply Matrix.ext; unfold raw637step0 raw637; decide +kernel
      have hl : raw637step0Labels = raw637Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw637 raw637Labels permutation194 permutation6
    mixedMoment B raw637step0 raw637step0Labels = mixedMoment B raw637step1 raw637step1Labels := by
      have ha : raw637step1 = -raw637step0 := by apply Matrix.ext; change ∀ i j, raw637step1 i j = -(raw637step0 i j); unfold raw637step1 raw637step0; decide +kernel
      have hl : raw637step1Labels = raw637step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node486 node486Labels := by rfl

def raw638 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw638step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw638 raw638Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw638 raw638Labels = mixedMoment B raw638step0 raw638step0Labels := by
      have ha : raw638step0 = (fun i j => raw638 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw638step0 raw638; decide +kernel
      have hl : raw638step0Labels = raw638Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw638 raw638Labels permutation32 permutation5
    mixedMoment B raw638step0 raw638step0Labels = mixedMoment B raw638step1 raw638step1Labels := by
      have ha : raw638step1 = raw638step0 := by apply Matrix.ext; unfold raw638step1 raw638step0; decide +kernel
      have hl : raw638step0Labels = labelEmbedding1 ∘ raw638step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw638step0 raw638step0Labels raw638step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw639 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -2, 2], ![2, -1, -1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2]]
def raw639Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw639step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw639step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw639 raw639Labels = mixedMoment B node487 node487Labels := by
  calc
    mixedMoment B raw639 raw639Labels = mixedMoment B raw639step0 raw639step0Labels := by
      have ha : raw639step0 = (fun i j => raw639 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw639step0 raw639; decide +kernel
      have hl : raw639step0Labels = raw639Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw639 raw639Labels permutation151 permutation4
    mixedMoment B raw639step0 raw639step0Labels = mixedMoment B raw639step1 raw639step1Labels := by
      have ha : raw639step1 = -raw639step0 := by apply Matrix.ext; change ∀ i j, raw639step1 i j = -(raw639step0 i j); unfold raw639step1 raw639step0; decide +kernel
      have hl : raw639step1Labels = raw639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node487 node487Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
