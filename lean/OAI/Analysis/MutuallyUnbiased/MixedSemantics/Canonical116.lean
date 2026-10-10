import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14848 raw14848Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw14848 raw14848Labels = mixedMoment B raw14848step0 raw14848step0Labels := by
      have hz : ∀ j, raw14848 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14848step0 = (fun i j => raw14848 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14848step0 raw14848; decide +kernel
      have hl : raw14848step0Labels = raw14848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14848 raw14848Labels permutation265 hz
    mixedMoment B raw14848step0 raw14848step0Labels = mixedMoment B raw14848step1 raw14848step1Labels := by
      have ha : raw14848step1 = (fun i j => raw14848step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14848step1 raw14848step0; decide +kernel
      have hl : raw14848step1Labels = raw14848step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14848step0 raw14848step0Labels permutation97 permutation6
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw14849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14849 raw14849Labels = mixedMoment B node2907 node2907Labels := by
  calc
    mixedMoment B raw14849 raw14849Labels = mixedMoment B raw14849step0 raw14849step0Labels := by
      have ha : raw14849step0 = (fun i j => raw14849 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14849step0 raw14849; decide +kernel
      have hl : raw14849step0Labels = raw14849Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14849 raw14849Labels permutation160 permutation3
    _ = mixedMoment B node2907 node2907Labels := by rfl

def raw14850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14850step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14850 raw14850Labels = mixedMoment B node3712 node3712Labels := by
  calc
    mixedMoment B raw14850 raw14850Labels = mixedMoment B raw14850step0 raw14850step0Labels := by
      have ha : raw14850step0 = (fun i j => raw14850 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14850step0 raw14850; decide +kernel
      have hl : raw14850step0Labels = raw14850Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14850 raw14850Labels permutation273 permutation3
    _ = mixedMoment B node3712 node3712Labels := by rfl

def raw14851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw14851step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14851 raw14851Labels = mixedMoment B node3518 node3518Labels := by
  calc
    mixedMoment B raw14851 raw14851Labels = mixedMoment B raw14851step0 raw14851step0Labels := by
      have ha : raw14851step0 = (fun i j => raw14851 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14851step0 raw14851; decide +kernel
      have hl : raw14851step0Labels = raw14851Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14851 raw14851Labels permutation494 permutation6
    _ = mixedMoment B node3518 node3518Labels := by rfl

def raw14852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14852step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14852step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14852step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14852 raw14852Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw14852 raw14852Labels = mixedMoment B raw14852step0 raw14852step0Labels := by
      have ha : raw14852step0 = (fun i j => raw14852 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14852step0 raw14852; decide +kernel
      have hl : raw14852step0Labels = raw14852Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14852 raw14852Labels permutation646 permutation3
    mixedMoment B raw14852step0 raw14852step0Labels = mixedMoment B raw14852step1 raw14852step1Labels := by
      have ha : raw14852step1 = -raw14852step0 := by apply Matrix.ext; change ∀ i j, raw14852step1 i j = -(raw14852step0 i j); unfold raw14852step1 raw14852step0; decide +kernel
      have hl : raw14852step1Labels = raw14852step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw14853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14853 raw14853Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw14853 raw14853Labels = mixedMoment B raw14853step0 raw14853step0Labels := by
      have ha : raw14853step0 = (fun i j => raw14853 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14853step0 raw14853; decide +kernel
      have hl : raw14853step0Labels = raw14853Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14853 raw14853Labels permutation494 permutation6
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw14854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14854 raw14854Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw14854 raw14854Labels = mixedMoment B raw14854step0 raw14854step0Labels := by
      have ha : raw14854step0 = (fun i j => raw14854 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14854step0 raw14854; decide +kernel
      have hl : raw14854step0Labels = raw14854Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14854 raw14854Labels permutation152 permutation3
    _ = mixedMoment B node2933 node2933Labels := by rfl

def raw14855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14855 raw14855Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw14855 raw14855Labels = mixedMoment B raw14855step0 raw14855step0Labels := by
      have ha : raw14855step0 = (fun i j => raw14855 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14855step0 raw14855; decide +kernel
      have hl : raw14855step0Labels = raw14855Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14855 raw14855Labels permutation265 permutation3
    _ = mixedMoment B node3723 node3723Labels := by rfl

def raw14856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14856step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14856 raw14856Labels = mixedMoment B node3830 node3830Labels := by
  calc
    mixedMoment B raw14856 raw14856Labels = mixedMoment B raw14856step0 raw14856step0Labels := by
      have ha : raw14856step0 = (fun i j => raw14856 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14856step0 raw14856; decide +kernel
      have hl : raw14856step0Labels = raw14856Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14856 raw14856Labels permutation688 permutation3
    mixedMoment B raw14856step0 raw14856step0Labels = mixedMoment B raw14856step1 raw14856step1Labels := by
      have ha : raw14856step1 = -raw14856step0 := by apply Matrix.ext; change ∀ i j, raw14856step1 i j = -(raw14856step0 i j); unfold raw14856step1 raw14856step0; decide +kernel
      have hl : raw14856step1Labels = raw14856step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3830 node3830Labels := by rfl

def raw14857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw14857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14857step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14857 raw14857Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw14857 raw14857Labels = mixedMoment B raw14857step0 raw14857step0Labels := by
      have ha : raw14857step0 = (fun i j => raw14857 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14857step0 raw14857; decide +kernel
      have hl : raw14857step0Labels = raw14857Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14857 raw14857Labels permutation658 permutation3
    mixedMoment B raw14857step0 raw14857step0Labels = mixedMoment B raw14857step1 raw14857step1Labels := by
      have ha : raw14857step1 = -raw14857step0 := by apply Matrix.ext; change ∀ i j, raw14857step1 i j = -(raw14857step0 i j); unfold raw14857step1 raw14857step0; decide +kernel
      have hl : raw14857step1Labels = raw14857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw14858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw14858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14858 raw14858Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw14858 raw14858Labels = mixedMoment B raw14858step0 raw14858step0Labels := by
      have ha : raw14858step0 = (fun i j => raw14858 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14858step0 raw14858; decide +kernel
      have hl : raw14858step0Labels = raw14858Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14858 raw14858Labels permutation494 permutation6
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw14859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14859 raw14859Labels = mixedMoment B node2905 node2905Labels := by
  calc
    mixedMoment B raw14859 raw14859Labels = mixedMoment B raw14859step0 raw14859step0Labels := by
      have ha : raw14859step0 = (fun i j => raw14859 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14859step0 raw14859; decide +kernel
      have hl : raw14859step0Labels = raw14859Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14859 raw14859Labels permutation158 permutation3
    _ = mixedMoment B node2905 node2905Labels := by rfl

def raw14860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw14860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14860 raw14860Labels = mixedMoment B node3679 node3679Labels := by
  calc
    mixedMoment B raw14860 raw14860Labels = mixedMoment B raw14860step0 raw14860step0Labels := by
      have ha : raw14860step0 = (fun i j => raw14860 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14860step0 raw14860; decide +kernel
      have hl : raw14860step0Labels = raw14860Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14860 raw14860Labels permutation681 permutation3
    mixedMoment B raw14860step0 raw14860step0Labels = mixedMoment B raw14860step1 raw14860step1Labels := by
      have ha : raw14860step1 = -raw14860step0 := by apply Matrix.ext; change ∀ i j, raw14860step1 i j = -(raw14860step0 i j); unfold raw14860step1 raw14860step0; decide +kernel
      have hl : raw14860step1Labels = raw14860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3679 node3679Labels := by rfl

def raw14861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14861 raw14861Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw14861 raw14861Labels = mixedMoment B raw14861step0 raw14861step0Labels := by
      have ha : raw14861step0 = (fun i j => raw14861 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14861step0 raw14861; decide +kernel
      have hl : raw14861step0Labels = raw14861Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14861 raw14861Labels permutation688 permutation3
    mixedMoment B raw14861step0 raw14861step0Labels = mixedMoment B raw14861step1 raw14861step1Labels := by
      have ha : raw14861step1 = -raw14861step0 := by apply Matrix.ext; change ∀ i j, raw14861step1 i j = -(raw14861step0 i j); unfold raw14861step1 raw14861step0; decide +kernel
      have hl : raw14861step1Labels = raw14861step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3698 node3698Labels := by rfl

def raw14862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14862 raw14862Labels = mixedMoment B node3561 node3561Labels := by
  calc
    mixedMoment B raw14862 raw14862Labels = mixedMoment B raw14862step0 raw14862step0Labels := by
      have ha : raw14862step0 = (fun i j => raw14862 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14862step0 raw14862; decide +kernel
      have hl : raw14862step0Labels = raw14862Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14862 raw14862Labels permutation494 permutation6
    _ = mixedMoment B node3561 node3561Labels := by rfl

def raw14863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw14863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14863 raw14863Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw14863 raw14863Labels = mixedMoment B raw14863step0 raw14863step0Labels := by
      have ha : raw14863step0 = (fun i j => raw14863 (permutation494 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14863step0 raw14863; decide +kernel
      have hl : raw14863step0Labels = raw14863Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14863 raw14863Labels permutation494 permutation6
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw14864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw14864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw14864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14864 raw14864Labels = mixedMoment B node1992 node1992Labels := by
  calc
    mixedMoment B raw14864 raw14864Labels = mixedMoment B raw14864step0 raw14864step0Labels := by
      have ha : raw14864step0 = (fun i j => raw14864 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14864step0 raw14864; decide +kernel
      have hl : raw14864step0Labels = raw14864Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14864 raw14864Labels permutation682 permutation3
    mixedMoment B raw14864step0 raw14864step0Labels = mixedMoment B raw14864step1 raw14864step1Labels := by
      have ha : raw14864step1 = -raw14864step0 := by apply Matrix.ext; change ∀ i j, raw14864step1 i j = -(raw14864step0 i j); unfold raw14864step1 raw14864step0; decide +kernel
      have hl : raw14864step1Labels = raw14864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1992 node1992Labels := by rfl

def raw14865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw14865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14865 raw14865Labels = mixedMoment B node1993 node1993Labels := by
  calc
    mixedMoment B raw14865 raw14865Labels = mixedMoment B raw14865step0 raw14865step0Labels := by
      have ha : raw14865step0 = (fun i j => raw14865 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14865step0 raw14865; decide +kernel
      have hl : raw14865step0Labels = raw14865Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14865 raw14865Labels permutation681 permutation3
    mixedMoment B raw14865step0 raw14865step0Labels = mixedMoment B raw14865step1 raw14865step1Labels := by
      have ha : raw14865step1 = -raw14865step0 := by apply Matrix.ext; change ∀ i j, raw14865step1 i j = -(raw14865step0 i j); unfold raw14865step1 raw14865step0; decide +kernel
      have hl : raw14865step1Labels = raw14865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1993 node1993Labels := by rfl

def raw14866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14866step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14866 raw14866Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw14866 raw14866Labels = mixedMoment B raw14866step0 raw14866step0Labels := by
      have ha : raw14866step0 = (fun i j => raw14866 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14866step0 raw14866; decide +kernel
      have hl : raw14866step0Labels = raw14866Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14866 raw14866Labels permutation688 permutation3
    mixedMoment B raw14866step0 raw14866step0Labels = mixedMoment B raw14866step1 raw14866step1Labels := by
      have ha : raw14866step1 = -raw14866step0 := by apply Matrix.ext; change ∀ i j, raw14866step1 i j = -(raw14866step0 i j); unfold raw14866step1 raw14866step0; decide +kernel
      have hl : raw14866step1Labels = raw14866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2034 node2034Labels := by rfl

def raw14867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw14867step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw14867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14867 raw14867Labels = mixedMoment B node2001 node2001Labels := by
  calc
    mixedMoment B raw14867 raw14867Labels = mixedMoment B raw14867step0 raw14867step0Labels := by
      have ha : raw14867step0 = (fun i j => raw14867 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14867step0 raw14867; decide +kernel
      have hl : raw14867step0Labels = raw14867Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14867 raw14867Labels permutation680 permutation3
    mixedMoment B raw14867step0 raw14867step0Labels = mixedMoment B raw14867step1 raw14867step1Labels := by
      have ha : raw14867step1 = -raw14867step0 := by apply Matrix.ext; change ∀ i j, raw14867step1 i j = -(raw14867step0 i j); unfold raw14867step1 raw14867step0; decide +kernel
      have hl : raw14867step1Labels = raw14867step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2001 node2001Labels := by rfl

def raw14868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw14868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14868 raw14868Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw14868 raw14868Labels = mixedMoment B raw14868step0 raw14868step0Labels := by
      have ha : raw14868step0 = (fun i j => raw14868 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14868step0 raw14868; decide +kernel
      have hl : raw14868step0Labels = raw14868Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14868 raw14868Labels permutation646 permutation3
    mixedMoment B raw14868step0 raw14868step0Labels = mixedMoment B raw14868step1 raw14868step1Labels := by
      have ha : raw14868step1 = -raw14868step0 := by apply Matrix.ext; change ∀ i j, raw14868step1 i j = -(raw14868step0 i j); unfold raw14868step1 raw14868step0; decide +kernel
      have hl : raw14868step1Labels = raw14868step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw14869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14869Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14869 raw14869Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw14869 raw14869Labels = mixedMoment B raw14869step0 raw14869step0Labels := by
      have ha : raw14869step0 = (fun i j => raw14869 (permutation461 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14869step0 raw14869; decide +kernel
      have hl : raw14869step0Labels = raw14869Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14869 raw14869Labels permutation461 permutation4
    mixedMoment B raw14869step0 raw14869step0Labels = mixedMoment B raw14869step1 raw14869step1Labels := by
      have ha : raw14869step1 = -raw14869step0 := by apply Matrix.ext; change ∀ i j, raw14869step1 i j = -(raw14869step0 i j); unfold raw14869step1 raw14869step0; decide +kernel
      have hl : raw14869step1Labels = raw14869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3722 node3722Labels := by rfl

def raw14870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14870Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14870 raw14870Labels = mixedMoment B node3841 node3841Labels := by
  calc
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw14871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14871Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14871 raw14871Labels = mixedMoment B node3717 node3717Labels := by
  calc
    mixedMoment B raw14871 raw14871Labels = mixedMoment B raw14871step0 raw14871step0Labels := by
      have ha : raw14871step0 = (fun i j => raw14871 (permutation460 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14871step0 raw14871; decide +kernel
      have hl : raw14871step0Labels = raw14871Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14871 raw14871Labels permutation460 permutation4
    mixedMoment B raw14871step0 raw14871step0Labels = mixedMoment B raw14871step1 raw14871step1Labels := by
      have ha : raw14871step1 = -raw14871step0 := by apply Matrix.ext; change ∀ i j, raw14871step1 i j = -(raw14871step0 i j); unfold raw14871step1 raw14871step0; decide +kernel
      have hl : raw14871step1Labels = raw14871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3717 node3717Labels := by rfl

def raw14872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14872Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14872 raw14872Labels = mixedMoment B node3722 node3722Labels := by
  calc
    mixedMoment B raw14872 raw14872Labels = mixedMoment B raw14872step0 raw14872step0Labels := by
      have ha : raw14872step0 = (fun i j => raw14872 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14872step0 raw14872; decide +kernel
      have hl : raw14872step0Labels = raw14872Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14872 raw14872Labels permutation154 permutation2
    _ = mixedMoment B node3722 node3722Labels := by rfl

def raw14873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw14873Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14873 raw14873Labels = mixedMoment B node3717 node3717Labels := by
  calc
    mixedMoment B raw14873 raw14873Labels = mixedMoment B raw14873step0 raw14873step0Labels := by
      have ha : raw14873step0 = (fun i j => raw14873 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14873step0 raw14873; decide +kernel
      have hl : raw14873step0Labels = raw14873Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14873 raw14873Labels permutation153 permutation2
    _ = mixedMoment B node3717 node3717Labels := by rfl

def raw14874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14874Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw14874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14874 raw14874Labels = mixedMoment B node3194 node3194Labels := by
  calc
    mixedMoment B raw14874 raw14874Labels = mixedMoment B raw14874step0 raw14874step0Labels := by
      have ha : raw14874step0 = (fun i j => raw14874 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14874step0 raw14874; decide +kernel
      have hl : raw14874step0Labels = raw14874Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14874 raw14874Labels permutation688 permutation2
    mixedMoment B raw14874step0 raw14874step0Labels = mixedMoment B raw14874step1 raw14874step1Labels := by
      have ha : raw14874step1 = -raw14874step0 := by apply Matrix.ext; change ∀ i j, raw14874step1 i j = -(raw14874step0 i j); unfold raw14874step1 raw14874step0; decide +kernel
      have hl : raw14874step1Labels = raw14874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3194 node3194Labels := by rfl

def raw14875 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1], ![0, 0]]
def raw14875Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14875step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw14875step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14875step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw14875step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14875step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw14875step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14875 raw14875Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw14875 raw14875Labels = mixedMoment B raw14875step0 raw14875step0Labels := by
      have hz : ∀ j, raw14875 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14875step0 = (fun i j => raw14875 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14875step0 raw14875; decide +kernel
      have hl : raw14875step0Labels = raw14875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14875 raw14875Labels permutation590 hz
    mixedMoment B raw14875step0 raw14875step0Labels = mixedMoment B raw14875step1 raw14875step1Labels := by
      have hz : ∀ j, raw14875step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14875step1 = (fun i j => raw14875step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14875step1 raw14875step0; decide +kernel
      have hl : raw14875step1Labels = raw14875step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14875step0 raw14875step0Labels permutation56 hz
    mixedMoment B raw14875step1 raw14875step1Labels = mixedMoment B raw14875step2 raw14875step2Labels := by
      have ha : raw14875step2 = (fun i j => raw14875step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14875step2 raw14875step1; decide +kernel
      have hl : raw14875step2Labels = raw14875step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14875step1 raw14875step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw14876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14876step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14876step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14876step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14876step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14876step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14876step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14876 raw14876Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw14876 raw14876Labels = mixedMoment B raw14876step0 raw14876step0Labels := by
      have hz : ∀ j, raw14876 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14876step0 = (fun i j => raw14876 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14876step0 raw14876; decide +kernel
      have hl : raw14876step0Labels = raw14876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14876 raw14876Labels permutation434 hz
    mixedMoment B raw14876step0 raw14876step0Labels = mixedMoment B raw14876step1 raw14876step1Labels := by
      have hz : ∀ j, raw14876step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14876step1 = (fun i j => raw14876step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14876step1 raw14876step0; decide +kernel
      have hl : raw14876step1Labels = raw14876step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14876step0 raw14876step0Labels permutation80 hz
    mixedMoment B raw14876step1 raw14876step1Labels = mixedMoment B raw14876step2 raw14876step2Labels := by
      have ha : raw14876step2 = (fun i j => raw14876step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14876step2 raw14876step1; decide +kernel
      have hl : raw14876step2Labels = raw14876step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14876step1 raw14876step1Labels permutation14 permutation3
    mixedMoment B raw14876step2 raw14876step2Labels = mixedMoment B raw14876step3 raw14876step3Labels := by
      have ha : raw14876step3 = raw14876step2 := by apply Matrix.ext; unfold raw14876step3 raw14876step2; decide +kernel
      have hl : raw14876step2Labels = labelEmbedding6 ∘ raw14876step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14876step2 raw14876step2Labels raw14876step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

def raw14877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14877step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14877step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14877step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14877 raw14877Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw14877 raw14877Labels = mixedMoment B raw14877step0 raw14877step0Labels := by
      have hz : ∀ j, raw14877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14877step0 = (fun i j => raw14877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14877step0 raw14877; decide +kernel
      have hl : raw14877step0Labels = raw14877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14877 raw14877Labels permutation434 hz
    mixedMoment B raw14877step0 raw14877step0Labels = mixedMoment B raw14877step1 raw14877step1Labels := by
      have ha : raw14877step1 = (fun i j => raw14877step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14877step1 raw14877step0; decide +kernel
      have hl : raw14877step1Labels = raw14877step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14877step0 raw14877step0Labels permutation146 permutation3
    mixedMoment B raw14877step1 raw14877step1Labels = mixedMoment B raw14877step2 raw14877step2Labels := by
      have ha : raw14877step2 = -raw14877step1 := by apply Matrix.ext; change ∀ i j, raw14877step2 i j = -(raw14877step1 i j); unfold raw14877step2 raw14877step1; decide +kernel
      have hl : raw14877step2Labels = raw14877step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14877step2 raw14877step2Labels = mixedMoment B raw14877step3 raw14877step3Labels := by
      have ha : raw14877step3 = raw14877step2 := by apply Matrix.ext; unfold raw14877step3 raw14877step2; decide +kernel
      have hl : raw14877step2Labels = labelEmbedding6 ∘ raw14877step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14877step2 raw14877step2Labels raw14877step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw14878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14878step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14878step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14878step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14878step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14878 raw14878Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw14878 raw14878Labels = mixedMoment B raw14878step0 raw14878step0Labels := by
      have hz : ∀ j, raw14878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14878step0 = (fun i j => raw14878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14878step0 raw14878; decide +kernel
      have hl : raw14878step0Labels = raw14878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14878 raw14878Labels permutation346 hz
    mixedMoment B raw14878step0 raw14878step0Labels = mixedMoment B raw14878step1 raw14878step1Labels := by
      have ha : raw14878step1 = (fun i j => raw14878step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14878step1 raw14878step0; decide +kernel
      have hl : raw14878step1Labels = raw14878step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14878step0 raw14878step0Labels permutation146 permutation3
    mixedMoment B raw14878step1 raw14878step1Labels = mixedMoment B raw14878step2 raw14878step2Labels := by
      have ha : raw14878step2 = -raw14878step1 := by apply Matrix.ext; change ∀ i j, raw14878step2 i j = -(raw14878step1 i j); unfold raw14878step2 raw14878step1; decide +kernel
      have hl : raw14878step2Labels = raw14878step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14878step2 raw14878step2Labels = mixedMoment B raw14878step3 raw14878step3Labels := by
      have ha : raw14878step3 = raw14878step2 := by apply Matrix.ext; unfold raw14878step3 raw14878step2; decide +kernel
      have hl : raw14878step2Labels = labelEmbedding6 ∘ raw14878step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14878step2 raw14878step2Labels raw14878step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw14879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14879step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14879step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14879step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw14879step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14879step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw14879step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14879 raw14879Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw14879 raw14879Labels = mixedMoment B raw14879step0 raw14879step0Labels := by
      have hz : ∀ j, raw14879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14879step0 = (fun i j => raw14879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14879step0 raw14879; decide +kernel
      have hl : raw14879step0Labels = raw14879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14879 raw14879Labels permutation434 hz
    mixedMoment B raw14879step0 raw14879step0Labels = mixedMoment B raw14879step1 raw14879step1Labels := by
      have hz : ∀ j, raw14879step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14879step1 = (fun i j => raw14879step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14879step1 raw14879step0; decide +kernel
      have hl : raw14879step1Labels = raw14879step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14879step0 raw14879step0Labels permutation80 hz
    mixedMoment B raw14879step1 raw14879step1Labels = mixedMoment B raw14879step2 raw14879step2Labels := by
      have ha : raw14879step2 = (fun i j => raw14879step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14879step2 raw14879step1; decide +kernel
      have hl : raw14879step2Labels = raw14879step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14879step1 raw14879step1Labels permutation23 permutation6
    mixedMoment B raw14879step2 raw14879step2Labels = mixedMoment B raw14879step3 raw14879step3Labels := by
      have ha : raw14879step3 = raw14879step2 := by apply Matrix.ext; unfold raw14879step3 raw14879step2; decide +kernel
      have hl : raw14879step2Labels = labelEmbedding9 ∘ raw14879step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14879step2 raw14879step2Labels raw14879step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw14880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14880step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14880 raw14880Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw14880 raw14880Labels = mixedMoment B raw14880step0 raw14880step0Labels := by
      have hz : ∀ j, raw14880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14880step0 = (fun i j => raw14880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14880step0 raw14880; decide +kernel
      have hl : raw14880step0Labels = raw14880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14880 raw14880Labels permutation434 hz
    mixedMoment B raw14880step0 raw14880step0Labels = mixedMoment B raw14880step1 raw14880step1Labels := by
      have ha : raw14880step1 = (fun i j => raw14880step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14880step1 raw14880step0; decide +kernel
      have hl : raw14880step1Labels = raw14880step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14880step0 raw14880step0Labels permutation58 permutation3
    mixedMoment B raw14880step1 raw14880step1Labels = mixedMoment B raw14880step2 raw14880step2Labels := by
      have ha : raw14880step2 = raw14880step1 := by apply Matrix.ext; unfold raw14880step2 raw14880step1; decide +kernel
      have hl : raw14880step1Labels = labelEmbedding6 ∘ raw14880step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14880step1 raw14880step1Labels raw14880step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw14881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14881step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14881step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14881step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14881step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14881 raw14881Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw14881 raw14881Labels = mixedMoment B raw14881step0 raw14881step0Labels := by
      have ha : raw14881step0 = (fun i j => raw14881 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14881step0 raw14881; decide +kernel
      have hl : raw14881step0Labels = raw14881Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14881 raw14881Labels permutation644 permutation3
    mixedMoment B raw14881step0 raw14881step0Labels = mixedMoment B raw14881step1 raw14881step1Labels := by
      have ha : raw14881step1 = -raw14881step0 := by apply Matrix.ext; change ∀ i j, raw14881step1 i j = -(raw14881step0 i j); unfold raw14881step1 raw14881step0; decide +kernel
      have hl : raw14881step1Labels = raw14881step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14881step1 raw14881step1Labels = mixedMoment B raw14881step2 raw14881step2Labels := by
      have ha : raw14881step2 = raw14881step1 := by apply Matrix.ext; unfold raw14881step2 raw14881step1; decide +kernel
      have hl : raw14881step1Labels = labelEmbedding6 ∘ raw14881step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14881step1 raw14881step1Labels raw14881step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw14882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14882 raw14882Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw14882 raw14882Labels = mixedMoment B raw14882step0 raw14882step0Labels := by
      have hz : ∀ j, raw14882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14882step0 = (fun i j => raw14882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14882step0 raw14882; decide +kernel
      have hl : raw14882step0Labels = raw14882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14882 raw14882Labels permutation434 hz
    mixedMoment B raw14882step0 raw14882step0Labels = mixedMoment B raw14882step1 raw14882step1Labels := by
      have ha : raw14882step1 = (fun i j => raw14882step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14882step1 raw14882step0; decide +kernel
      have hl : raw14882step1Labels = raw14882step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14882step0 raw14882step0Labels permutation33 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw14883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14883step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14883step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14883 raw14883Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw14883 raw14883Labels = mixedMoment B raw14883step0 raw14883step0Labels := by
      have hz : ∀ j, raw14883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14883step0 = (fun i j => raw14883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14883step0 raw14883; decide +kernel
      have hl : raw14883step0Labels = raw14883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14883 raw14883Labels permutation346 hz
    mixedMoment B raw14883step0 raw14883step0Labels = mixedMoment B raw14883step1 raw14883step1Labels := by
      have ha : raw14883step1 = (fun i j => raw14883step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14883step1 raw14883step0; decide +kernel
      have hl : raw14883step1Labels = raw14883step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14883step0 raw14883step0Labels permutation58 permutation3
    mixedMoment B raw14883step1 raw14883step1Labels = mixedMoment B raw14883step2 raw14883step2Labels := by
      have ha : raw14883step2 = raw14883step1 := by apply Matrix.ext; unfold raw14883step2 raw14883step1; decide +kernel
      have hl : raw14883step1Labels = labelEmbedding6 ∘ raw14883step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14883step1 raw14883step1Labels raw14883step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw14884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14884step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14884step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14884step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14884 raw14884Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw14884 raw14884Labels = mixedMoment B raw14884step0 raw14884step0Labels := by
      have ha : raw14884step0 = (fun i j => raw14884 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14884step0 raw14884; decide +kernel
      have hl : raw14884step0Labels = raw14884Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14884 raw14884Labels permutation662 permutation3
    mixedMoment B raw14884step0 raw14884step0Labels = mixedMoment B raw14884step1 raw14884step1Labels := by
      have ha : raw14884step1 = -raw14884step0 := by apply Matrix.ext; change ∀ i j, raw14884step1 i j = -(raw14884step0 i j); unfold raw14884step1 raw14884step0; decide +kernel
      have hl : raw14884step1Labels = raw14884step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14884step1 raw14884step1Labels = mixedMoment B raw14884step2 raw14884step2Labels := by
      have ha : raw14884step2 = raw14884step1 := by apply Matrix.ext; unfold raw14884step2 raw14884step1; decide +kernel
      have hl : raw14884step1Labels = labelEmbedding6 ∘ raw14884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14884step1 raw14884step1Labels raw14884step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw14885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14885 raw14885Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw14885 raw14885Labels = mixedMoment B raw14885step0 raw14885step0Labels := by
      have hz : ∀ j, raw14885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14885step0 = (fun i j => raw14885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14885step0 raw14885; decide +kernel
      have hl : raw14885step0Labels = raw14885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14885 raw14885Labels permutation346 hz
    mixedMoment B raw14885step0 raw14885step0Labels = mixedMoment B raw14885step1 raw14885step1Labels := by
      have ha : raw14885step1 = (fun i j => raw14885step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14885step1 raw14885step0; decide +kernel
      have hl : raw14885step1Labels = raw14885step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14885step0 raw14885step0Labels permutation33 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw14886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14886step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14886step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw14886step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14886 raw14886Labels = mixedMoment B node5389 node5389Labels := by
  calc
    mixedMoment B raw14886 raw14886Labels = mixedMoment B raw14886step0 raw14886step0Labels := by
      have hz : ∀ j, raw14886 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14886step0 = (fun i j => raw14886 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14886step0 raw14886; decide +kernel
      have hl : raw14886step0Labels = raw14886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14886 raw14886Labels permutation434 hz
    mixedMoment B raw14886step0 raw14886step0Labels = mixedMoment B raw14886step1 raw14886step1Labels := by
      have hz : ∀ j, raw14886step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14886step1 = (fun i j => raw14886step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14886step1 raw14886step0; decide +kernel
      have hl : raw14886step1Labels = raw14886step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14886step0 raw14886step0Labels permutation80 hz
    mixedMoment B raw14886step1 raw14886step1Labels = mixedMoment B raw14886step2 raw14886step2Labels := by
      have ha : raw14886step2 = (fun i j => raw14886step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14886step2 raw14886step1; decide +kernel
      have hl : raw14886step2Labels = raw14886step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14886step1 raw14886step1Labels permutation9 permutation2
    _ = mixedMoment B node5389 node5389Labels := by rfl

def raw14887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw14887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14887 raw14887Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw14887 raw14887Labels = mixedMoment B raw14887step0 raw14887step0Labels := by
      have hz : ∀ j, raw14887 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14887step0 = (fun i j => raw14887 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14887step0 raw14887; decide +kernel
      have hl : raw14887step0Labels = raw14887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14887 raw14887Labels permutation434 hz
    mixedMoment B raw14887step0 raw14887step0Labels = mixedMoment B raw14887step1 raw14887step1Labels := by
      have ha : raw14887step1 = (fun i j => raw14887step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14887step1 raw14887step0; decide +kernel
      have hl : raw14887step1Labels = raw14887step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14887step0 raw14887step0Labels permutation125 permutation2
    mixedMoment B raw14887step1 raw14887step1Labels = mixedMoment B raw14887step2 raw14887step2Labels := by
      have ha : raw14887step2 = -raw14887step1 := by apply Matrix.ext; change ∀ i j, raw14887step2 i j = -(raw14887step1 i j); unfold raw14887step2 raw14887step1; decide +kernel
      have hl : raw14887step2Labels = raw14887step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw14888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw14888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14888 raw14888Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw14888 raw14888Labels = mixedMoment B raw14888step0 raw14888step0Labels := by
      have hz : ∀ j, raw14888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14888step0 = (fun i j => raw14888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14888step0 raw14888; decide +kernel
      have hl : raw14888step0Labels = raw14888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14888 raw14888Labels permutation346 hz
    mixedMoment B raw14888step0 raw14888step0Labels = mixedMoment B raw14888step1 raw14888step1Labels := by
      have ha : raw14888step1 = (fun i j => raw14888step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14888step1 raw14888step0; decide +kernel
      have hl : raw14888step1Labels = raw14888step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14888step0 raw14888step0Labels permutation125 permutation2
    mixedMoment B raw14888step1 raw14888step1Labels = mixedMoment B raw14888step2 raw14888step2Labels := by
      have ha : raw14888step2 = -raw14888step1 := by apply Matrix.ext; change ∀ i j, raw14888step2 i j = -(raw14888step1 i j); unfold raw14888step2 raw14888step1; decide +kernel
      have hl : raw14888step2Labels = raw14888step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw14889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14889 raw14889Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw14889 raw14889Labels = mixedMoment B raw14889step0 raw14889step0Labels := by
      have hz : ∀ j, raw14889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14889step0 = (fun i j => raw14889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14889step0 raw14889; decide +kernel
      have hl : raw14889step0Labels = raw14889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14889 raw14889Labels permutation434 hz
    mixedMoment B raw14889step0 raw14889step0Labels = mixedMoment B raw14889step1 raw14889step1Labels := by
      have hz : ∀ j, raw14889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14889step1 = (fun i j => raw14889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14889step1 raw14889step0; decide +kernel
      have hl : raw14889step1Labels = raw14889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14889step0 raw14889step0Labels permutation80 hz
    mixedMoment B raw14889step1 raw14889step1Labels = mixedMoment B raw14889step2 raw14889step2Labels := by
      have ha : raw14889step2 = (fun i j => raw14889step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14889step2 raw14889step1; decide +kernel
      have hl : raw14889step2Labels = raw14889step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14889step1 raw14889step1Labels permutation9 permutation2
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw14890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw14890step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14890step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14890step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14890step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14890step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14890 raw14890Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw14890 raw14890Labels = mixedMoment B raw14890step0 raw14890step0Labels := by
      have hz : ∀ j, raw14890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14890step0 = (fun i j => raw14890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14890step0 raw14890; decide +kernel
      have hl : raw14890step0Labels = raw14890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14890 raw14890Labels permutation434 hz
    mixedMoment B raw14890step0 raw14890step0Labels = mixedMoment B raw14890step1 raw14890step1Labels := by
      have hz : ∀ j, raw14890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14890step1 = (fun i j => raw14890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14890step1 raw14890step0; decide +kernel
      have hl : raw14890step1Labels = raw14890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14890step0 raw14890step0Labels permutation80 hz
    mixedMoment B raw14890step1 raw14890step1Labels = mixedMoment B raw14890step2 raw14890step2Labels := by
      have ha : raw14890step2 = (fun i j => raw14890step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14890step2 raw14890step1; decide +kernel
      have hl : raw14890step2Labels = raw14890step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14890step1 raw14890step1Labels permutation30 permutation3
    mixedMoment B raw14890step2 raw14890step2Labels = mixedMoment B raw14890step3 raw14890step3Labels := by
      have ha : raw14890step3 = -raw14890step2 := by apply Matrix.ext; change ∀ i j, raw14890step3 i j = -(raw14890step2 i j); unfold raw14890step3 raw14890step2; decide +kernel
      have hl : raw14890step3Labels = raw14890step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14890step3 raw14890step3Labels = mixedMoment B raw14890step4 raw14890step4Labels := by
      have ha : raw14890step4 = raw14890step3 := by apply Matrix.ext; unfold raw14890step4 raw14890step3; decide +kernel
      have hl : raw14890step3Labels = labelEmbedding6 ∘ raw14890step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14890step3 raw14890step3Labels raw14890step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw14891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14891step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14891step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14891step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14891 raw14891Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw14891 raw14891Labels = mixedMoment B raw14891step0 raw14891step0Labels := by
      have hz : ∀ j, raw14891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14891step0 = (fun i j => raw14891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14891step0 raw14891; decide +kernel
      have hl : raw14891step0Labels = raw14891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14891 raw14891Labels permutation434 hz
    mixedMoment B raw14891step0 raw14891step0Labels = mixedMoment B raw14891step1 raw14891step1Labels := by
      have ha : raw14891step1 = (fun i j => raw14891step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14891step1 raw14891step0; decide +kernel
      have hl : raw14891step1Labels = raw14891step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14891step0 raw14891step0Labels permutation149 permutation3
    mixedMoment B raw14891step1 raw14891step1Labels = mixedMoment B raw14891step2 raw14891step2Labels := by
      have ha : raw14891step2 = -raw14891step1 := by apply Matrix.ext; change ∀ i j, raw14891step2 i j = -(raw14891step1 i j); unfold raw14891step2 raw14891step1; decide +kernel
      have hl : raw14891step2Labels = raw14891step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14891step2 raw14891step2Labels = mixedMoment B raw14891step3 raw14891step3Labels := by
      have ha : raw14891step3 = raw14891step2 := by apply Matrix.ext; unfold raw14891step3 raw14891step2; decide +kernel
      have hl : raw14891step2Labels = labelEmbedding6 ∘ raw14891step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14891step2 raw14891step2Labels raw14891step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw14892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14892step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14892step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14892step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14892step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14892 raw14892Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw14892 raw14892Labels = mixedMoment B raw14892step0 raw14892step0Labels := by
      have hz : ∀ j, raw14892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14892step0 = (fun i j => raw14892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14892step0 raw14892; decide +kernel
      have hl : raw14892step0Labels = raw14892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14892 raw14892Labels permutation346 hz
    mixedMoment B raw14892step0 raw14892step0Labels = mixedMoment B raw14892step1 raw14892step1Labels := by
      have ha : raw14892step1 = (fun i j => raw14892step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14892step1 raw14892step0; decide +kernel
      have hl : raw14892step1Labels = raw14892step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14892step0 raw14892step0Labels permutation149 permutation3
    mixedMoment B raw14892step1 raw14892step1Labels = mixedMoment B raw14892step2 raw14892step2Labels := by
      have ha : raw14892step2 = -raw14892step1 := by apply Matrix.ext; change ∀ i j, raw14892step2 i j = -(raw14892step1 i j); unfold raw14892step2 raw14892step1; decide +kernel
      have hl : raw14892step2Labels = raw14892step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14892step2 raw14892step2Labels = mixedMoment B raw14892step3 raw14892step3Labels := by
      have ha : raw14892step3 = raw14892step2 := by apply Matrix.ext; unfold raw14892step3 raw14892step2; decide +kernel
      have hl : raw14892step2Labels = labelEmbedding6 ∘ raw14892step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14892step2 raw14892step2Labels raw14892step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw14893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14893Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14893step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14893step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14893step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14893step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14893 raw14893Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw14893 raw14893Labels = mixedMoment B raw14893step0 raw14893step0Labels := by
      have hz : ∀ j, raw14893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14893step0 = (fun i j => raw14893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14893step0 raw14893; decide +kernel
      have hl : raw14893step0Labels = raw14893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14893 raw14893Labels permutation434 hz
    mixedMoment B raw14893step0 raw14893step0Labels = mixedMoment B raw14893step1 raw14893step1Labels := by
      have hz : ∀ j, raw14893step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14893step1 = (fun i j => raw14893step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14893step1 raw14893step0; decide +kernel
      have hl : raw14893step1Labels = raw14893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14893step0 raw14893step0Labels permutation80 hz
    mixedMoment B raw14893step1 raw14893step1Labels = mixedMoment B raw14893step2 raw14893step2Labels := by
      have ha : raw14893step2 = (fun i j => raw14893step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14893step2 raw14893step1; decide +kernel
      have hl : raw14893step2Labels = raw14893step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14893step1 raw14893step1Labels permutation14 permutation3
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw14894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14894Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14894step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14894 raw14894Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw14894 raw14894Labels = mixedMoment B raw14894step0 raw14894step0Labels := by
      have hz : ∀ j, raw14894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14894step0 = (fun i j => raw14894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14894step0 raw14894; decide +kernel
      have hl : raw14894step0Labels = raw14894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14894 raw14894Labels permutation434 hz
    mixedMoment B raw14894step0 raw14894step0Labels = mixedMoment B raw14894step1 raw14894step1Labels := by
      have ha : raw14894step1 = (fun i j => raw14894step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14894step1 raw14894step0; decide +kernel
      have hl : raw14894step1Labels = raw14894step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14894step0 raw14894step0Labels permutation146 permutation3
    mixedMoment B raw14894step1 raw14894step1Labels = mixedMoment B raw14894step2 raw14894step2Labels := by
      have ha : raw14894step2 = -raw14894step1 := by apply Matrix.ext; change ∀ i j, raw14894step2 i j = -(raw14894step1 i j); unfold raw14894step2 raw14894step1; decide +kernel
      have hl : raw14894step2Labels = raw14894step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw14895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14895step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw14895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14895 raw14895Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw14895 raw14895Labels = mixedMoment B raw14895step0 raw14895step0Labels := by
      have hz : ∀ j, raw14895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14895step0 = (fun i j => raw14895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14895step0 raw14895; decide +kernel
      have hl : raw14895step0Labels = raw14895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14895 raw14895Labels permutation346 hz
    mixedMoment B raw14895step0 raw14895step0Labels = mixedMoment B raw14895step1 raw14895step1Labels := by
      have ha : raw14895step1 = (fun i j => raw14895step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14895step1 raw14895step0; decide +kernel
      have hl : raw14895step1Labels = raw14895step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14895step0 raw14895step0Labels permutation146 permutation3
    mixedMoment B raw14895step1 raw14895step1Labels = mixedMoment B raw14895step2 raw14895step2Labels := by
      have ha : raw14895step2 = -raw14895step1 := by apply Matrix.ext; change ∀ i j, raw14895step2 i j = -(raw14895step1 i j); unfold raw14895step2 raw14895step1; decide +kernel
      have hl : raw14895step2Labels = raw14895step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw14896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14896step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14896step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw14896step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14896 raw14896Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw14896 raw14896Labels = mixedMoment B raw14896step0 raw14896step0Labels := by
      have hz : ∀ j, raw14896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14896step0 = (fun i j => raw14896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14896step0 raw14896; decide +kernel
      have hl : raw14896step0Labels = raw14896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14896 raw14896Labels permutation434 hz
    mixedMoment B raw14896step0 raw14896step0Labels = mixedMoment B raw14896step1 raw14896step1Labels := by
      have hz : ∀ j, raw14896step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14896step1 = (fun i j => raw14896step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14896step1 raw14896step0; decide +kernel
      have hl : raw14896step1Labels = raw14896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14896step0 raw14896step0Labels permutation80 hz
    mixedMoment B raw14896step1 raw14896step1Labels = mixedMoment B raw14896step2 raw14896step2Labels := by
      have ha : raw14896step2 = (fun i j => raw14896step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14896step2 raw14896step1; decide +kernel
      have hl : raw14896step2Labels = raw14896step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14896step1 raw14896step1Labels permutation23 permutation6
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw14897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14897step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14897step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw14897step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14897 raw14897Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw14897 raw14897Labels = mixedMoment B raw14897step0 raw14897step0Labels := by
      have hz : ∀ j, raw14897 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14897step0 = (fun i j => raw14897 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14897step0 raw14897; decide +kernel
      have hl : raw14897step0Labels = raw14897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14897 raw14897Labels permutation434 hz
    mixedMoment B raw14897step0 raw14897step0Labels = mixedMoment B raw14897step1 raw14897step1Labels := by
      have hz : ∀ j, raw14897step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14897step1 = (fun i j => raw14897step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14897step1 raw14897step0; decide +kernel
      have hl : raw14897step1Labels = raw14897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14897step0 raw14897step0Labels permutation80 hz
    mixedMoment B raw14897step1 raw14897step1Labels = mixedMoment B raw14897step2 raw14897step2Labels := by
      have ha : raw14897step2 = (fun i j => raw14897step1 (permutation23 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14897step2 raw14897step1; decide +kernel
      have hl : raw14897step2Labels = raw14897step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14897step1 raw14897step1Labels permutation23 permutation6
    _ = mixedMoment B node4014 node4014Labels := by rfl

def raw14898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14898step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14898 raw14898Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw14898 raw14898Labels = mixedMoment B raw14898step0 raw14898step0Labels := by
      have hz : ∀ j, raw14898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14898step0 = (fun i j => raw14898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14898step0 raw14898; decide +kernel
      have hl : raw14898step0Labels = raw14898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14898 raw14898Labels permutation434 hz
    mixedMoment B raw14898step0 raw14898step0Labels = mixedMoment B raw14898step1 raw14898step1Labels := by
      have ha : raw14898step1 = (fun i j => raw14898step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14898step1 raw14898step0; decide +kernel
      have hl : raw14898step1Labels = raw14898step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14898step0 raw14898step0Labels permutation58 permutation3
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw14899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14899 raw14899Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw14899 raw14899Labels = mixedMoment B raw14899step0 raw14899step0Labels := by
      have ha : raw14899step0 = (fun i j => raw14899 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14899step0 raw14899; decide +kernel
      have hl : raw14899step0Labels = raw14899Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14899 raw14899Labels permutation644 permutation3
    mixedMoment B raw14899step0 raw14899step0Labels = mixedMoment B raw14899step1 raw14899step1Labels := by
      have ha : raw14899step1 = -raw14899step0 := by apply Matrix.ext; change ∀ i j, raw14899step1 i j = -(raw14899step0 i j); unfold raw14899step1 raw14899step0; decide +kernel
      have hl : raw14899step1Labels = raw14899step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3789 node3789Labels := by rfl

def raw14900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14900step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14900step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14900 raw14900Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw14900 raw14900Labels = mixedMoment B raw14900step0 raw14900step0Labels := by
      have hz : ∀ j, raw14900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14900step0 = (fun i j => raw14900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14900step0 raw14900; decide +kernel
      have hl : raw14900step0Labels = raw14900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14900 raw14900Labels permutation434 hz
    mixedMoment B raw14900step0 raw14900step0Labels = mixedMoment B raw14900step1 raw14900step1Labels := by
      have ha : raw14900step1 = (fun i j => raw14900step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14900step1 raw14900step0; decide +kernel
      have hl : raw14900step1Labels = raw14900step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14900step0 raw14900step0Labels permutation145 permutation3
    mixedMoment B raw14900step1 raw14900step1Labels = mixedMoment B raw14900step2 raw14900step2Labels := by
      have ha : raw14900step2 = -raw14900step1 := by apply Matrix.ext; change ∀ i j, raw14900step2 i j = -(raw14900step1 i j); unfold raw14900step2 raw14900step1; decide +kernel
      have hl : raw14900step2Labels = raw14900step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw14901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14901step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14901step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14901 raw14901Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw14901 raw14901Labels = mixedMoment B raw14901step0 raw14901step0Labels := by
      have hz : ∀ j, raw14901 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14901step0 = (fun i j => raw14901 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14901step0 raw14901; decide +kernel
      have hl : raw14901step0Labels = raw14901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14901 raw14901Labels permutation434 hz
    mixedMoment B raw14901step0 raw14901step0Labels = mixedMoment B raw14901step1 raw14901step1Labels := by
      have ha : raw14901step1 = (fun i j => raw14901step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14901step1 raw14901step0; decide +kernel
      have hl : raw14901step1Labels = raw14901step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14901step0 raw14901step0Labels permutation113 permutation6
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw14902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14902step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14902 raw14902Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw14902 raw14902Labels = mixedMoment B raw14902step0 raw14902step0Labels := by
      have hz : ∀ j, raw14902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14902step0 = (fun i j => raw14902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14902step0 raw14902; decide +kernel
      have hl : raw14902step0Labels = raw14902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14902 raw14902Labels permutation346 hz
    mixedMoment B raw14902step0 raw14902step0Labels = mixedMoment B raw14902step1 raw14902step1Labels := by
      have ha : raw14902step1 = (fun i j => raw14902step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14902step1 raw14902step0; decide +kernel
      have hl : raw14902step1Labels = raw14902step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14902step0 raw14902step0Labels permutation58 permutation3
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw14903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14903 raw14903Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw14903 raw14903Labels = mixedMoment B raw14903step0 raw14903step0Labels := by
      have ha : raw14903step0 = (fun i j => raw14903 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14903step0 raw14903; decide +kernel
      have hl : raw14903step0Labels = raw14903Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14903 raw14903Labels permutation662 permutation3
    mixedMoment B raw14903step0 raw14903step0Labels = mixedMoment B raw14903step1 raw14903step1Labels := by
      have ha : raw14903step1 = -raw14903step0 := by apply Matrix.ext; change ∀ i j, raw14903step1 i j = -(raw14903step0 i j); unfold raw14903step1 raw14903step0; decide +kernel
      have hl : raw14903step1Labels = raw14903step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3789 node3789Labels := by rfl

def raw14904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw14904step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14904 raw14904Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw14904 raw14904Labels = mixedMoment B raw14904step0 raw14904step0Labels := by
      have hz : ∀ j, raw14904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14904step0 = (fun i j => raw14904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14904step0 raw14904; decide +kernel
      have hl : raw14904step0Labels = raw14904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14904 raw14904Labels permutation346 hz
    mixedMoment B raw14904step0 raw14904step0Labels = mixedMoment B raw14904step1 raw14904step1Labels := by
      have ha : raw14904step1 = (fun i j => raw14904step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14904step1 raw14904step0; decide +kernel
      have hl : raw14904step1Labels = raw14904step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14904step0 raw14904step0Labels permutation145 permutation3
    mixedMoment B raw14904step1 raw14904step1Labels = mixedMoment B raw14904step2 raw14904step2Labels := by
      have ha : raw14904step2 = -raw14904step1 := by apply Matrix.ext; change ∀ i j, raw14904step2 i j = -(raw14904step1 i j); unfold raw14904step2 raw14904step1; decide +kernel
      have hl : raw14904step2Labels = raw14904step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw14905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw14905step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14905 raw14905Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw14905 raw14905Labels = mixedMoment B raw14905step0 raw14905step0Labels := by
      have hz : ∀ j, raw14905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14905step0 = (fun i j => raw14905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14905step0 raw14905; decide +kernel
      have hl : raw14905step0Labels = raw14905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14905 raw14905Labels permutation346 hz
    mixedMoment B raw14905step0 raw14905step0Labels = mixedMoment B raw14905step1 raw14905step1Labels := by
      have ha : raw14905step1 = (fun i j => raw14905step0 (permutation113 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14905step1 raw14905step0; decide +kernel
      have hl : raw14905step1Labels = raw14905step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14905step0 raw14905step0Labels permutation113 permutation6
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw14906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14906step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14906step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw14906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14906 raw14906Labels = mixedMoment B node3740 node3740Labels := by
  calc
    mixedMoment B raw14906 raw14906Labels = mixedMoment B raw14906step0 raw14906step0Labels := by
      have hz : ∀ j, raw14906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14906step0 = (fun i j => raw14906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14906step0 raw14906; decide +kernel
      have hl : raw14906step0Labels = raw14906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14906 raw14906Labels permutation434 hz
    mixedMoment B raw14906step0 raw14906step0Labels = mixedMoment B raw14906step1 raw14906step1Labels := by
      have hz : ∀ j, raw14906step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14906step1 = (fun i j => raw14906step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14906step1 raw14906step0; decide +kernel
      have hl : raw14906step1Labels = raw14906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14906step0 raw14906step0Labels permutation80 hz
    mixedMoment B raw14906step1 raw14906step1Labels = mixedMoment B raw14906step2 raw14906step2Labels := by
      have ha : raw14906step2 = (fun i j => raw14906step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14906step2 raw14906step1; decide +kernel
      have hl : raw14906step2Labels = raw14906step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14906step1 raw14906step1Labels permutation14 permutation3
    _ = mixedMoment B node3740 node3740Labels := by rfl

def raw14907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14907 raw14907Labels = mixedMoment B node3739 node3739Labels := by
  calc
    mixedMoment B raw14907 raw14907Labels = mixedMoment B raw14907step0 raw14907step0Labels := by
      have hz : ∀ j, raw14907 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14907step0 = (fun i j => raw14907 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14907step0 raw14907; decide +kernel
      have hl : raw14907step0Labels = raw14907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14907 raw14907Labels permutation434 hz
    mixedMoment B raw14907step0 raw14907step0Labels = mixedMoment B raw14907step1 raw14907step1Labels := by
      have ha : raw14907step1 = (fun i j => raw14907step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14907step1 raw14907step0; decide +kernel
      have hl : raw14907step1Labels = raw14907step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14907step0 raw14907step0Labels permutation149 permutation3
    mixedMoment B raw14907step1 raw14907step1Labels = mixedMoment B raw14907step2 raw14907step2Labels := by
      have ha : raw14907step2 = -raw14907step1 := by apply Matrix.ext; change ∀ i j, raw14907step2 i j = -(raw14907step1 i j); unfold raw14907step2 raw14907step1; decide +kernel
      have hl : raw14907step2Labels = raw14907step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3739 node3739Labels := by rfl

def raw14908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw14908step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14908step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14908 raw14908Labels = mixedMoment B node3739 node3739Labels := by
  calc
    mixedMoment B raw14908 raw14908Labels = mixedMoment B raw14908step0 raw14908step0Labels := by
      have hz : ∀ j, raw14908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14908step0 = (fun i j => raw14908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14908step0 raw14908; decide +kernel
      have hl : raw14908step0Labels = raw14908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14908 raw14908Labels permutation346 hz
    mixedMoment B raw14908step0 raw14908step0Labels = mixedMoment B raw14908step1 raw14908step1Labels := by
      have ha : raw14908step1 = (fun i j => raw14908step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14908step1 raw14908step0; decide +kernel
      have hl : raw14908step1Labels = raw14908step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14908step0 raw14908step0Labels permutation149 permutation3
    mixedMoment B raw14908step1 raw14908step1Labels = mixedMoment B raw14908step2 raw14908step2Labels := by
      have ha : raw14908step2 = -raw14908step1 := by apply Matrix.ext; change ∀ i j, raw14908step2 i j = -(raw14908step1 i j); unfold raw14908step2 raw14908step1; decide +kernel
      have hl : raw14908step2Labels = raw14908step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3739 node3739Labels := by rfl

def raw14909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14909step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw14909step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14909step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14909step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14909 raw14909Labels = mixedMoment B node4037 node4037Labels := by
  calc
    mixedMoment B raw14909 raw14909Labels = mixedMoment B raw14909step0 raw14909step0Labels := by
      have hz : ∀ j, raw14909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14909step0 = (fun i j => raw14909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14909step0 raw14909; decide +kernel
      have hl : raw14909step0Labels = raw14909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14909 raw14909Labels permutation434 hz
    mixedMoment B raw14909step0 raw14909step0Labels = mixedMoment B raw14909step1 raw14909step1Labels := by
      have hz : ∀ j, raw14909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14909step1 = (fun i j => raw14909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14909step1 raw14909step0; decide +kernel
      have hl : raw14909step1Labels = raw14909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14909step0 raw14909step0Labels permutation80 hz
    mixedMoment B raw14909step1 raw14909step1Labels = mixedMoment B raw14909step2 raw14909step2Labels := by
      have ha : raw14909step2 = (fun i j => raw14909step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14909step2 raw14909step1; decide +kernel
      have hl : raw14909step2Labels = raw14909step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14909step1 raw14909step1Labels permutation9 permutation3
    _ = mixedMoment B node4037 node4037Labels := by rfl

def raw14910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14910step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14910step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14910step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14910step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw14910step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14910step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw14910step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14910 raw14910Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw14910 raw14910Labels = mixedMoment B raw14910step0 raw14910step0Labels := by
      have hz : ∀ j, raw14910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14910step0 = (fun i j => raw14910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14910step0 raw14910; decide +kernel
      have hl : raw14910step0Labels = raw14910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14910 raw14910Labels permutation434 hz
    mixedMoment B raw14910step0 raw14910step0Labels = mixedMoment B raw14910step1 raw14910step1Labels := by
      have hz : ∀ j, raw14910step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14910step1 = (fun i j => raw14910step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14910step1 raw14910step0; decide +kernel
      have hl : raw14910step1Labels = raw14910step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14910step0 raw14910step0Labels permutation80 hz
    mixedMoment B raw14910step1 raw14910step1Labels = mixedMoment B raw14910step2 raw14910step2Labels := by
      have ha : raw14910step2 = (fun i j => raw14910step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14910step2 raw14910step1; decide +kernel
      have hl : raw14910step2Labels = raw14910step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14910step1 raw14910step1Labels permutation30 permutation3
    mixedMoment B raw14910step2 raw14910step2Labels = mixedMoment B raw14910step3 raw14910step3Labels := by
      have ha : raw14910step3 = -raw14910step2 := by apply Matrix.ext; change ∀ i j, raw14910step3 i j = -(raw14910step2 i j); unfold raw14910step3 raw14910step2; decide +kernel
      have hl : raw14910step3Labels = raw14910step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw14911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14911step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14911step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14911 raw14911Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw14911 raw14911Labels = mixedMoment B raw14911step0 raw14911step0Labels := by
      have hz : ∀ j, raw14911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14911step0 = (fun i j => raw14911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14911step0 raw14911; decide +kernel
      have hl : raw14911step0Labels = raw14911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14911 raw14911Labels permutation434 hz
    mixedMoment B raw14911step0 raw14911step0Labels = mixedMoment B raw14911step1 raw14911step1Labels := by
      have ha : raw14911step1 = (fun i j => raw14911step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14911step1 raw14911step0; decide +kernel
      have hl : raw14911step1Labels = raw14911step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14911step0 raw14911step0Labels permutation149 permutation3
    mixedMoment B raw14911step1 raw14911step1Labels = mixedMoment B raw14911step2 raw14911step2Labels := by
      have ha : raw14911step2 = -raw14911step1 := by apply Matrix.ext; change ∀ i j, raw14911step2 i j = -(raw14911step1 i j); unfold raw14911step2 raw14911step1; decide +kernel
      have hl : raw14911step2Labels = raw14911step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw14912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw14912step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14912step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14912 raw14912Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw14912 raw14912Labels = mixedMoment B raw14912step0 raw14912step0Labels := by
      have hz : ∀ j, raw14912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14912step0 = (fun i j => raw14912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14912step0 raw14912; decide +kernel
      have hl : raw14912step0Labels = raw14912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14912 raw14912Labels permutation346 hz
    mixedMoment B raw14912step0 raw14912step0Labels = mixedMoment B raw14912step1 raw14912step1Labels := by
      have ha : raw14912step1 = (fun i j => raw14912step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14912step1 raw14912step0; decide +kernel
      have hl : raw14912step1Labels = raw14912step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14912step0 raw14912step0Labels permutation149 permutation3
    mixedMoment B raw14912step1 raw14912step1Labels = mixedMoment B raw14912step2 raw14912step2Labels := by
      have ha : raw14912step2 = -raw14912step1 := by apply Matrix.ext; change ∀ i j, raw14912step2 i j = -(raw14912step1 i j); unfold raw14912step2 raw14912step1; decide +kernel
      have hl : raw14912step2Labels = raw14912step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw14913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14913step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14913step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14913step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14913 raw14913Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw14913 raw14913Labels = mixedMoment B raw14913step0 raw14913step0Labels := by
      have hz : ∀ j, raw14913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14913step0 = (fun i j => raw14913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14913step0 raw14913; decide +kernel
      have hl : raw14913step0Labels = raw14913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14913 raw14913Labels permutation434 hz
    mixedMoment B raw14913step0 raw14913step0Labels = mixedMoment B raw14913step1 raw14913step1Labels := by
      have hz : ∀ j, raw14913step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14913step1 = (fun i j => raw14913step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14913step1 raw14913step0; decide +kernel
      have hl : raw14913step1Labels = raw14913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14913step0 raw14913step0Labels permutation80 hz
    mixedMoment B raw14913step1 raw14913step1Labels = mixedMoment B raw14913step2 raw14913step2Labels := by
      have ha : raw14913step2 = (fun i j => raw14913step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14913step2 raw14913step1; decide +kernel
      have hl : raw14913step2Labels = raw14913step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14913step1 raw14913step1Labels permutation30 permutation2
    mixedMoment B raw14913step2 raw14913step2Labels = mixedMoment B raw14913step3 raw14913step3Labels := by
      have ha : raw14913step3 = -raw14913step2 := by apply Matrix.ext; change ∀ i j, raw14913step3 i j = -(raw14913step2 i j); unfold raw14913step3 raw14913step2; decide +kernel
      have hl : raw14913step3Labels = raw14913step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw14914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14914 raw14914Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw14914 raw14914Labels = mixedMoment B raw14914step0 raw14914step0Labels := by
      have hz : ∀ j, raw14914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14914step0 = (fun i j => raw14914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14914step0 raw14914; decide +kernel
      have hl : raw14914step0Labels = raw14914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14914 raw14914Labels permutation434 hz
    mixedMoment B raw14914step0 raw14914step0Labels = mixedMoment B raw14914step1 raw14914step1Labels := by
      have ha : raw14914step1 = (fun i j => raw14914step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14914step1 raw14914step0; decide +kernel
      have hl : raw14914step1Labels = raw14914step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14914step0 raw14914step0Labels permutation147 permutation2
    mixedMoment B raw14914step1 raw14914step1Labels = mixedMoment B raw14914step2 raw14914step2Labels := by
      have ha : raw14914step2 = -raw14914step1 := by apply Matrix.ext; change ∀ i j, raw14914step2 i j = -(raw14914step1 i j); unfold raw14914step2 raw14914step1; decide +kernel
      have hl : raw14914step2Labels = raw14914step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw14915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14915 raw14915Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw14915 raw14915Labels = mixedMoment B raw14915step0 raw14915step0Labels := by
      have hz : ∀ j, raw14915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14915step0 = (fun i j => raw14915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14915step0 raw14915; decide +kernel
      have hl : raw14915step0Labels = raw14915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14915 raw14915Labels permutation346 hz
    mixedMoment B raw14915step0 raw14915step0Labels = mixedMoment B raw14915step1 raw14915step1Labels := by
      have ha : raw14915step1 = (fun i j => raw14915step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14915step1 raw14915step0; decide +kernel
      have hl : raw14915step1Labels = raw14915step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14915step0 raw14915step0Labels permutation147 permutation2
    mixedMoment B raw14915step1 raw14915step1Labels = mixedMoment B raw14915step2 raw14915step2Labels := by
      have ha : raw14915step2 = -raw14915step1 := by apply Matrix.ext; change ∀ i j, raw14915step2 i j = -(raw14915step1 i j); unfold raw14915step2 raw14915step1; decide +kernel
      have hl : raw14915step2Labels = raw14915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw14916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14916step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14916step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14916step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw14916step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14916 raw14916Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw14916 raw14916Labels = mixedMoment B raw14916step0 raw14916step0Labels := by
      have hz : ∀ j, raw14916 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14916step0 = (fun i j => raw14916 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14916step0 raw14916; decide +kernel
      have hl : raw14916step0Labels = raw14916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14916 raw14916Labels permutation434 hz
    mixedMoment B raw14916step0 raw14916step0Labels = mixedMoment B raw14916step1 raw14916step1Labels := by
      have hz : ∀ j, raw14916step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14916step1 = (fun i j => raw14916step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14916step1 raw14916step0; decide +kernel
      have hl : raw14916step1Labels = raw14916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14916step0 raw14916step0Labels permutation80 hz
    mixedMoment B raw14916step1 raw14916step1Labels = mixedMoment B raw14916step2 raw14916step2Labels := by
      have ha : raw14916step2 = (fun i j => raw14916step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14916step2 raw14916step1; decide +kernel
      have hl : raw14916step2Labels = raw14916step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14916step1 raw14916step1Labels permutation30 permutation2
    mixedMoment B raw14916step2 raw14916step2Labels = mixedMoment B raw14916step3 raw14916step3Labels := by
      have ha : raw14916step3 = -raw14916step2 := by apply Matrix.ext; change ∀ i j, raw14916step3 i j = -(raw14916step2 i j); unfold raw14916step3 raw14916step2; decide +kernel
      have hl : raw14916step3Labels = raw14916step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw14917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14917step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14917step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14917step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14917 raw14917Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw14917 raw14917Labels = mixedMoment B raw14917step0 raw14917step0Labels := by
      have hz : ∀ j, raw14917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14917step0 = (fun i j => raw14917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14917step0 raw14917; decide +kernel
      have hl : raw14917step0Labels = raw14917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14917 raw14917Labels permutation434 hz
    mixedMoment B raw14917step0 raw14917step0Labels = mixedMoment B raw14917step1 raw14917step1Labels := by
      have hz : ∀ j, raw14917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14917step1 = (fun i j => raw14917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14917step1 raw14917step0; decide +kernel
      have hl : raw14917step1Labels = raw14917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14917step0 raw14917step0Labels permutation80 hz
    mixedMoment B raw14917step1 raw14917step1Labels = mixedMoment B raw14917step2 raw14917step2Labels := by
      have ha : raw14917step2 = (fun i j => raw14917step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14917step2 raw14917step1; decide +kernel
      have hl : raw14917step2Labels = raw14917step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14917step1 raw14917step1Labels permutation22 permutation4
    mixedMoment B raw14917step2 raw14917step2Labels = mixedMoment B raw14917step3 raw14917step3Labels := by
      have ha : raw14917step3 = raw14917step2 := by apply Matrix.ext; unfold raw14917step3 raw14917step2; decide +kernel
      have hl : raw14917step2Labels = labelEmbedding7 ∘ raw14917step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14917step2 raw14917step2Labels raw14917step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw14918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14918step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14918step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14918step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14918step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14918 raw14918Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw14918 raw14918Labels = mixedMoment B raw14918step0 raw14918step0Labels := by
      have hz : ∀ j, raw14918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14918step0 = (fun i j => raw14918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14918step0 raw14918; decide +kernel
      have hl : raw14918step0Labels = raw14918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14918 raw14918Labels permutation434 hz
    mixedMoment B raw14918step0 raw14918step0Labels = mixedMoment B raw14918step1 raw14918step1Labels := by
      have hz : ∀ j, raw14918step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14918step1 = (fun i j => raw14918step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14918step1 raw14918step0; decide +kernel
      have hl : raw14918step1Labels = raw14918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14918step0 raw14918step0Labels permutation80 hz
    mixedMoment B raw14918step1 raw14918step1Labels = mixedMoment B raw14918step2 raw14918step2Labels := by
      have ha : raw14918step2 = (fun i j => raw14918step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14918step2 raw14918step1; decide +kernel
      have hl : raw14918step2Labels = raw14918step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14918step1 raw14918step1Labels permutation8 permutation3
    mixedMoment B raw14918step2 raw14918step2Labels = mixedMoment B raw14918step3 raw14918step3Labels := by
      have ha : raw14918step3 = raw14918step2 := by apply Matrix.ext; unfold raw14918step3 raw14918step2; decide +kernel
      have hl : raw14918step2Labels = labelEmbedding6 ∘ raw14918step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14918step2 raw14918step2Labels raw14918step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw14919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14919step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14919 raw14919Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw14919 raw14919Labels = mixedMoment B raw14919step0 raw14919step0Labels := by
      have hz : ∀ j, raw14919 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14919step0 = (fun i j => raw14919 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14919step0 raw14919; decide +kernel
      have hl : raw14919step0Labels = raw14919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14919 raw14919Labels permutation434 hz
    mixedMoment B raw14919step0 raw14919step0Labels = mixedMoment B raw14919step1 raw14919step1Labels := by
      have ha : raw14919step1 = (fun i j => raw14919step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14919step1 raw14919step0; decide +kernel
      have hl : raw14919step1Labels = raw14919step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14919step0 raw14919step0Labels permutation38 permutation3
    mixedMoment B raw14919step1 raw14919step1Labels = mixedMoment B raw14919step2 raw14919step2Labels := by
      have ha : raw14919step2 = raw14919step1 := by apply Matrix.ext; unfold raw14919step2 raw14919step1; decide +kernel
      have hl : raw14919step1Labels = labelEmbedding6 ∘ raw14919step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14919step1 raw14919step1Labels raw14919step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw14920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14920step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14920step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14920 raw14920Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw14920 raw14920Labels = mixedMoment B raw14920step0 raw14920step0Labels := by
      have hz : ∀ j, raw14920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14920step0 = (fun i j => raw14920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14920step0 raw14920; decide +kernel
      have hl : raw14920step0Labels = raw14920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14920 raw14920Labels permutation346 hz
    mixedMoment B raw14920step0 raw14920step0Labels = mixedMoment B raw14920step1 raw14920step1Labels := by
      have ha : raw14920step1 = (fun i j => raw14920step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14920step1 raw14920step0; decide +kernel
      have hl : raw14920step1Labels = raw14920step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14920step0 raw14920step0Labels permutation38 permutation3
    mixedMoment B raw14920step1 raw14920step1Labels = mixedMoment B raw14920step2 raw14920step2Labels := by
      have ha : raw14920step2 = raw14920step1 := by apply Matrix.ext; unfold raw14920step2 raw14920step1; decide +kernel
      have hl : raw14920step1Labels = labelEmbedding6 ∘ raw14920step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14920step1 raw14920step1Labels raw14920step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw14921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw14921step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14921 raw14921Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw14921 raw14921Labels = mixedMoment B raw14921step0 raw14921step0Labels := by
      have hz : ∀ j, raw14921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14921step0 = (fun i j => raw14921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14921step0 raw14921; decide +kernel
      have hl : raw14921step0Labels = raw14921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14921 raw14921Labels permutation434 hz
    mixedMoment B raw14921step0 raw14921step0Labels = mixedMoment B raw14921step1 raw14921step1Labels := by
      have hz : ∀ j, raw14921step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14921step1 = (fun i j => raw14921step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14921step1 raw14921step0; decide +kernel
      have hl : raw14921step1Labels = raw14921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14921step0 raw14921step0Labels permutation80 hz
    mixedMoment B raw14921step1 raw14921step1Labels = mixedMoment B raw14921step2 raw14921step2Labels := by
      have ha : raw14921step2 = (fun i j => raw14921step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14921step2 raw14921step1; decide +kernel
      have hl : raw14921step2Labels = raw14921step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14921step1 raw14921step1Labels permutation29 permutation2
    mixedMoment B raw14921step2 raw14921step2Labels = mixedMoment B raw14921step3 raw14921step3Labels := by
      have ha : raw14921step3 = -raw14921step2 := by apply Matrix.ext; change ∀ i j, raw14921step3 i j = -(raw14921step2 i j); unfold raw14921step3 raw14921step2; decide +kernel
      have hl : raw14921step3Labels = raw14921step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw14922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14922step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14922step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14922step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14922step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14922step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14922step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14922 raw14922Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw14922 raw14922Labels = mixedMoment B raw14922step0 raw14922step0Labels := by
      have hz : ∀ j, raw14922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14922step0 = (fun i j => raw14922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14922step0 raw14922; decide +kernel
      have hl : raw14922step0Labels = raw14922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14922 raw14922Labels permutation434 hz
    mixedMoment B raw14922step0 raw14922step0Labels = mixedMoment B raw14922step1 raw14922step1Labels := by
      have hz : ∀ j, raw14922step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14922step1 = (fun i j => raw14922step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14922step1 raw14922step0; decide +kernel
      have hl : raw14922step1Labels = raw14922step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14922step0 raw14922step0Labels permutation80 hz
    mixedMoment B raw14922step1 raw14922step1Labels = mixedMoment B raw14922step2 raw14922step2Labels := by
      have ha : raw14922step2 = (fun i j => raw14922step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14922step2 raw14922step1; decide +kernel
      have hl : raw14922step2Labels = raw14922step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14922step1 raw14922step1Labels permutation12 permutation5
    mixedMoment B raw14922step2 raw14922step2Labels = mixedMoment B raw14922step3 raw14922step3Labels := by
      have ha : raw14922step3 = -raw14922step2 := by apply Matrix.ext; change ∀ i j, raw14922step3 i j = -(raw14922step2 i j); unfold raw14922step3 raw14922step2; decide +kernel
      have hl : raw14922step3Labels = raw14922step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14922step3 raw14922step3Labels = mixedMoment B raw14922step4 raw14922step4Labels := by
      have ha : raw14922step4 = raw14922step3 := by apply Matrix.ext; unfold raw14922step4 raw14922step3; decide +kernel
      have hl : raw14922step3Labels = labelEmbedding8 ∘ raw14922step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14922step3 raw14922step3Labels raw14922step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw14923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14923step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14923step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14923 raw14923Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw14923 raw14923Labels = mixedMoment B raw14923step0 raw14923step0Labels := by
      have hz : ∀ j, raw14923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14923step0 = (fun i j => raw14923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14923step0 raw14923; decide +kernel
      have hl : raw14923step0Labels = raw14923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14923 raw14923Labels permutation434 hz
    mixedMoment B raw14923step0 raw14923step0Labels = mixedMoment B raw14923step1 raw14923step1Labels := by
      have ha : raw14923step1 = (fun i j => raw14923step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14923step1 raw14923step0; decide +kernel
      have hl : raw14923step1Labels = raw14923step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14923step0 raw14923step0Labels permutation32 permutation3
    mixedMoment B raw14923step1 raw14923step1Labels = mixedMoment B raw14923step2 raw14923step2Labels := by
      have ha : raw14923step2 = raw14923step1 := by apply Matrix.ext; unfold raw14923step2 raw14923step1; decide +kernel
      have hl : raw14923step1Labels = labelEmbedding6 ∘ raw14923step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14923step1 raw14923step1Labels raw14923step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw14924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14924step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14924step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14924 raw14924Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw14924 raw14924Labels = mixedMoment B raw14924step0 raw14924step0Labels := by
      have hz : ∀ j, raw14924 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14924step0 = (fun i j => raw14924 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14924step0 raw14924; decide +kernel
      have hl : raw14924step0Labels = raw14924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14924 raw14924Labels permutation434 hz
    mixedMoment B raw14924step0 raw14924step0Labels = mixedMoment B raw14924step1 raw14924step1Labels := by
      have ha : raw14924step1 = (fun i j => raw14924step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14924step1 raw14924step0; decide +kernel
      have hl : raw14924step1Labels = raw14924step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14924step0 raw14924step0Labels permutation32 permutation3
    mixedMoment B raw14924step1 raw14924step1Labels = mixedMoment B raw14924step2 raw14924step2Labels := by
      have ha : raw14924step2 = raw14924step1 := by apply Matrix.ext; unfold raw14924step2 raw14924step1; decide +kernel
      have hl : raw14924step1Labels = labelEmbedding6 ∘ raw14924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14924step1 raw14924step1Labels raw14924step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw14925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14925step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14925 raw14925Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw14925 raw14925Labels = mixedMoment B raw14925step0 raw14925step0Labels := by
      have ha : raw14925step0 = (fun i j => raw14925 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14925step0 raw14925; decide +kernel
      have hl : raw14925step0Labels = raw14925Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14925 raw14925Labels permutation200 permutation3
    mixedMoment B raw14925step0 raw14925step0Labels = mixedMoment B raw14925step1 raw14925step1Labels := by
      have ha : raw14925step1 = raw14925step0 := by apply Matrix.ext; unfold raw14925step1 raw14925step0; decide +kernel
      have hl : raw14925step0Labels = labelEmbedding6 ∘ raw14925step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14925step0 raw14925step0Labels raw14925step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw14926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14926step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14926step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14926 raw14926Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw14926 raw14926Labels = mixedMoment B raw14926step0 raw14926step0Labels := by
      have hz : ∀ j, raw14926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14926step0 = (fun i j => raw14926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14926step0 raw14926; decide +kernel
      have hl : raw14926step0Labels = raw14926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14926 raw14926Labels permutation434 hz
    mixedMoment B raw14926step0 raw14926step0Labels = mixedMoment B raw14926step1 raw14926step1Labels := by
      have ha : raw14926step1 = (fun i j => raw14926step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14926step1 raw14926step0; decide +kernel
      have hl : raw14926step1Labels = raw14926step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14926step0 raw14926step0Labels permutation145 permutation2
    mixedMoment B raw14926step1 raw14926step1Labels = mixedMoment B raw14926step2 raw14926step2Labels := by
      have ha : raw14926step2 = -raw14926step1 := by apply Matrix.ext; change ∀ i j, raw14926step2 i j = -(raw14926step1 i j); unfold raw14926step2 raw14926step1; decide +kernel
      have hl : raw14926step2Labels = raw14926step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw14927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14927step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14927step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14927 raw14927Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw14927 raw14927Labels = mixedMoment B raw14927step0 raw14927step0Labels := by
      have hz : ∀ j, raw14927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14927step0 = (fun i j => raw14927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14927step0 raw14927; decide +kernel
      have hl : raw14927step0Labels = raw14927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14927 raw14927Labels permutation434 hz
    mixedMoment B raw14927step0 raw14927step0Labels = mixedMoment B raw14927step1 raw14927step1Labels := by
      have ha : raw14927step1 = (fun i j => raw14927step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14927step1 raw14927step0; decide +kernel
      have hl : raw14927step1Labels = raw14927step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14927step0 raw14927step0Labels permutation36 permutation3
    mixedMoment B raw14927step1 raw14927step1Labels = mixedMoment B raw14927step2 raw14927step2Labels := by
      have ha : raw14927step2 = raw14927step1 := by apply Matrix.ext; unfold raw14927step2 raw14927step1; decide +kernel
      have hl : raw14927step1Labels = labelEmbedding6 ∘ raw14927step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14927step1 raw14927step1Labels raw14927step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw14928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14928step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14928step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14928 raw14928Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw14928 raw14928Labels = mixedMoment B raw14928step0 raw14928step0Labels := by
      have hz : ∀ j, raw14928 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14928step0 = (fun i j => raw14928 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14928step0 raw14928; decide +kernel
      have hl : raw14928step0Labels = raw14928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14928 raw14928Labels permutation346 hz
    mixedMoment B raw14928step0 raw14928step0Labels = mixedMoment B raw14928step1 raw14928step1Labels := by
      have ha : raw14928step1 = (fun i j => raw14928step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14928step1 raw14928step0; decide +kernel
      have hl : raw14928step1Labels = raw14928step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14928step0 raw14928step0Labels permutation32 permutation3
    mixedMoment B raw14928step1 raw14928step1Labels = mixedMoment B raw14928step2 raw14928step2Labels := by
      have ha : raw14928step2 = raw14928step1 := by apply Matrix.ext; unfold raw14928step2 raw14928step1; decide +kernel
      have hl : raw14928step1Labels = labelEmbedding6 ∘ raw14928step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14928step1 raw14928step1Labels raw14928step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw14929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14929step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14929step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14929step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14929 raw14929Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw14929 raw14929Labels = mixedMoment B raw14929step0 raw14929step0Labels := by
      have hz : ∀ j, raw14929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14929step0 = (fun i j => raw14929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14929step0 raw14929; decide +kernel
      have hl : raw14929step0Labels = raw14929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14929 raw14929Labels permutation346 hz
    mixedMoment B raw14929step0 raw14929step0Labels = mixedMoment B raw14929step1 raw14929step1Labels := by
      have ha : raw14929step1 = (fun i j => raw14929step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14929step1 raw14929step0; decide +kernel
      have hl : raw14929step1Labels = raw14929step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14929step0 raw14929step0Labels permutation32 permutation3
    mixedMoment B raw14929step1 raw14929step1Labels = mixedMoment B raw14929step2 raw14929step2Labels := by
      have ha : raw14929step2 = raw14929step1 := by apply Matrix.ext; unfold raw14929step2 raw14929step1; decide +kernel
      have hl : raw14929step1Labels = labelEmbedding6 ∘ raw14929step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14929step1 raw14929step1Labels raw14929step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw14930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14930step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14930 raw14930Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw14930 raw14930Labels = mixedMoment B raw14930step0 raw14930step0Labels := by
      have ha : raw14930step0 = (fun i j => raw14930 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14930step0 raw14930; decide +kernel
      have hl : raw14930step0Labels = raw14930Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14930 raw14930Labels permutation176 permutation3
    mixedMoment B raw14930step0 raw14930step0Labels = mixedMoment B raw14930step1 raw14930step1Labels := by
      have ha : raw14930step1 = raw14930step0 := by apply Matrix.ext; unfold raw14930step1 raw14930step0; decide +kernel
      have hl : raw14930step0Labels = labelEmbedding6 ∘ raw14930step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14930step0 raw14930step0Labels raw14930step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw14931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14931step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14931 raw14931Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw14931 raw14931Labels = mixedMoment B raw14931step0 raw14931step0Labels := by
      have hz : ∀ j, raw14931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14931step0 = (fun i j => raw14931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14931step0 raw14931; decide +kernel
      have hl : raw14931step0Labels = raw14931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14931 raw14931Labels permutation346 hz
    mixedMoment B raw14931step0 raw14931step0Labels = mixedMoment B raw14931step1 raw14931step1Labels := by
      have ha : raw14931step1 = (fun i j => raw14931step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14931step1 raw14931step0; decide +kernel
      have hl : raw14931step1Labels = raw14931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14931step0 raw14931step0Labels permutation145 permutation2
    mixedMoment B raw14931step1 raw14931step1Labels = mixedMoment B raw14931step2 raw14931step2Labels := by
      have ha : raw14931step2 = -raw14931step1 := by apply Matrix.ext; change ∀ i j, raw14931step2 i j = -(raw14931step1 i j); unfold raw14931step2 raw14931step1; decide +kernel
      have hl : raw14931step2Labels = raw14931step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw14932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14932step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14932step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14932 raw14932Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw14932 raw14932Labels = mixedMoment B raw14932step0 raw14932step0Labels := by
      have hz : ∀ j, raw14932 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14932step0 = (fun i j => raw14932 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14932step0 raw14932; decide +kernel
      have hl : raw14932step0Labels = raw14932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14932 raw14932Labels permutation346 hz
    mixedMoment B raw14932step0 raw14932step0Labels = mixedMoment B raw14932step1 raw14932step1Labels := by
      have ha : raw14932step1 = (fun i j => raw14932step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14932step1 raw14932step0; decide +kernel
      have hl : raw14932step1Labels = raw14932step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14932step0 raw14932step0Labels permutation36 permutation3
    mixedMoment B raw14932step1 raw14932step1Labels = mixedMoment B raw14932step2 raw14932step2Labels := by
      have ha : raw14932step2 = raw14932step1 := by apply Matrix.ext; unfold raw14932step2 raw14932step1; decide +kernel
      have hl : raw14932step1Labels = labelEmbedding6 ∘ raw14932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14932step1 raw14932step1Labels raw14932step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw14933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14933step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw14933step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14933step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw14933step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14933 raw14933Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw14933 raw14933Labels = mixedMoment B raw14933step0 raw14933step0Labels := by
      have hz : ∀ j, raw14933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14933step0 = (fun i j => raw14933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14933step0 raw14933; decide +kernel
      have hl : raw14933step0Labels = raw14933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14933 raw14933Labels permutation434 hz
    mixedMoment B raw14933step0 raw14933step0Labels = mixedMoment B raw14933step1 raw14933step1Labels := by
      have hz : ∀ j, raw14933step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14933step1 = (fun i j => raw14933step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14933step1 raw14933step0; decide +kernel
      have hl : raw14933step1Labels = raw14933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14933step0 raw14933step0Labels permutation80 hz
    mixedMoment B raw14933step1 raw14933step1Labels = mixedMoment B raw14933step2 raw14933step2Labels := by
      have ha : raw14933step2 = (fun i j => raw14933step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14933step2 raw14933step1; decide +kernel
      have hl : raw14933step2Labels = raw14933step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14933step1 raw14933step1Labels permutation9 permutation3
    mixedMoment B raw14933step2 raw14933step2Labels = mixedMoment B raw14933step3 raw14933step3Labels := by
      have ha : raw14933step3 = raw14933step2 := by apply Matrix.ext; unfold raw14933step3 raw14933step2; decide +kernel
      have hl : raw14933step2Labels = labelEmbedding6 ∘ raw14933step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14933step2 raw14933step2Labels raw14933step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw14934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw14934step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw14934step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14934 raw14934Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw14934 raw14934Labels = mixedMoment B raw14934step0 raw14934step0Labels := by
      have hz : ∀ j, raw14934 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14934step0 = (fun i j => raw14934 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14934step0 raw14934; decide +kernel
      have hl : raw14934step0Labels = raw14934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14934 raw14934Labels permutation434 hz
    mixedMoment B raw14934step0 raw14934step0Labels = mixedMoment B raw14934step1 raw14934step1Labels := by
      have hz : ∀ j, raw14934step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14934step1 = (fun i j => raw14934step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14934step1 raw14934step0; decide +kernel
      have hl : raw14934step1Labels = raw14934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14934step0 raw14934step0Labels permutation80 hz
    mixedMoment B raw14934step1 raw14934step1Labels = mixedMoment B raw14934step2 raw14934step2Labels := by
      have ha : raw14934step2 = (fun i j => raw14934step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14934step2 raw14934step1; decide +kernel
      have hl : raw14934step2Labels = raw14934step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14934step1 raw14934step1Labels permutation25 permutation5
    mixedMoment B raw14934step2 raw14934step2Labels = mixedMoment B raw14934step3 raw14934step3Labels := by
      have ha : raw14934step3 = raw14934step2 := by apply Matrix.ext; unfold raw14934step3 raw14934step2; decide +kernel
      have hl : raw14934step2Labels = labelEmbedding8 ∘ raw14934step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14934step2 raw14934step2Labels raw14934step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw14935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14935step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14935step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14935 raw14935Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw14935 raw14935Labels = mixedMoment B raw14935step0 raw14935step0Labels := by
      have hz : ∀ j, raw14935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14935step0 = (fun i j => raw14935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14935step0 raw14935; decide +kernel
      have hl : raw14935step0Labels = raw14935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14935 raw14935Labels permutation434 hz
    mixedMoment B raw14935step0 raw14935step0Labels = mixedMoment B raw14935step1 raw14935step1Labels := by
      have ha : raw14935step1 = (fun i j => raw14935step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14935step1 raw14935step0; decide +kernel
      have hl : raw14935step1Labels = raw14935step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14935step0 raw14935step0Labels permutation125 permutation5
    mixedMoment B raw14935step1 raw14935step1Labels = mixedMoment B raw14935step2 raw14935step2Labels := by
      have ha : raw14935step2 = raw14935step1 := by apply Matrix.ext; unfold raw14935step2 raw14935step1; decide +kernel
      have hl : raw14935step1Labels = labelEmbedding8 ∘ raw14935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14935step1 raw14935step1Labels raw14935step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw14936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14936step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14936 raw14936Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw14936 raw14936Labels = mixedMoment B raw14936step0 raw14936step0Labels := by
      have hz : ∀ j, raw14936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14936step0 = (fun i j => raw14936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14936step0 raw14936; decide +kernel
      have hl : raw14936step0Labels = raw14936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14936 raw14936Labels permutation346 hz
    mixedMoment B raw14936step0 raw14936step0Labels = mixedMoment B raw14936step1 raw14936step1Labels := by
      have ha : raw14936step1 = (fun i j => raw14936step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14936step1 raw14936step0; decide +kernel
      have hl : raw14936step1Labels = raw14936step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14936step0 raw14936step0Labels permutation125 permutation5
    mixedMoment B raw14936step1 raw14936step1Labels = mixedMoment B raw14936step2 raw14936step2Labels := by
      have ha : raw14936step2 = raw14936step1 := by apply Matrix.ext; unfold raw14936step2 raw14936step1; decide +kernel
      have hl : raw14936step1Labels = labelEmbedding8 ∘ raw14936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14936step1 raw14936step1Labels raw14936step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw14937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14937step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14937step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw14937step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14937 raw14937Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw14937 raw14937Labels = mixedMoment B raw14937step0 raw14937step0Labels := by
      have hz : ∀ j, raw14937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14937step0 = (fun i j => raw14937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14937step0 raw14937; decide +kernel
      have hl : raw14937step0Labels = raw14937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14937 raw14937Labels permutation434 hz
    mixedMoment B raw14937step0 raw14937step0Labels = mixedMoment B raw14937step1 raw14937step1Labels := by
      have hz : ∀ j, raw14937step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14937step1 = (fun i j => raw14937step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14937step1 raw14937step0; decide +kernel
      have hl : raw14937step1Labels = raw14937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14937step0 raw14937step0Labels permutation80 hz
    mixedMoment B raw14937step1 raw14937step1Labels = mixedMoment B raw14937step2 raw14937step2Labels := by
      have ha : raw14937step2 = (fun i j => raw14937step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14937step2 raw14937step1; decide +kernel
      have hl : raw14937step2Labels = raw14937step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14937step1 raw14937step1Labels permutation23 permutation5
    mixedMoment B raw14937step2 raw14937step2Labels = mixedMoment B raw14937step3 raw14937step3Labels := by
      have ha : raw14937step3 = raw14937step2 := by apply Matrix.ext; unfold raw14937step3 raw14937step2; decide +kernel
      have hl : raw14937step2Labels = labelEmbedding8 ∘ raw14937step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14937step2 raw14937step2Labels raw14937step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw14938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14938step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw14938step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14938step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw14938step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14938 raw14938Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw14938 raw14938Labels = mixedMoment B raw14938step0 raw14938step0Labels := by
      have hz : ∀ j, raw14938 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14938step0 = (fun i j => raw14938 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14938step0 raw14938; decide +kernel
      have hl : raw14938step0Labels = raw14938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14938 raw14938Labels permutation434 hz
    mixedMoment B raw14938step0 raw14938step0Labels = mixedMoment B raw14938step1 raw14938step1Labels := by
      have hz : ∀ j, raw14938step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14938step1 = (fun i j => raw14938step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14938step1 raw14938step0; decide +kernel
      have hl : raw14938step1Labels = raw14938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14938step0 raw14938step0Labels permutation80 hz
    mixedMoment B raw14938step1 raw14938step1Labels = mixedMoment B raw14938step2 raw14938step2Labels := by
      have ha : raw14938step2 = (fun i j => raw14938step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14938step2 raw14938step1; decide +kernel
      have hl : raw14938step2Labels = raw14938step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14938step1 raw14938step1Labels permutation8 permutation3
    mixedMoment B raw14938step2 raw14938step2Labels = mixedMoment B raw14938step3 raw14938step3Labels := by
      have ha : raw14938step3 = raw14938step2 := by apply Matrix.ext; unfold raw14938step3 raw14938step2; decide +kernel
      have hl : raw14938step2Labels = labelEmbedding6 ∘ raw14938step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14938step2 raw14938step2Labels raw14938step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw14939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw14939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw14939step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14939 raw14939Labels = mixedMoment B node5207 node5207Labels := by
  calc
    mixedMoment B raw14939 raw14939Labels = mixedMoment B raw14939step0 raw14939step0Labels := by
      have hz : ∀ j, raw14939 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14939step0 = (fun i j => raw14939 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14939step0 raw14939; decide +kernel
      have hl : raw14939step0Labels = raw14939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14939 raw14939Labels permutation434 hz
    mixedMoment B raw14939step0 raw14939step0Labels = mixedMoment B raw14939step1 raw14939step1Labels := by
      have hz : ∀ j, raw14939step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14939step1 = (fun i j => raw14939step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14939step1 raw14939step0; decide +kernel
      have hl : raw14939step1Labels = raw14939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14939step0 raw14939step0Labels permutation80 hz
    mixedMoment B raw14939step1 raw14939step1Labels = mixedMoment B raw14939step2 raw14939step2Labels := by
      have ha : raw14939step2 = (fun i j => raw14939step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14939step2 raw14939step1; decide +kernel
      have hl : raw14939step2Labels = raw14939step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14939step1 raw14939step1Labels permutation30 permutation2
    mixedMoment B raw14939step2 raw14939step2Labels = mixedMoment B raw14939step3 raw14939step3Labels := by
      have ha : raw14939step3 = -raw14939step2 := by apply Matrix.ext; change ∀ i j, raw14939step3 i j = -(raw14939step2 i j); unfold raw14939step3 raw14939step2; decide +kernel
      have hl : raw14939step3Labels = raw14939step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5207 node5207Labels := by rfl

def raw14940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14940step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14940step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14940 raw14940Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw14940 raw14940Labels = mixedMoment B raw14940step0 raw14940step0Labels := by
      have hz : ∀ j, raw14940 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14940step0 = (fun i j => raw14940 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14940step0 raw14940; decide +kernel
      have hl : raw14940step0Labels = raw14940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14940 raw14940Labels permutation434 hz
    mixedMoment B raw14940step0 raw14940step0Labels = mixedMoment B raw14940step1 raw14940step1Labels := by
      have ha : raw14940step1 = (fun i j => raw14940step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14940step1 raw14940step0; decide +kernel
      have hl : raw14940step1Labels = raw14940step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14940step0 raw14940step0Labels permutation151 permutation2
    mixedMoment B raw14940step1 raw14940step1Labels = mixedMoment B raw14940step2 raw14940step2Labels := by
      have ha : raw14940step2 = -raw14940step1 := by apply Matrix.ext; change ∀ i j, raw14940step2 i j = -(raw14940step1 i j); unfold raw14940step2 raw14940step1; decide +kernel
      have hl : raw14940step2Labels = raw14940step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw14941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14941step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14941 raw14941Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw14941 raw14941Labels = mixedMoment B raw14941step0 raw14941step0Labels := by
      have hz : ∀ j, raw14941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14941step0 = (fun i j => raw14941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14941step0 raw14941; decide +kernel
      have hl : raw14941step0Labels = raw14941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14941 raw14941Labels permutation346 hz
    mixedMoment B raw14941step0 raw14941step0Labels = mixedMoment B raw14941step1 raw14941step1Labels := by
      have ha : raw14941step1 = (fun i j => raw14941step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14941step1 raw14941step0; decide +kernel
      have hl : raw14941step1Labels = raw14941step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14941step0 raw14941step0Labels permutation151 permutation2
    mixedMoment B raw14941step1 raw14941step1Labels = mixedMoment B raw14941step2 raw14941step2Labels := by
      have ha : raw14941step2 = -raw14941step1 := by apply Matrix.ext; change ∀ i j, raw14941step2 i j = -(raw14941step1 i j); unfold raw14941step2 raw14941step1; decide +kernel
      have hl : raw14941step2Labels = raw14941step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw14942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw14942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw14942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2]]
def raw14942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14942step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14942step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14942step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14942 raw14942Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw14942 raw14942Labels = mixedMoment B raw14942step0 raw14942step0Labels := by
      have hz : ∀ j, raw14942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14942step0 = (fun i j => raw14942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14942step0 raw14942; decide +kernel
      have hl : raw14942step0Labels = raw14942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14942 raw14942Labels permutation434 hz
    mixedMoment B raw14942step0 raw14942step0Labels = mixedMoment B raw14942step1 raw14942step1Labels := by
      have hz : ∀ j, raw14942step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14942step1 = (fun i j => raw14942step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14942step1 raw14942step0; decide +kernel
      have hl : raw14942step1Labels = raw14942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14942step0 raw14942step0Labels permutation80 hz
    mixedMoment B raw14942step1 raw14942step1Labels = mixedMoment B raw14942step2 raw14942step2Labels := by
      have ha : raw14942step2 = (fun i j => raw14942step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14942step2 raw14942step1; decide +kernel
      have hl : raw14942step2Labels = raw14942step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14942step1 raw14942step1Labels permutation31 permutation2
    mixedMoment B raw14942step2 raw14942step2Labels = mixedMoment B raw14942step3 raw14942step3Labels := by
      have ha : raw14942step3 = -raw14942step2 := by apply Matrix.ext; change ∀ i j, raw14942step3 i j = -(raw14942step2 i j); unfold raw14942step3 raw14942step2; decide +kernel
      have hl : raw14942step3Labels = raw14942step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw14943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14943step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw14943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14943 raw14943Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw14943 raw14943Labels = mixedMoment B raw14943step0 raw14943step0Labels := by
      have hz : ∀ j, raw14943 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14943step0 = (fun i j => raw14943 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14943step0 raw14943; decide +kernel
      have hl : raw14943step0Labels = raw14943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14943 raw14943Labels permutation434 hz
    mixedMoment B raw14943step0 raw14943step0Labels = mixedMoment B raw14943step1 raw14943step1Labels := by
      have hz : ∀ j, raw14943step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14943step1 = (fun i j => raw14943step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14943step1 raw14943step0; decide +kernel
      have hl : raw14943step1Labels = raw14943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14943step0 raw14943step0Labels permutation80 hz
    mixedMoment B raw14943step1 raw14943step1Labels = mixedMoment B raw14943step2 raw14943step2Labels := by
      have ha : raw14943step2 = (fun i j => raw14943step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14943step2 raw14943step1; decide +kernel
      have hl : raw14943step2Labels = raw14943step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14943step1 raw14943step1Labels permutation14 permutation3
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw14944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14944 raw14944Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw14944 raw14944Labels = mixedMoment B raw14944step0 raw14944step0Labels := by
      have hz : ∀ j, raw14944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14944step0 = (fun i j => raw14944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14944step0 raw14944; decide +kernel
      have hl : raw14944step0Labels = raw14944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14944 raw14944Labels permutation434 hz
    mixedMoment B raw14944step0 raw14944step0Labels = mixedMoment B raw14944step1 raw14944step1Labels := by
      have ha : raw14944step1 = (fun i j => raw14944step0 (permutation148 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14944step1 raw14944step0; decide +kernel
      have hl : raw14944step1Labels = raw14944step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14944step0 raw14944step0Labels permutation148 permutation3
    mixedMoment B raw14944step1 raw14944step1Labels = mixedMoment B raw14944step2 raw14944step2Labels := by
      have ha : raw14944step2 = -raw14944step1 := by apply Matrix.ext; change ∀ i j, raw14944step2 i j = -(raw14944step1 i j); unfold raw14944step2 raw14944step1; decide +kernel
      have hl : raw14944step2Labels = raw14944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw14945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14945 raw14945Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw14945 raw14945Labels = mixedMoment B raw14945step0 raw14945step0Labels := by
      have hz : ∀ j, raw14945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14945step0 = (fun i j => raw14945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14945step0 raw14945; decide +kernel
      have hl : raw14945step0Labels = raw14945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14945 raw14945Labels permutation346 hz
    mixedMoment B raw14945step0 raw14945step0Labels = mixedMoment B raw14945step1 raw14945step1Labels := by
      have ha : raw14945step1 = (fun i j => raw14945step0 (permutation148 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14945step1 raw14945step0; decide +kernel
      have hl : raw14945step1Labels = raw14945step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14945step0 raw14945step0Labels permutation148 permutation3
    mixedMoment B raw14945step1 raw14945step1Labels = mixedMoment B raw14945step2 raw14945step2Labels := by
      have ha : raw14945step2 = -raw14945step1 := by apply Matrix.ext; change ∀ i j, raw14945step2 i j = -(raw14945step1 i j); unfold raw14945step2 raw14945step1; decide +kernel
      have hl : raw14945step2Labels = raw14945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw14946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14946step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14946step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14946step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14946 raw14946Labels = mixedMoment B node4040 node4040Labels := by
  calc
    mixedMoment B raw14946 raw14946Labels = mixedMoment B raw14946step0 raw14946step0Labels := by
      have hz : ∀ j, raw14946 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14946step0 = (fun i j => raw14946 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14946step0 raw14946; decide +kernel
      have hl : raw14946step0Labels = raw14946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14946 raw14946Labels permutation434 hz
    mixedMoment B raw14946step0 raw14946step0Labels = mixedMoment B raw14946step1 raw14946step1Labels := by
      have hz : ∀ j, raw14946step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14946step1 = (fun i j => raw14946step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14946step1 raw14946step0; decide +kernel
      have hl : raw14946step1Labels = raw14946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14946step0 raw14946step0Labels permutation80 hz
    mixedMoment B raw14946step1 raw14946step1Labels = mixedMoment B raw14946step2 raw14946step2Labels := by
      have ha : raw14946step2 = (fun i j => raw14946step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14946step2 raw14946step1; decide +kernel
      have hl : raw14946step2Labels = raw14946step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14946step1 raw14946step1Labels permutation31 permutation3
    mixedMoment B raw14946step2 raw14946step2Labels = mixedMoment B raw14946step3 raw14946step3Labels := by
      have ha : raw14946step3 = -raw14946step2 := by apply Matrix.ext; change ∀ i j, raw14946step3 i j = -(raw14946step2 i j); unfold raw14946step3 raw14946step2; decide +kernel
      have hl : raw14946step3Labels = raw14946step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4040 node4040Labels := by rfl

def raw14947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14947step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14947 raw14947Labels = mixedMoment B node4015 node4015Labels := by
  calc
    mixedMoment B raw14947 raw14947Labels = mixedMoment B raw14947step0 raw14947step0Labels := by
      have hz : ∀ j, raw14947 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14947step0 = (fun i j => raw14947 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14947step0 raw14947; decide +kernel
      have hl : raw14947step0Labels = raw14947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14947 raw14947Labels permutation434 hz
    mixedMoment B raw14947step0 raw14947step0Labels = mixedMoment B raw14947step1 raw14947step1Labels := by
      have hz : ∀ j, raw14947step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14947step1 = (fun i j => raw14947step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14947step1 raw14947step0; decide +kernel
      have hl : raw14947step1Labels = raw14947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14947step0 raw14947step0Labels permutation80 hz
    mixedMoment B raw14947step1 raw14947step1Labels = mixedMoment B raw14947step2 raw14947step2Labels := by
      have ha : raw14947step2 = (fun i j => raw14947step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14947step2 raw14947step1; decide +kernel
      have hl : raw14947step2Labels = raw14947step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14947step1 raw14947step1Labels permutation26 permutation6
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw14948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14948step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14948 raw14948Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw14948 raw14948Labels = mixedMoment B raw14948step0 raw14948step0Labels := by
      have hz : ∀ j, raw14948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14948step0 = (fun i j => raw14948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14948step0 raw14948; decide +kernel
      have hl : raw14948step0Labels = raw14948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14948 raw14948Labels permutation434 hz
    mixedMoment B raw14948step0 raw14948step0Labels = mixedMoment B raw14948step1 raw14948step1Labels := by
      have hz : ∀ j, raw14948step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14948step1 = (fun i j => raw14948step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14948step1 raw14948step0; decide +kernel
      have hl : raw14948step1Labels = raw14948step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14948step0 raw14948step0Labels permutation80 hz
    mixedMoment B raw14948step1 raw14948step1Labels = mixedMoment B raw14948step2 raw14948step2Labels := by
      have ha : raw14948step2 = (fun i j => raw14948step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14948step2 raw14948step1; decide +kernel
      have hl : raw14948step2Labels = raw14948step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14948step1 raw14948step1Labels permutation8 permutation3
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw14949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14949 raw14949Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw14949 raw14949Labels = mixedMoment B raw14949step0 raw14949step0Labels := by
      have hz : ∀ j, raw14949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14949step0 = (fun i j => raw14949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14949step0 raw14949; decide +kernel
      have hl : raw14949step0Labels = raw14949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14949 raw14949Labels permutation434 hz
    mixedMoment B raw14949step0 raw14949step0Labels = mixedMoment B raw14949step1 raw14949step1Labels := by
      have ha : raw14949step1 = (fun i j => raw14949step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14949step1 raw14949step0; decide +kernel
      have hl : raw14949step1Labels = raw14949step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14949step0 raw14949step0Labels permutation38 permutation3
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw14950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14950 raw14950Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw14950 raw14950Labels = mixedMoment B raw14950step0 raw14950step0Labels := by
      have hz : ∀ j, raw14950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14950step0 = (fun i j => raw14950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14950step0 raw14950; decide +kernel
      have hl : raw14950step0Labels = raw14950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14950 raw14950Labels permutation346 hz
    mixedMoment B raw14950step0 raw14950step0Labels = mixedMoment B raw14950step1 raw14950step1Labels := by
      have ha : raw14950step1 = (fun i j => raw14950step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14950step1 raw14950step0; decide +kernel
      have hl : raw14950step1Labels = raw14950step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14950step0 raw14950step0Labels permutation38 permutation3
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw14951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14951step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14951 raw14951Labels = mixedMoment B node3912 node3912Labels := by
  calc
    mixedMoment B raw14951 raw14951Labels = mixedMoment B raw14951step0 raw14951step0Labels := by
      have hz : ∀ j, raw14951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14951step0 = (fun i j => raw14951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14951step0 raw14951; decide +kernel
      have hl : raw14951step0Labels = raw14951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14951 raw14951Labels permutation434 hz
    mixedMoment B raw14951step0 raw14951step0Labels = mixedMoment B raw14951step1 raw14951step1Labels := by
      have hz : ∀ j, raw14951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14951step1 = (fun i j => raw14951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14951step1 raw14951step0; decide +kernel
      have hl : raw14951step1Labels = raw14951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14951step0 raw14951step0Labels permutation80 hz
    mixedMoment B raw14951step1 raw14951step1Labels = mixedMoment B raw14951step2 raw14951step2Labels := by
      have ha : raw14951step2 = (fun i j => raw14951step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14951step2 raw14951step1; decide +kernel
      have hl : raw14951step2Labels = raw14951step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14951step1 raw14951step1Labels permutation8 permutation3
    _ = mixedMoment B node3912 node3912Labels := by rfl

def raw14952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14952step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14952step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw14952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14952 raw14952Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw14952 raw14952Labels = mixedMoment B raw14952step0 raw14952step0Labels := by
      have hz : ∀ j, raw14952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14952step0 = (fun i j => raw14952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14952step0 raw14952; decide +kernel
      have hl : raw14952step0Labels = raw14952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14952 raw14952Labels permutation434 hz
    mixedMoment B raw14952step0 raw14952step0Labels = mixedMoment B raw14952step1 raw14952step1Labels := by
      have hz : ∀ j, raw14952step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14952step1 = (fun i j => raw14952step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14952step1 raw14952step0; decide +kernel
      have hl : raw14952step1Labels = raw14952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14952step0 raw14952step0Labels permutation80 hz
    mixedMoment B raw14952step1 raw14952step1Labels = mixedMoment B raw14952step2 raw14952step2Labels := by
      have ha : raw14952step2 = (fun i j => raw14952step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14952step2 raw14952step1; decide +kernel
      have hl : raw14952step2Labels = raw14952step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14952step1 raw14952step1Labels permutation9 permutation3
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw14953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14953step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14953 raw14953Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw14953 raw14953Labels = mixedMoment B raw14953step0 raw14953step0Labels := by
      have hz : ∀ j, raw14953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14953step0 = (fun i j => raw14953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14953step0 raw14953; decide +kernel
      have hl : raw14953step0Labels = raw14953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14953 raw14953Labels permutation434 hz
    mixedMoment B raw14953step0 raw14953step0Labels = mixedMoment B raw14953step1 raw14953step1Labels := by
      have ha : raw14953step1 = (fun i j => raw14953step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14953step1 raw14953step0; decide +kernel
      have hl : raw14953step1Labels = raw14953step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14953step0 raw14953step0Labels permutation32 permutation3
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw14954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14954step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14954 raw14954Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw14954 raw14954Labels = mixedMoment B raw14954step0 raw14954step0Labels := by
      have hz : ∀ j, raw14954 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14954step0 = (fun i j => raw14954 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14954step0 raw14954; decide +kernel
      have hl : raw14954step0Labels = raw14954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14954 raw14954Labels permutation434 hz
    mixedMoment B raw14954step0 raw14954step0Labels = mixedMoment B raw14954step1 raw14954step1Labels := by
      have ha : raw14954step1 = (fun i j => raw14954step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14954step1 raw14954step0; decide +kernel
      have hl : raw14954step1Labels = raw14954step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14954step0 raw14954step0Labels permutation32 permutation3
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw14955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14955 raw14955Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw14955 raw14955Labels = mixedMoment B raw14955step0 raw14955step0Labels := by
      have ha : raw14955step0 = (fun i j => raw14955 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14955step0 raw14955; decide +kernel
      have hl : raw14955step0Labels = raw14955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14955 raw14955Labels permutation200 permutation3
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw14956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14956step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14956 raw14956Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw14956 raw14956Labels = mixedMoment B raw14956step0 raw14956step0Labels := by
      have hz : ∀ j, raw14956 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14956step0 = (fun i j => raw14956 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14956step0 raw14956; decide +kernel
      have hl : raw14956step0Labels = raw14956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14956 raw14956Labels permutation434 hz
    mixedMoment B raw14956step0 raw14956step0Labels = mixedMoment B raw14956step1 raw14956step1Labels := by
      have ha : raw14956step1 = (fun i j => raw14956step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14956step1 raw14956step0; decide +kernel
      have hl : raw14956step1Labels = raw14956step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14956step0 raw14956step0Labels permutation34 permutation3
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw14957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14957step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14957 raw14957Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw14957 raw14957Labels = mixedMoment B raw14957step0 raw14957step0Labels := by
      have hz : ∀ j, raw14957 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14957step0 = (fun i j => raw14957 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14957step0 raw14957; decide +kernel
      have hl : raw14957step0Labels = raw14957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14957 raw14957Labels permutation434 hz
    mixedMoment B raw14957step0 raw14957step0Labels = mixedMoment B raw14957step1 raw14957step1Labels := by
      have ha : raw14957step1 = (fun i j => raw14957step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14957step1 raw14957step0; decide +kernel
      have hl : raw14957step1Labels = raw14957step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14957step0 raw14957step0Labels permutation36 permutation3
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw14958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14958step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14958 raw14958Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw14958 raw14958Labels = mixedMoment B raw14958step0 raw14958step0Labels := by
      have hz : ∀ j, raw14958 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14958step0 = (fun i j => raw14958 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14958step0 raw14958; decide +kernel
      have hl : raw14958step0Labels = raw14958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14958 raw14958Labels permutation346 hz
    mixedMoment B raw14958step0 raw14958step0Labels = mixedMoment B raw14958step1 raw14958step1Labels := by
      have ha : raw14958step1 = (fun i j => raw14958step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14958step1 raw14958step0; decide +kernel
      have hl : raw14958step1Labels = raw14958step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14958step0 raw14958step0Labels permutation32 permutation3
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw14959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14959step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14959 raw14959Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw14959 raw14959Labels = mixedMoment B raw14959step0 raw14959step0Labels := by
      have hz : ∀ j, raw14959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14959step0 = (fun i j => raw14959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14959step0 raw14959; decide +kernel
      have hl : raw14959step0Labels = raw14959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14959 raw14959Labels permutation346 hz
    mixedMoment B raw14959step0 raw14959step0Labels = mixedMoment B raw14959step1 raw14959step1Labels := by
      have ha : raw14959step1 = (fun i j => raw14959step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14959step1 raw14959step0; decide +kernel
      have hl : raw14959step1Labels = raw14959step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14959step0 raw14959step0Labels permutation32 permutation3
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw14960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw14960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14960 raw14960Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw14960 raw14960Labels = mixedMoment B raw14960step0 raw14960step0Labels := by
      have ha : raw14960step0 = (fun i j => raw14960 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14960step0 raw14960; decide +kernel
      have hl : raw14960step0Labels = raw14960Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14960 raw14960Labels permutation176 permutation3
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw14961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw14961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14961 raw14961Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw14961 raw14961Labels = mixedMoment B raw14961step0 raw14961step0Labels := by
      have hz : ∀ j, raw14961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14961step0 = (fun i j => raw14961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14961step0 raw14961; decide +kernel
      have hl : raw14961step0Labels = raw14961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14961 raw14961Labels permutation346 hz
    mixedMoment B raw14961step0 raw14961step0Labels = mixedMoment B raw14961step1 raw14961step1Labels := by
      have ha : raw14961step1 = (fun i j => raw14961step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14961step1 raw14961step0; decide +kernel
      have hl : raw14961step1Labels = raw14961step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14961step0 raw14961step0Labels permutation34 permutation3
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw14962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw14962step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14962 raw14962Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw14962 raw14962Labels = mixedMoment B raw14962step0 raw14962step0Labels := by
      have hz : ∀ j, raw14962 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14962step0 = (fun i j => raw14962 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14962step0 raw14962; decide +kernel
      have hl : raw14962step0Labels = raw14962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14962 raw14962Labels permutation346 hz
    mixedMoment B raw14962step0 raw14962step0Labels = mixedMoment B raw14962step1 raw14962step1Labels := by
      have ha : raw14962step1 = (fun i j => raw14962step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14962step1 raw14962step0; decide +kernel
      have hl : raw14962step1Labels = raw14962step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14962step0 raw14962step0Labels permutation36 permutation3
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw14963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14963step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw14963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14963 raw14963Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw14963 raw14963Labels = mixedMoment B raw14963step0 raw14963step0Labels := by
      have hz : ∀ j, raw14963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14963step0 = (fun i j => raw14963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14963step0 raw14963; decide +kernel
      have hl : raw14963step0Labels = raw14963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14963 raw14963Labels permutation434 hz
    mixedMoment B raw14963step0 raw14963step0Labels = mixedMoment B raw14963step1 raw14963step1Labels := by
      have hz : ∀ j, raw14963step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14963step1 = (fun i j => raw14963step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14963step1 raw14963step0; decide +kernel
      have hl : raw14963step1Labels = raw14963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14963step0 raw14963step0Labels permutation80 hz
    mixedMoment B raw14963step1 raw14963step1Labels = mixedMoment B raw14963step2 raw14963step2Labels := by
      have ha : raw14963step2 = (fun i j => raw14963step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14963step2 raw14963step1; decide +kernel
      have hl : raw14963step2Labels = raw14963step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14963step1 raw14963step1Labels permutation9 permutation3
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw14964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14964step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14964step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw14964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14964step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw14964step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14964 raw14964Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw14964 raw14964Labels = mixedMoment B raw14964step0 raw14964step0Labels := by
      have hz : ∀ j, raw14964 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14964step0 = (fun i j => raw14964 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14964step0 raw14964; decide +kernel
      have hl : raw14964step0Labels = raw14964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14964 raw14964Labels permutation434 hz
    mixedMoment B raw14964step0 raw14964step0Labels = mixedMoment B raw14964step1 raw14964step1Labels := by
      have hz : ∀ j, raw14964step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14964step1 = (fun i j => raw14964step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14964step1 raw14964step0; decide +kernel
      have hl : raw14964step1Labels = raw14964step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14964step0 raw14964step0Labels permutation80 hz
    mixedMoment B raw14964step1 raw14964step1Labels = mixedMoment B raw14964step2 raw14964step2Labels := by
      have ha : raw14964step2 = (fun i j => raw14964step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14964step2 raw14964step1; decide +kernel
      have hl : raw14964step2Labels = raw14964step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14964step1 raw14964step1Labels permutation25 permutation3
    mixedMoment B raw14964step2 raw14964step2Labels = mixedMoment B raw14964step3 raw14964step3Labels := by
      have ha : raw14964step3 = -raw14964step2 := by apply Matrix.ext; change ∀ i j, raw14964step3 i j = -(raw14964step2 i j); unfold raw14964step3 raw14964step2; decide +kernel
      have hl : raw14964step3Labels = raw14964step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw14965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14965 raw14965Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw14965 raw14965Labels = mixedMoment B raw14965step0 raw14965step0Labels := by
      have hz : ∀ j, raw14965 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14965step0 = (fun i j => raw14965 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14965step0 raw14965; decide +kernel
      have hl : raw14965step0Labels = raw14965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14965 raw14965Labels permutation434 hz
    mixedMoment B raw14965step0 raw14965step0Labels = mixedMoment B raw14965step1 raw14965step1Labels := by
      have ha : raw14965step1 = (fun i j => raw14965step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14965step1 raw14965step0; decide +kernel
      have hl : raw14965step1Labels = raw14965step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14965step0 raw14965step0Labels permutation125 permutation3
    mixedMoment B raw14965step1 raw14965step1Labels = mixedMoment B raw14965step2 raw14965step2Labels := by
      have ha : raw14965step2 = -raw14965step1 := by apply Matrix.ext; change ∀ i j, raw14965step2 i j = -(raw14965step1 i j); unfold raw14965step2 raw14965step1; decide +kernel
      have hl : raw14965step2Labels = raw14965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw14966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw14966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14966 raw14966Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw14966 raw14966Labels = mixedMoment B raw14966step0 raw14966step0Labels := by
      have hz : ∀ j, raw14966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14966step0 = (fun i j => raw14966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14966step0 raw14966; decide +kernel
      have hl : raw14966step0Labels = raw14966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14966 raw14966Labels permutation346 hz
    mixedMoment B raw14966step0 raw14966step0Labels = mixedMoment B raw14966step1 raw14966step1Labels := by
      have ha : raw14966step1 = (fun i j => raw14966step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14966step1 raw14966step0; decide +kernel
      have hl : raw14966step1Labels = raw14966step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14966step0 raw14966step0Labels permutation125 permutation3
    mixedMoment B raw14966step1 raw14966step1Labels = mixedMoment B raw14966step2 raw14966step2Labels := by
      have ha : raw14966step2 = -raw14966step1 := by apply Matrix.ext; change ∀ i j, raw14966step2 i j = -(raw14966step1 i j); unfold raw14966step2 raw14966step1; decide +kernel
      have hl : raw14966step2Labels = raw14966step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw14967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw14967step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14967step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14967step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14967step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14967 raw14967Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw14967 raw14967Labels = mixedMoment B raw14967step0 raw14967step0Labels := by
      have hz : ∀ j, raw14967 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14967step0 = (fun i j => raw14967 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14967step0 raw14967; decide +kernel
      have hl : raw14967step0Labels = raw14967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14967 raw14967Labels permutation434 hz
    mixedMoment B raw14967step0 raw14967step0Labels = mixedMoment B raw14967step1 raw14967step1Labels := by
      have hz : ∀ j, raw14967step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14967step1 = (fun i j => raw14967step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14967step1 raw14967step0; decide +kernel
      have hl : raw14967step1Labels = raw14967step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14967step0 raw14967step0Labels permutation80 hz
    mixedMoment B raw14967step1 raw14967step1Labels = mixedMoment B raw14967step2 raw14967step2Labels := by
      have ha : raw14967step2 = (fun i j => raw14967step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14967step2 raw14967step1; decide +kernel
      have hl : raw14967step2Labels = raw14967step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14967step1 raw14967step1Labels permutation25 permutation3
    mixedMoment B raw14967step2 raw14967step2Labels = mixedMoment B raw14967step3 raw14967step3Labels := by
      have ha : raw14967step3 = -raw14967step2 := by apply Matrix.ext; change ∀ i j, raw14967step3 i j = -(raw14967step2 i j); unfold raw14967step3 raw14967step2; decide +kernel
      have hl : raw14967step3Labels = raw14967step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw14968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14968step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw14968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14968 raw14968Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw14968 raw14968Labels = mixedMoment B raw14968step0 raw14968step0Labels := by
      have hz : ∀ j, raw14968 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14968step0 = (fun i j => raw14968 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14968step0 raw14968; decide +kernel
      have hl : raw14968step0Labels = raw14968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14968 raw14968Labels permutation434 hz
    mixedMoment B raw14968step0 raw14968step0Labels = mixedMoment B raw14968step1 raw14968step1Labels := by
      have hz : ∀ j, raw14968step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14968step1 = (fun i j => raw14968step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14968step1 raw14968step0; decide +kernel
      have hl : raw14968step1Labels = raw14968step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14968step0 raw14968step0Labels permutation80 hz
    mixedMoment B raw14968step1 raw14968step1Labels = mixedMoment B raw14968step2 raw14968step2Labels := by
      have ha : raw14968step2 = (fun i j => raw14968step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14968step2 raw14968step1; decide +kernel
      have hl : raw14968step2Labels = raw14968step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14968step1 raw14968step1Labels permutation8 permutation3
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw14969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14969step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14969step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw14969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14969step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw14969step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14969 raw14969Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw14969 raw14969Labels = mixedMoment B raw14969step0 raw14969step0Labels := by
      have hz : ∀ j, raw14969 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14969step0 = (fun i j => raw14969 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14969step0 raw14969; decide +kernel
      have hl : raw14969step0Labels = raw14969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14969 raw14969Labels permutation434 hz
    mixedMoment B raw14969step0 raw14969step0Labels = mixedMoment B raw14969step1 raw14969step1Labels := by
      have hz : ∀ j, raw14969step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14969step1 = (fun i j => raw14969step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14969step1 raw14969step0; decide +kernel
      have hl : raw14969step1Labels = raw14969step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14969step0 raw14969step0Labels permutation80 hz
    mixedMoment B raw14969step1 raw14969step1Labels = mixedMoment B raw14969step2 raw14969step2Labels := by
      have ha : raw14969step2 = (fun i j => raw14969step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14969step2 raw14969step1; decide +kernel
      have hl : raw14969step2Labels = raw14969step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14969step1 raw14969step1Labels permutation31 permutation3
    mixedMoment B raw14969step2 raw14969step2Labels = mixedMoment B raw14969step3 raw14969step3Labels := by
      have ha : raw14969step3 = -raw14969step2 := by apply Matrix.ext; change ∀ i j, raw14969step3 i j = -(raw14969step2 i j); unfold raw14969step3 raw14969step2; decide +kernel
      have hl : raw14969step3Labels = raw14969step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw14970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14970 raw14970Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw14970 raw14970Labels = mixedMoment B raw14970step0 raw14970step0Labels := by
      have hz : ∀ j, raw14970 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14970step0 = (fun i j => raw14970 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14970step0 raw14970; decide +kernel
      have hl : raw14970step0Labels = raw14970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14970 raw14970Labels permutation434 hz
    mixedMoment B raw14970step0 raw14970step0Labels = mixedMoment B raw14970step1 raw14970step1Labels := by
      have ha : raw14970step1 = (fun i j => raw14970step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14970step1 raw14970step0; decide +kernel
      have hl : raw14970step1Labels = raw14970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14970step0 raw14970step0Labels permutation149 permutation3
    mixedMoment B raw14970step1 raw14970step1Labels = mixedMoment B raw14970step2 raw14970step2Labels := by
      have ha : raw14970step2 = -raw14970step1 := by apply Matrix.ext; change ∀ i j, raw14970step2 i j = -(raw14970step1 i j); unfold raw14970step2 raw14970step1; decide +kernel
      have hl : raw14970step2Labels = raw14970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw14971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw14971step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw14971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14971 raw14971Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw14971 raw14971Labels = mixedMoment B raw14971step0 raw14971step0Labels := by
      have hz : ∀ j, raw14971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14971step0 = (fun i j => raw14971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14971step0 raw14971; decide +kernel
      have hl : raw14971step0Labels = raw14971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14971 raw14971Labels permutation346 hz
    mixedMoment B raw14971step0 raw14971step0Labels = mixedMoment B raw14971step1 raw14971step1Labels := by
      have ha : raw14971step1 = (fun i j => raw14971step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14971step1 raw14971step0; decide +kernel
      have hl : raw14971step1Labels = raw14971step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14971step0 raw14971step0Labels permutation149 permutation3
    mixedMoment B raw14971step1 raw14971step1Labels = mixedMoment B raw14971step2 raw14971step2Labels := by
      have ha : raw14971step2 = -raw14971step1 := by apply Matrix.ext; change ∀ i j, raw14971step2 i j = -(raw14971step1 i j); unfold raw14971step2 raw14971step1; decide +kernel
      have hl : raw14971step2Labels = raw14971step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw14972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw14972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw14972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2]]
def raw14972step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14972 raw14972Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw14972 raw14972Labels = mixedMoment B raw14972step0 raw14972step0Labels := by
      have hz : ∀ j, raw14972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14972step0 = (fun i j => raw14972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14972step0 raw14972; decide +kernel
      have hl : raw14972step0Labels = raw14972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14972 raw14972Labels permutation434 hz
    mixedMoment B raw14972step0 raw14972step0Labels = mixedMoment B raw14972step1 raw14972step1Labels := by
      have hz : ∀ j, raw14972step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14972step1 = (fun i j => raw14972step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14972step1 raw14972step0; decide +kernel
      have hl : raw14972step1Labels = raw14972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14972step0 raw14972step0Labels permutation80 hz
    mixedMoment B raw14972step1 raw14972step1Labels = mixedMoment B raw14972step2 raw14972step2Labels := by
      have ha : raw14972step2 = (fun i j => raw14972step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14972step2 raw14972step1; decide +kernel
      have hl : raw14972step2Labels = raw14972step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14972step1 raw14972step1Labels permutation31 permutation3
    mixedMoment B raw14972step2 raw14972step2Labels = mixedMoment B raw14972step3 raw14972step3Labels := by
      have ha : raw14972step3 = -raw14972step2 := by apply Matrix.ext; change ∀ i j, raw14972step3 i j = -(raw14972step2 i j); unfold raw14972step3 raw14972step2; decide +kernel
      have hl : raw14972step3Labels = raw14972step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw14973 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14973step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14973step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14973step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14973step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14973step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14973 raw14973Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw14973 raw14973Labels = mixedMoment B raw14973step0 raw14973step0Labels := by
      have hz : ∀ j, raw14973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14973step0 = (fun i j => raw14973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14973step0 raw14973; decide +kernel
      have hl : raw14973step0Labels = raw14973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14973 raw14973Labels permutation434 hz
    mixedMoment B raw14973step0 raw14973step0Labels = mixedMoment B raw14973step1 raw14973step1Labels := by
      have hz : ∀ j, raw14973step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14973step1 = (fun i j => raw14973step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14973step1 raw14973step0; decide +kernel
      have hl : raw14973step1Labels = raw14973step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14973step0 raw14973step0Labels permutation80 hz
    mixedMoment B raw14973step1 raw14973step1Labels = mixedMoment B raw14973step2 raw14973step2Labels := by
      have ha : raw14973step2 = (fun i j => raw14973step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14973step2 raw14973step1; decide +kernel
      have hl : raw14973step2Labels = raw14973step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14973step1 raw14973step1Labels permutation31 permutation7
    mixedMoment B raw14973step2 raw14973step2Labels = mixedMoment B raw14973step3 raw14973step3Labels := by
      have ha : raw14973step3 = -raw14973step2 := by apply Matrix.ext; change ∀ i j, raw14973step3 i j = -(raw14973step2 i j); unfold raw14973step3 raw14973step2; decide +kernel
      have hl : raw14973step3Labels = raw14973step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14973step3 raw14973step3Labels = mixedMoment B raw14973step4 raw14973step4Labels := by
      have ha : raw14973step4 = raw14973step3 := by apply Matrix.ext; unfold raw14973step4 raw14973step3; decide +kernel
      have hl : raw14973step3Labels = labelEmbedding10 ∘ raw14973step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14973step3 raw14973step3Labels raw14973step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw14974 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14974step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14974 raw14974Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw14974 raw14974Labels = mixedMoment B raw14974step0 raw14974step0Labels := by
      have hz : ∀ j, raw14974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14974step0 = (fun i j => raw14974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14974step0 raw14974; decide +kernel
      have hl : raw14974step0Labels = raw14974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14974 raw14974Labels permutation346 hz
    mixedMoment B raw14974step0 raw14974step0Labels = mixedMoment B raw14974step1 raw14974step1Labels := by
      have ha : raw14974step1 = (fun i j => raw14974step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14974step1 raw14974step0; decide +kernel
      have hl : raw14974step1Labels = raw14974step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14974step0 raw14974step0Labels permutation145 permutation2
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw14975 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14975step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2]]
def raw14975step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14975step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw14975step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14975step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14975step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14975step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14975step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14975 raw14975Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw14975 raw14975Labels = mixedMoment B raw14975step0 raw14975step0Labels := by
      have hz : ∀ j, raw14975 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14975step0 = (fun i j => raw14975 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14975step0 raw14975; decide +kernel
      have hl : raw14975step0Labels = raw14975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14975 raw14975Labels permutation434 hz
    mixedMoment B raw14975step0 raw14975step0Labels = mixedMoment B raw14975step1 raw14975step1Labels := by
      have hz : ∀ j, raw14975step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14975step1 = (fun i j => raw14975step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14975step1 raw14975step0; decide +kernel
      have hl : raw14975step1Labels = raw14975step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14975step0 raw14975step0Labels permutation80 hz
    mixedMoment B raw14975step1 raw14975step1Labels = mixedMoment B raw14975step2 raw14975step2Labels := by
      have ha : raw14975step2 = (fun i j => raw14975step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14975step2 raw14975step1; decide +kernel
      have hl : raw14975step2Labels = raw14975step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14975step1 raw14975step1Labels permutation31 permutation7
    mixedMoment B raw14975step2 raw14975step2Labels = mixedMoment B raw14975step3 raw14975step3Labels := by
      have ha : raw14975step3 = -raw14975step2 := by apply Matrix.ext; change ∀ i j, raw14975step3 i j = -(raw14975step2 i j); unfold raw14975step3 raw14975step2; decide +kernel
      have hl : raw14975step3Labels = raw14975step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14975step3 raw14975step3Labels = mixedMoment B raw14975step4 raw14975step4Labels := by
      have ha : raw14975step4 = raw14975step3 := by apply Matrix.ext; unfold raw14975step4 raw14975step3; decide +kernel
      have hl : raw14975step3Labels = labelEmbedding10 ∘ raw14975step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14975step3 raw14975step3Labels raw14975step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
