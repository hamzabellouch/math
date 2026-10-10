import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26112 raw26112Labels = mixedMoment B node892 node892Labels := by
  calc
    mixedMoment B raw26112 raw26112Labels = mixedMoment B raw26112step0 raw26112step0Labels := by
      have hz : ∀ j, raw26112 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26112step0 = (fun i j => raw26112 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26112step0 raw26112; decide +kernel
      have hl : raw26112step0Labels = raw26112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26112 raw26112Labels permutation265 hz
    _ = mixedMoment B node892 node892Labels := by rfl

def raw26113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw26113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26113 raw26113Labels = mixedMoment B node887 node887Labels := by
  calc
    mixedMoment B raw26113 raw26113Labels = mixedMoment B raw26113step0 raw26113step0Labels := by
      have hz : ∀ j, raw26113 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26113step0 = (fun i j => raw26113 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26113step0 raw26113; decide +kernel
      have hl : raw26113step0Labels = raw26113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26113 raw26113Labels permutation265 hz
    mixedMoment B raw26113step0 raw26113step0Labels = mixedMoment B raw26113step1 raw26113step1Labels := by
      have ha : raw26113step1 = (fun i j => raw26113step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26113step1 raw26113step0; decide +kernel
      have hl : raw26113step1Labels = raw26113step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26113step0 raw26113step0Labels permutation34 permutation2
    _ = mixedMoment B node887 node887Labels := by rfl

def raw26114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26114 raw26114Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw26114 raw26114Labels = mixedMoment B raw26114step0 raw26114step0Labels := by
      have ha : raw26114step0 = (fun i j => raw26114 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26114step0 raw26114; decide +kernel
      have hl : raw26114step0Labels = raw26114Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26114 raw26114Labels permutation179 permutation2
    _ = mixedMoment B node998 node998Labels := by rfl

def raw26115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26115 raw26115Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw26115 raw26115Labels = mixedMoment B raw26115step0 raw26115step0Labels := by
      have hz : ∀ j, raw26115 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26115step0 = (fun i j => raw26115 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26115step0 raw26115; decide +kernel
      have hl : raw26115step0Labels = raw26115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26115 raw26115Labels permutation265 hz
    mixedMoment B raw26115step0 raw26115step0Labels = mixedMoment B raw26115step1 raw26115step1Labels := by
      have ha : raw26115step1 = (fun i j => raw26115step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26115step1 raw26115step0; decide +kernel
      have hl : raw26115step1Labels = raw26115step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26115step0 raw26115step0Labels permutation35 permutation2
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw26116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26116step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26116 raw26116Labels = mixedMoment B node1004 node1004Labels := by
  calc
    mixedMoment B raw26116 raw26116Labels = mixedMoment B raw26116step0 raw26116step0Labels := by
      have hz : ∀ j, raw26116 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26116step0 = (fun i j => raw26116 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26116step0 raw26116; decide +kernel
      have hl : raw26116step0Labels = raw26116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26116 raw26116Labels permutation265 hz
    mixedMoment B raw26116step0 raw26116step0Labels = mixedMoment B raw26116step1 raw26116step1Labels := by
      have ha : raw26116step1 = (fun i j => raw26116step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26116step1 raw26116step0; decide +kernel
      have hl : raw26116step1Labels = raw26116step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26116step0 raw26116step0Labels permutation35 permutation2
    _ = mixedMoment B node1004 node1004Labels := by rfl

def raw26117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw26117Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw26117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26117step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26117 raw26117Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw26117 raw26117Labels = mixedMoment B raw26117step0 raw26117step0Labels := by
      have hz : ∀ j, raw26117 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26117step0 = (fun i j => raw26117 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26117step0 raw26117; decide +kernel
      have hl : raw26117step0Labels = raw26117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26117 raw26117Labels permutation265 hz
    mixedMoment B raw26117step0 raw26117step0Labels = mixedMoment B raw26117step1 raw26117step1Labels := by
      have ha : raw26117step1 = (fun i j => raw26117step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26117step1 raw26117step0; decide +kernel
      have hl : raw26117step1Labels = raw26117step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26117step0 raw26117step0Labels permutation36 permutation2
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw26118 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26118 raw26118Labels = mixedMoment B node1623 node1623Labels := by
  calc
    mixedMoment B raw26118 raw26118Labels = mixedMoment B raw26118step0 raw26118step0Labels := by
      have hz : ∀ j, raw26118 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26118step0 = (fun i j => raw26118 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26118step0 raw26118; decide +kernel
      have hl : raw26118step0Labels = raw26118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26118 raw26118Labels permutation265 hz
    mixedMoment B raw26118step0 raw26118step0Labels = mixedMoment B raw26118step1 raw26118step1Labels := by
      have ha : raw26118step1 = (fun i j => raw26118step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26118step1 raw26118step0; decide +kernel
      have hl : raw26118step1Labels = raw26118step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26118step0 raw26118step0Labels permutation35 permutation4
    mixedMoment B raw26118step1 raw26118step1Labels = mixedMoment B raw26118step2 raw26118step2Labels := by
      have ha : raw26118step2 = -raw26118step1 := by apply Matrix.ext; change ∀ i j, raw26118step2 i j = -(raw26118step1 i j); unfold raw26118step2 raw26118step1; decide +kernel
      have hl : raw26118step2Labels = raw26118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1623 node1623Labels := by rfl

def raw26119 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26119step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26119 raw26119Labels = mixedMoment B node856 node856Labels := by
  calc
    mixedMoment B raw26119 raw26119Labels = mixedMoment B raw26119step0 raw26119step0Labels := by
      have hz : ∀ j, raw26119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26119step0 = (fun i j => raw26119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26119step0 raw26119; decide +kernel
      have hl : raw26119step0Labels = raw26119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26119 raw26119Labels permutation346 hz
    mixedMoment B raw26119step0 raw26119step0Labels = mixedMoment B raw26119step1 raw26119step1Labels := by
      have hz : ∀ j, raw26119step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26119step1 = (fun i j => raw26119step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26119step1 raw26119step0; decide +kernel
      have hl : raw26119step1Labels = raw26119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26119step0 raw26119step0Labels permutation56 hz
    mixedMoment B raw26119step1 raw26119step1Labels = mixedMoment B raw26119step2 raw26119step2Labels := by
      have ha : raw26119step2 = (fun i j => raw26119step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26119step2 raw26119step1; decide +kernel
      have hl : raw26119step2Labels = raw26119step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26119step1 raw26119step1Labels permutation11 permutation4
    mixedMoment B raw26119step2 raw26119step2Labels = mixedMoment B raw26119step3 raw26119step3Labels := by
      have ha : raw26119step3 = -raw26119step2 := by apply Matrix.ext; change ∀ i j, raw26119step3 i j = -(raw26119step2 i j); unfold raw26119step3 raw26119step2; decide +kernel
      have hl : raw26119step3Labels = raw26119step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node856 node856Labels := by rfl

def raw26120 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26120Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26120step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw26120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw26120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26120 raw26120Labels = mixedMoment B node720 node720Labels := by
  calc
    mixedMoment B raw26120 raw26120Labels = mixedMoment B raw26120step0 raw26120step0Labels := by
      have hz : ∀ j, raw26120 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26120step0 = (fun i j => raw26120 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26120step0 raw26120; decide +kernel
      have hl : raw26120step0Labels = raw26120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26120 raw26120Labels permutation265 hz
    mixedMoment B raw26120step0 raw26120step0Labels = mixedMoment B raw26120step1 raw26120step1Labels := by
      have ha : raw26120step1 = (fun i j => raw26120step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26120step1 raw26120step0; decide +kernel
      have hl : raw26120step1Labels = raw26120step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26120step0 raw26120step0Labels permutation35 permutation4
    mixedMoment B raw26120step1 raw26120step1Labels = mixedMoment B raw26120step2 raw26120step2Labels := by
      have ha : raw26120step2 = -raw26120step1 := by apply Matrix.ext; change ∀ i j, raw26120step2 i j = -(raw26120step1 i j); unfold raw26120step2 raw26120step1; decide +kernel
      have hl : raw26120step2Labels = raw26120step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node720 node720Labels := by rfl

def raw26121 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26121Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw26121step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26121 raw26121Labels = mixedMoment B node725 node725Labels := by
  calc
    mixedMoment B raw26121 raw26121Labels = mixedMoment B raw26121step0 raw26121step0Labels := by
      have hz : ∀ j, raw26121 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26121step0 = (fun i j => raw26121 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26121step0 raw26121; decide +kernel
      have hl : raw26121step0Labels = raw26121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26121 raw26121Labels permutation265 hz
    mixedMoment B raw26121step0 raw26121step0Labels = mixedMoment B raw26121step1 raw26121step1Labels := by
      have ha : raw26121step1 = (fun i j => raw26121step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26121step1 raw26121step0; decide +kernel
      have hl : raw26121step1Labels = raw26121step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26121step0 raw26121step0Labels permutation36 permutation4
    mixedMoment B raw26121step1 raw26121step1Labels = mixedMoment B raw26121step2 raw26121step2Labels := by
      have ha : raw26121step2 = -raw26121step1 := by apply Matrix.ext; change ∀ i j, raw26121step2 i j = -(raw26121step1 i j); unfold raw26121step2 raw26121step1; decide +kernel
      have hl : raw26121step2Labels = raw26121step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node725 node725Labels := by rfl

def raw26122 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26122Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26122step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw26122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26122 raw26122Labels = mixedMoment B node722 node722Labels := by
  calc
    mixedMoment B raw26122 raw26122Labels = mixedMoment B raw26122step0 raw26122step0Labels := by
      have hz : ∀ j, raw26122 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26122step0 = (fun i j => raw26122 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26122step0 raw26122; decide +kernel
      have hl : raw26122step0Labels = raw26122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26122 raw26122Labels permutation265 hz
    mixedMoment B raw26122step0 raw26122step0Labels = mixedMoment B raw26122step1 raw26122step1Labels := by
      have ha : raw26122step1 = (fun i j => raw26122step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26122step1 raw26122step0; decide +kernel
      have hl : raw26122step1Labels = raw26122step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26122step0 raw26122step0Labels permutation34 permutation4
    mixedMoment B raw26122step1 raw26122step1Labels = mixedMoment B raw26122step2 raw26122step2Labels := by
      have ha : raw26122step2 = -raw26122step1 := by apply Matrix.ext; change ∀ i j, raw26122step2 i j = -(raw26122step1 i j); unfold raw26122step2 raw26122step1; decide +kernel
      have hl : raw26122step2Labels = raw26122step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node722 node722Labels := by rfl

def raw26123 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw26123Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw26123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw26123step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26123 raw26123Labels = mixedMoment B node1605 node1605Labels := by
  calc
    mixedMoment B raw26123 raw26123Labels = mixedMoment B raw26123step0 raw26123step0Labels := by
      have hz : ∀ j, raw26123 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26123step0 = (fun i j => raw26123 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26123step0 raw26123; decide +kernel
      have hl : raw26123step0Labels = raw26123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26123 raw26123Labels permutation265 hz
    mixedMoment B raw26123step0 raw26123step0Labels = mixedMoment B raw26123step1 raw26123step1Labels := by
      have ha : raw26123step1 = (fun i j => raw26123step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26123step1 raw26123step0; decide +kernel
      have hl : raw26123step1Labels = raw26123step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26123step0 raw26123step0Labels permutation34 permutation4
    mixedMoment B raw26123step1 raw26123step1Labels = mixedMoment B raw26123step2 raw26123step2Labels := by
      have ha : raw26123step2 = -raw26123step1 := by apply Matrix.ext; change ∀ i j, raw26123step2 i j = -(raw26123step1 i j); unfold raw26123step2 raw26123step1; decide +kernel
      have hl : raw26123step2Labels = raw26123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1605 node1605Labels := by rfl

def raw26124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26124Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26124step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26124 raw26124Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw26124 raw26124Labels = mixedMoment B raw26124step0 raw26124step0Labels := by
      have hz : ∀ j, raw26124 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26124step0 = (fun i j => raw26124 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26124step0 raw26124; decide +kernel
      have hl : raw26124step0Labels = raw26124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26124 raw26124Labels permutation265 hz
    mixedMoment B raw26124step0 raw26124step0Labels = mixedMoment B raw26124step1 raw26124step1Labels := by
      have ha : raw26124step1 = (fun i j => raw26124step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26124step1 raw26124step0; decide +kernel
      have hl : raw26124step1Labels = raw26124step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26124step0 raw26124step0Labels permutation34 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw26125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26125Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26125 raw26125Labels = mixedMoment B node1997 node1997Labels := by
  calc
    mixedMoment B raw26125 raw26125Labels = mixedMoment B raw26125step0 raw26125step0Labels := by
      have ha : raw26125step0 = (fun i j => raw26125 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26125step0 raw26125; decide +kernel
      have hl : raw26125step0Labels = raw26125Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26125 raw26125Labels permutation154 permutation2
    _ = mixedMoment B node1997 node1997Labels := by rfl

def raw26126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26126Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26126step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26126step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26126 raw26126Labels = mixedMoment B node1945 node1945Labels := by
  calc
    mixedMoment B raw26126 raw26126Labels = mixedMoment B raw26126step0 raw26126step0Labels := by
      have hz : ∀ j, raw26126 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26126step0 = (fun i j => raw26126 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26126step0 raw26126; decide +kernel
      have hl : raw26126step0Labels = raw26126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26126 raw26126Labels permutation265 hz
    mixedMoment B raw26126step0 raw26126step0Labels = mixedMoment B raw26126step1 raw26126step1Labels := by
      have ha : raw26126step1 = (fun i j => raw26126step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26126step1 raw26126step0; decide +kernel
      have hl : raw26126step1Labels = raw26126step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26126step0 raw26126step0Labels permutation34 permutation2
    _ = mixedMoment B node1945 node1945Labels := by rfl

def raw26127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26127Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26127 raw26127Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw26127 raw26127Labels = mixedMoment B raw26127step0 raw26127step0Labels := by
      have hz : ∀ j, raw26127 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26127step0 = (fun i j => raw26127 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26127step0 raw26127; decide +kernel
      have hl : raw26127step0Labels = raw26127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26127 raw26127Labels permutation265 hz
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw26128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 0, 0], ![2, 0, -2]]
def raw26128Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw26128step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26128step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw26128step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26128 raw26128Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw26128 raw26128Labels = mixedMoment B raw26128step0 raw26128step0Labels := by
      have hz : ∀ j, raw26128 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26128step0 = (fun i j => raw26128 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26128step0 raw26128; decide +kernel
      have hl : raw26128step0Labels = raw26128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26128 raw26128Labels permutation520 hz
    mixedMoment B raw26128step0 raw26128step0Labels = mixedMoment B raw26128step1 raw26128step1Labels := by
      have hz : ∀ j, raw26128step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26128step1 = (fun i j => raw26128step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26128step1 raw26128step0; decide +kernel
      have hl : raw26128step1Labels = raw26128step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26128step0 raw26128step0Labels permutation56 hz
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw26129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw26129Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 1, -2]]
def raw26129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26129step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26129 raw26129Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw26129 raw26129Labels = mixedMoment B raw26129step0 raw26129step0Labels := by
      have hz : ∀ j, raw26129 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26129step0 = (fun i j => raw26129 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26129step0 raw26129; decide +kernel
      have hl : raw26129step0Labels = raw26129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26129 raw26129Labels permutation265 hz
    mixedMoment B raw26129step0 raw26129step0Labels = mixedMoment B raw26129step1 raw26129step1Labels := by
      have ha : raw26129step1 = (fun i j => raw26129step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26129step1 raw26129step0; decide +kernel
      have hl : raw26129step1Labels = raw26129step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26129step0 raw26129step0Labels permutation34 permutation2
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw26130 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![0, 0], ![2, -2]]
def raw26130Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26130step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw26130step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26130step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw26130step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26130 raw26130Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw26130 raw26130Labels = mixedMoment B raw26130step0 raw26130step0Labels := by
      have hz : ∀ j, raw26130 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26130step0 = (fun i j => raw26130 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26130step0 raw26130; decide +kernel
      have hl : raw26130step0Labels = raw26130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26130 raw26130Labels permutation520 hz
    mixedMoment B raw26130step0 raw26130step0Labels = mixedMoment B raw26130step1 raw26130step1Labels := by
      have hz : ∀ j, raw26130step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26130step1 = (fun i j => raw26130step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26130step1 raw26130step0; decide +kernel
      have hl : raw26130step1Labels = raw26130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26130step0 raw26130step0Labels permutation56 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw26131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26131Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26131 raw26131Labels = mixedMoment B node876 node876Labels := by
  calc
    mixedMoment B raw26131 raw26131Labels = mixedMoment B raw26131step0 raw26131step0Labels := by
      have ha : raw26131step0 = (fun i j => raw26131 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26131step0 raw26131; decide +kernel
      have hl : raw26131step0Labels = raw26131Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26131 raw26131Labels permutation178 permutation2
    _ = mixedMoment B node876 node876Labels := by rfl

def raw26132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26132Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0], ![2, 0, -2]]
def raw26132step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw26132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26132 raw26132Labels = mixedMoment B node883 node883Labels := by
  calc
    mixedMoment B raw26132 raw26132Labels = mixedMoment B raw26132step0 raw26132step0Labels := by
      have hz : ∀ j, raw26132 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26132step0 = (fun i j => raw26132 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26132step0 raw26132; decide +kernel
      have hl : raw26132step0Labels = raw26132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26132 raw26132Labels permutation265 hz
    mixedMoment B raw26132step0 raw26132step0Labels = mixedMoment B raw26132step1 raw26132step1Labels := by
      have ha : raw26132step1 = (fun i j => raw26132step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26132step1 raw26132step0; decide +kernel
      have hl : raw26132step1Labels = raw26132step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26132step0 raw26132step0Labels permutation34 permutation2
    _ = mixedMoment B node883 node883Labels := by rfl

def raw26133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw26133Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw26133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26133 raw26133Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw26133 raw26133Labels = mixedMoment B raw26133step0 raw26133step0Labels := by
      have hz : ∀ j, raw26133 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26133step0 = (fun i j => raw26133 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26133step0 raw26133; decide +kernel
      have hl : raw26133step0Labels = raw26133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26133 raw26133Labels permutation265 hz
    _ = mixedMoment B node891 node891Labels := by rfl

def raw26134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![3, -1, -2]]
def raw26134Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![3, -1, -2]]
def raw26134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw26134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26134 raw26134Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw26134 raw26134Labels = mixedMoment B raw26134step0 raw26134step0Labels := by
      have hz : ∀ j, raw26134 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26134step0 = (fun i j => raw26134 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26134step0 raw26134; decide +kernel
      have hl : raw26134step0Labels = raw26134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26134 raw26134Labels permutation265 hz
    mixedMoment B raw26134step0 raw26134step0Labels = mixedMoment B raw26134step1 raw26134step1Labels := by
      have ha : raw26134step1 = (fun i j => raw26134step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26134step1 raw26134step0; decide +kernel
      have hl : raw26134step1Labels = raw26134step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26134step0 raw26134step0Labels permutation34 permutation2
    _ = mixedMoment B node881 node881Labels := by rfl

def raw26135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26135 raw26135Labels = mixedMoment B node4786 node4786Labels := by
  calc
    _ = mixedMoment B node4786 node4786Labels := by rfl

def raw26136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26136step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26136step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw26136step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26136step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26136 raw26136Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw26136 raw26136Labels = mixedMoment B raw26136step0 raw26136step0Labels := by
      have hz : ∀ j, raw26136 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26136step0 = (fun i j => raw26136 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26136step0 raw26136; decide +kernel
      have hl : raw26136step0Labels = raw26136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26136 raw26136Labels permutation265 hz
    mixedMoment B raw26136step0 raw26136step0Labels = mixedMoment B raw26136step1 raw26136step1Labels := by
      have hz : ∀ i, raw26136step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw26136step1 = (fun i j => raw26136step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw26136step1 raw26136step0; decide +kernel
      have hl : raw26136step1Labels = (fun j => raw26136step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26136step0 raw26136step0Labels permutation4 hz
    mixedMoment B raw26136step1 raw26136step1Labels = mixedMoment B raw26136step2 raw26136step2Labels := by
      have ha : raw26136step2 = raw26136step1 := by apply Matrix.ext; unfold raw26136step2 raw26136step1; decide +kernel
      have hl : raw26136step1Labels = labelEmbedding2 ∘ raw26136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26136step1 raw26136step1Labels raw26136step2Labels labelEmbedding2 hl
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw26137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw26137step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26137step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26137step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26137step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26137step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26137 raw26137Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw26137 raw26137Labels = mixedMoment B raw26137step0 raw26137step0Labels := by
      have hz : ∀ j, raw26137 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26137step0 = (fun i j => raw26137 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26137step0 raw26137; decide +kernel
      have hl : raw26137step0Labels = raw26137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26137 raw26137Labels permutation265 hz
    mixedMoment B raw26137step0 raw26137step0Labels = mixedMoment B raw26137step1 raw26137step1Labels := by
      have ha : raw26137step1 = (fun i j => raw26137step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26137step1 raw26137step0; decide +kernel
      have hl : raw26137step1Labels = raw26137step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26137step0 raw26137step0Labels permutation32 permutation7
    mixedMoment B raw26137step1 raw26137step1Labels = mixedMoment B raw26137step2 raw26137step2Labels := by
      have ha : raw26137step2 = -raw26137step1 := by apply Matrix.ext; change ∀ i j, raw26137step2 i j = -(raw26137step1 i j); unfold raw26137step2 raw26137step1; decide +kernel
      have hl : raw26137step2Labels = raw26137step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26137step2 raw26137step2Labels = mixedMoment B raw26137step3 raw26137step3Labels := by
      have ha : raw26137step3 = raw26137step2 := by apply Matrix.ext; unfold raw26137step3 raw26137step2; decide +kernel
      have hl : raw26137step2Labels = labelEmbedding10 ∘ raw26137step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26137step2 raw26137step2Labels raw26137step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw26138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw26138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw26138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw26138step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26138step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26138step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26138 raw26138Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw26138 raw26138Labels = mixedMoment B raw26138step0 raw26138step0Labels := by
      have hz : ∀ j, raw26138 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26138step0 = (fun i j => raw26138 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26138step0 raw26138; decide +kernel
      have hl : raw26138step0Labels = raw26138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26138 raw26138Labels permutation265 hz
    mixedMoment B raw26138step0 raw26138step0Labels = mixedMoment B raw26138step1 raw26138step1Labels := by
      have ha : raw26138step1 = (fun i j => raw26138step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26138step1 raw26138step0; decide +kernel
      have hl : raw26138step1Labels = raw26138step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26138step0 raw26138step0Labels permutation34 permutation7
    mixedMoment B raw26138step1 raw26138step1Labels = mixedMoment B raw26138step2 raw26138step2Labels := by
      have ha : raw26138step2 = -raw26138step1 := by apply Matrix.ext; change ∀ i j, raw26138step2 i j = -(raw26138step1 i j); unfold raw26138step2 raw26138step1; decide +kernel
      have hl : raw26138step2Labels = raw26138step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26138step2 raw26138step2Labels = mixedMoment B raw26138step3 raw26138step3Labels := by
      have ha : raw26138step3 = raw26138step2 := by apply Matrix.ext; unfold raw26138step3 raw26138step2; decide +kernel
      have hl : raw26138step2Labels = labelEmbedding10 ∘ raw26138step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26138step2 raw26138step2Labels raw26138step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw26139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26139step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26139step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26139step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26139 raw26139Labels = mixedMoment B node4838 node4838Labels := by
  calc
    mixedMoment B raw26139 raw26139Labels = mixedMoment B raw26139step0 raw26139step0Labels := by
      have hz : ∀ j, raw26139 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26139step0 = (fun i j => raw26139 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26139step0 raw26139; decide +kernel
      have hl : raw26139step0Labels = raw26139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26139 raw26139Labels permutation265 hz
    mixedMoment B raw26139step0 raw26139step0Labels = mixedMoment B raw26139step1 raw26139step1Labels := by
      have ha : raw26139step1 = (fun i j => raw26139step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26139step1 raw26139step0; decide +kernel
      have hl : raw26139step1Labels = raw26139step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26139step0 raw26139step0Labels permutation32 permutation7
    mixedMoment B raw26139step1 raw26139step1Labels = mixedMoment B raw26139step2 raw26139step2Labels := by
      have ha : raw26139step2 = -raw26139step1 := by apply Matrix.ext; change ∀ i j, raw26139step2 i j = -(raw26139step1 i j); unfold raw26139step2 raw26139step1; decide +kernel
      have hl : raw26139step2Labels = raw26139step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26139step2 raw26139step2Labels = mixedMoment B raw26139step3 raw26139step3Labels := by
      have ha : raw26139step3 = raw26139step2 := by apply Matrix.ext; unfold raw26139step3 raw26139step2; decide +kernel
      have hl : raw26139step2Labels = labelEmbedding10 ∘ raw26139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26139step2 raw26139step2Labels raw26139step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4838 node4838Labels := by rfl

def raw26140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26140 raw26140Labels = mixedMoment B node4139 node4139Labels := by
  calc
    mixedMoment B raw26140 raw26140Labels = mixedMoment B raw26140step0 raw26140step0Labels := by
      have ha : raw26140step0 = (fun i j => raw26140 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26140step0 raw26140; decide +kernel
      have hl : raw26140step0Labels = raw26140Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26140 raw26140Labels permutation176 permutation2
    _ = mixedMoment B node4139 node4139Labels := by rfl

def raw26141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26141step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26141 raw26141Labels = mixedMoment B node4300 node4300Labels := by
  calc
    mixedMoment B raw26141 raw26141Labels = mixedMoment B raw26141step0 raw26141step0Labels := by
      have ha : raw26141step0 = (fun i j => raw26141 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26141step0 raw26141; decide +kernel
      have hl : raw26141step0Labels = raw26141Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26141 raw26141Labels permutation176 permutation2
    _ = mixedMoment B node4300 node4300Labels := by rfl

def raw26142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26142 raw26142Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw26142 raw26142Labels = mixedMoment B raw26142step0 raw26142step0Labels := by
      have ha : raw26142step0 = (fun i j => raw26142 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26142step0 raw26142; decide +kernel
      have hl : raw26142step0Labels = raw26142Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26142 raw26142Labels permutation182 permutation2
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw26143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw26143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26143 raw26143Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw26143 raw26143Labels = mixedMoment B raw26143step0 raw26143step0Labels := by
      have ha : raw26143step0 = (fun i j => raw26143 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26143step0 raw26143; decide +kernel
      have hl : raw26143step0Labels = raw26143Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26143 raw26143Labels permutation188 permutation2
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw26144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26144 raw26144Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw26144 raw26144Labels = mixedMoment B raw26144step0 raw26144step0Labels := by
      have ha : raw26144step0 = (fun i j => raw26144 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26144step0 raw26144; decide +kernel
      have hl : raw26144step0Labels = raw26144Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26144 raw26144Labels permutation176 permutation2
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw26145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26145 raw26145Labels = mixedMoment B node4165 node4165Labels := by
  calc
    mixedMoment B raw26145 raw26145Labels = mixedMoment B raw26145step0 raw26145step0Labels := by
      have hz : ∀ j, raw26145 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26145step0 = (fun i j => raw26145 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26145step0 raw26145; decide +kernel
      have hl : raw26145step0Labels = raw26145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26145 raw26145Labels permutation265 hz
    _ = mixedMoment B node4165 node4165Labels := by rfl

def raw26146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26146 raw26146Labels = mixedMoment B node4337 node4337Labels := by
  calc
    _ = mixedMoment B node4337 node4337Labels := by rfl

def raw26147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26147 raw26147Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw26147 raw26147Labels = mixedMoment B raw26147step0 raw26147step0Labels := by
      have hz : ∀ j, raw26147 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26147step0 = (fun i j => raw26147 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26147step0 raw26147; decide +kernel
      have hl : raw26147step0Labels = raw26147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26147 raw26147Labels permutation265 hz
    mixedMoment B raw26147step0 raw26147step0Labels = mixedMoment B raw26147step1 raw26147step1Labels := by
      have ha : raw26147step1 = (fun i j => raw26147step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26147step1 raw26147step0; decide +kernel
      have hl : raw26147step1Labels = raw26147step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26147step0 raw26147step0Labels permutation38 permutation2
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw26148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw26148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw26148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26148 raw26148Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw26148 raw26148Labels = mixedMoment B raw26148step0 raw26148step0Labels := by
      have hz : ∀ j, raw26148 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26148step0 = (fun i j => raw26148 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26148step0 raw26148; decide +kernel
      have hl : raw26148step0Labels = raw26148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26148 raw26148Labels permutation265 hz
    mixedMoment B raw26148step0 raw26148step0Labels = mixedMoment B raw26148step1 raw26148step1Labels := by
      have ha : raw26148step1 = (fun i j => raw26148step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26148step1 raw26148step0; decide +kernel
      have hl : raw26148step1Labels = raw26148step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26148step0 raw26148step0Labels permutation44 permutation2
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw26149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26149 raw26149Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw26149 raw26149Labels = mixedMoment B raw26149step0 raw26149step0Labels := by
      have hz : ∀ j, raw26149 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26149step0 = (fun i j => raw26149 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26149step0 raw26149; decide +kernel
      have hl : raw26149step0Labels = raw26149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26149 raw26149Labels permutation265 hz
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw26150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26150 raw26150Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw26150 raw26150Labels = mixedMoment B raw26150step0 raw26150step0Labels := by
      have hz : ∀ j, raw26150 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26150step0 = (fun i j => raw26150 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26150step0 raw26150; decide +kernel
      have hl : raw26150step0Labels = raw26150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26150 raw26150Labels permutation265 hz
    mixedMoment B raw26150step0 raw26150step0Labels = mixedMoment B raw26150step1 raw26150step1Labels := by
      have ha : raw26150step1 = (fun i j => raw26150step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26150step1 raw26150step0; decide +kernel
      have hl : raw26150step1Labels = raw26150step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26150step0 raw26150step0Labels permutation34 permutation2
    _ = mixedMoment B node4145 node4145Labels := by rfl

def raw26151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26151 raw26151Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw26151 raw26151Labels = mixedMoment B raw26151step0 raw26151step0Labels := by
      have ha : raw26151step0 = (fun i j => raw26151 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26151step0 raw26151; decide +kernel
      have hl : raw26151step0Labels = raw26151Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26151 raw26151Labels permutation154 permutation2
    _ = mixedMoment B node4323 node4323Labels := by rfl

def raw26152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26152 raw26152Labels = mixedMoment B node4311 node4311Labels := by
  calc
    mixedMoment B raw26152 raw26152Labels = mixedMoment B raw26152step0 raw26152step0Labels := by
      have hz : ∀ j, raw26152 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26152step0 = (fun i j => raw26152 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26152step0 raw26152; decide +kernel
      have hl : raw26152step0Labels = raw26152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26152 raw26152Labels permutation265 hz
    mixedMoment B raw26152step0 raw26152step0Labels = mixedMoment B raw26152step1 raw26152step1Labels := by
      have ha : raw26152step1 = (fun i j => raw26152step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26152step1 raw26152step0; decide +kernel
      have hl : raw26152step1Labels = raw26152step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26152step0 raw26152step0Labels permutation34 permutation2
    _ = mixedMoment B node4311 node4311Labels := by rfl

def raw26153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw26153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw26153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26153 raw26153Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw26153 raw26153Labels = mixedMoment B raw26153step0 raw26153step0Labels := by
      have hz : ∀ j, raw26153 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26153step0 = (fun i j => raw26153 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26153step0 raw26153; decide +kernel
      have hl : raw26153step0Labels = raw26153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26153 raw26153Labels permutation265 hz
    mixedMoment B raw26153step0 raw26153step0Labels = mixedMoment B raw26153step1 raw26153step1Labels := by
      have ha : raw26153step1 = (fun i j => raw26153step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26153step1 raw26153step0; decide +kernel
      have hl : raw26153step1Labels = raw26153step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26153step0 raw26153step0Labels permutation34 permutation2
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw26154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26154step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26154 raw26154Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw26154 raw26154Labels = mixedMoment B raw26154step0 raw26154step0Labels := by
      have hz : ∀ j, raw26154 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26154step0 = (fun i j => raw26154 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26154step0 raw26154; decide +kernel
      have hl : raw26154step0Labels = raw26154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26154 raw26154Labels permutation265 hz
    mixedMoment B raw26154step0 raw26154step0Labels = mixedMoment B raw26154step1 raw26154step1Labels := by
      have ha : raw26154step1 = (fun i j => raw26154step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26154step1 raw26154step0; decide +kernel
      have hl : raw26154step1Labels = raw26154step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26154step0 raw26154step0Labels permutation35 permutation2
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw26155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26155 raw26155Labels = mixedMoment B node4145 node4145Labels := by
  calc
    mixedMoment B raw26155 raw26155Labels = mixedMoment B raw26155step0 raw26155step0Labels := by
      have hz : ∀ j, raw26155 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26155step0 = (fun i j => raw26155 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26155step0 raw26155; decide +kernel
      have hl : raw26155step0Labels = raw26155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26155 raw26155Labels permutation265 hz
    _ = mixedMoment B node4145 node4145Labels := by rfl

def raw26156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26156 raw26156Labels = mixedMoment B node4323 node4323Labels := by
  calc
    _ = mixedMoment B node4323 node4323Labels := by rfl

def raw26157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26157 raw26157Labels = mixedMoment B node4311 node4311Labels := by
  calc
    mixedMoment B raw26157 raw26157Labels = mixedMoment B raw26157step0 raw26157step0Labels := by
      have hz : ∀ j, raw26157 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26157step0 = (fun i j => raw26157 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26157step0 raw26157; decide +kernel
      have hl : raw26157step0Labels = raw26157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26157 raw26157Labels permutation265 hz
    _ = mixedMoment B node4311 node4311Labels := by rfl

def raw26158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26158 raw26158Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw26158 raw26158Labels = mixedMoment B raw26158step0 raw26158step0Labels := by
      have hz : ∀ j, raw26158 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26158step0 = (fun i j => raw26158 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26158step0 raw26158; decide +kernel
      have hl : raw26158step0Labels = raw26158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26158 raw26158Labels permutation265 hz
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw26159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 1, -2]]
def raw26159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 1, -2]]
def raw26159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26159 raw26159Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw26159 raw26159Labels = mixedMoment B raw26159step0 raw26159step0Labels := by
      have hz : ∀ j, raw26159 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26159step0 = (fun i j => raw26159 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26159step0 raw26159; decide +kernel
      have hl : raw26159step0Labels = raw26159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26159 raw26159Labels permutation265 hz
    mixedMoment B raw26159step0 raw26159step0Labels = mixedMoment B raw26159step1 raw26159step1Labels := by
      have ha : raw26159step1 = (fun i j => raw26159step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26159step1 raw26159step0; decide +kernel
      have hl : raw26159step1Labels = raw26159step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26159step0 raw26159step0Labels permutation33 permutation2
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw26160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26160 raw26160Labels = mixedMoment B node4144 node4144Labels := by
  calc
    mixedMoment B raw26160 raw26160Labels = mixedMoment B raw26160step0 raw26160step0Labels := by
      have hz : ∀ j, raw26160 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26160step0 = (fun i j => raw26160 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26160step0 raw26160; decide +kernel
      have hl : raw26160step0Labels = raw26160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26160 raw26160Labels permutation265 hz
    _ = mixedMoment B node4144 node4144Labels := by rfl

def raw26161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26161 raw26161Labels = mixedMoment B node4322 node4322Labels := by
  calc
    _ = mixedMoment B node4322 node4322Labels := by rfl

def raw26162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26162 raw26162Labels = mixedMoment B node4308 node4308Labels := by
  calc
    mixedMoment B raw26162 raw26162Labels = mixedMoment B raw26162step0 raw26162step0Labels := by
      have hz : ∀ j, raw26162 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26162step0 = (fun i j => raw26162 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26162step0 raw26162; decide +kernel
      have hl : raw26162step0Labels = raw26162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26162 raw26162Labels permutation265 hz
    _ = mixedMoment B node4308 node4308Labels := by rfl

def raw26163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26163 raw26163Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw26163 raw26163Labels = mixedMoment B raw26163step0 raw26163step0Labels := by
      have hz : ∀ j, raw26163 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26163step0 = (fun i j => raw26163 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26163step0 raw26163; decide +kernel
      have hl : raw26163step0Labels = raw26163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26163 raw26163Labels permutation265 hz
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw26164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw26164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw26164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26164 raw26164Labels = mixedMoment B node4401 node4401Labels := by
  calc
    mixedMoment B raw26164 raw26164Labels = mixedMoment B raw26164step0 raw26164step0Labels := by
      have hz : ∀ j, raw26164 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26164step0 = (fun i j => raw26164 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26164step0 raw26164; decide +kernel
      have hl : raw26164step0Labels = raw26164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26164 raw26164Labels permutation265 hz
    mixedMoment B raw26164step0 raw26164step0Labels = mixedMoment B raw26164step1 raw26164step1Labels := by
      have ha : raw26164step1 = (fun i j => raw26164step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26164step1 raw26164step0; decide +kernel
      have hl : raw26164step1Labels = raw26164step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26164step0 raw26164step0Labels permutation34 permutation2
    _ = mixedMoment B node4401 node4401Labels := by rfl

def raw26165 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw26165step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26165step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26165step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26165 raw26165Labels = mixedMoment B node4209 node4209Labels := by
  calc
    mixedMoment B raw26165 raw26165Labels = mixedMoment B raw26165step0 raw26165step0Labels := by
      have ha : raw26165step0 = (fun i j => raw26165 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26165step0 raw26165; decide +kernel
      have hl : raw26165step0Labels = raw26165Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26165 raw26165Labels permutation176 permutation4
    mixedMoment B raw26165step0 raw26165step0Labels = mixedMoment B raw26165step1 raw26165step1Labels := by
      have ha : raw26165step1 = -raw26165step0 := by apply Matrix.ext; change ∀ i j, raw26165step1 i j = -(raw26165step0 i j); unfold raw26165step1 raw26165step0; decide +kernel
      have hl : raw26165step1Labels = raw26165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26165step1 raw26165step1Labels = mixedMoment B raw26165step2 raw26165step2Labels := by
      have ha : raw26165step2 = raw26165step1 := by apply Matrix.ext; unfold raw26165step2 raw26165step1; decide +kernel
      have hl : raw26165step1Labels = labelEmbedding7 ∘ raw26165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26165step1 raw26165step1Labels raw26165step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4209 node4209Labels := by rfl

def raw26166 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26166Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26166step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26166step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26166 raw26166Labels = mixedMoment B node4376 node4376Labels := by
  calc
    mixedMoment B raw26166 raw26166Labels = mixedMoment B raw26166step0 raw26166step0Labels := by
      have ha : raw26166step0 = (fun i j => raw26166 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26166step0 raw26166; decide +kernel
      have hl : raw26166step0Labels = raw26166Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26166 raw26166Labels permutation176 permutation6
    mixedMoment B raw26166step0 raw26166step0Labels = mixedMoment B raw26166step1 raw26166step1Labels := by
      have ha : raw26166step1 = raw26166step0 := by apply Matrix.ext; unfold raw26166step1 raw26166step0; decide +kernel
      have hl : raw26166step0Labels = labelEmbedding9 ∘ raw26166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26166step0 raw26166step0Labels raw26166step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4376 node4376Labels := by rfl

def raw26167 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26167Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26167step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26167step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26167step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26167step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw26167step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw26167step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26167step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw26167step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26167step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26167 raw26167Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw26167 raw26167Labels = mixedMoment B raw26167step0 raw26167step0Labels := by
      have hz : ∀ j, raw26167 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26167step0 = (fun i j => raw26167 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26167step0 raw26167; decide +kernel
      have hl : raw26167step0Labels = raw26167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26167 raw26167Labels permutation346 hz
    mixedMoment B raw26167step0 raw26167step0Labels = mixedMoment B raw26167step1 raw26167step1Labels := by
      have hz : ∀ j, raw26167step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26167step1 = (fun i j => raw26167step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26167step1 raw26167step0; decide +kernel
      have hl : raw26167step1Labels = raw26167step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26167step0 raw26167step0Labels permutation56 hz
    mixedMoment B raw26167step1 raw26167step1Labels = mixedMoment B raw26167step2 raw26167step2Labels := by
      have hz : ∀ i, raw26167step1 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw26167step2 = (fun i j => raw26167step1 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw26167step2 raw26167step1; decide +kernel
      have hl : raw26167step2Labels = (fun j => raw26167step1Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26167step1 raw26167step1Labels permutation2 hz
    mixedMoment B raw26167step2 raw26167step2Labels = mixedMoment B raw26167step3 raw26167step3Labels := by
      have ha : raw26167step3 = -raw26167step2 := by apply Matrix.ext; change ∀ i j, raw26167step3 i j = -(raw26167step2 i j); unfold raw26167step3 raw26167step2; decide +kernel
      have hl : raw26167step3Labels = raw26167step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26167step3 raw26167step3Labels = mixedMoment B raw26167step4 raw26167step4Labels := by
      have ha : raw26167step4 = raw26167step3 := by apply Matrix.ext; unfold raw26167step4 raw26167step3; decide +kernel
      have hl : raw26167step3Labels = labelEmbedding3 ∘ raw26167step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26167step3 raw26167step3Labels raw26167step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw26168 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26168Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26168step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26168step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26168step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26168 raw26168Labels = mixedMoment B node4423 node4423Labels := by
  calc
    mixedMoment B raw26168 raw26168Labels = mixedMoment B raw26168step0 raw26168step0Labels := by
      have hz : ∀ j, raw26168 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26168step0 = (fun i j => raw26168 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26168step0 raw26168; decide +kernel
      have hl : raw26168step0Labels = raw26168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26168 raw26168Labels permutation346 hz
    mixedMoment B raw26168step0 raw26168step0Labels = mixedMoment B raw26168step1 raw26168step1Labels := by
      have ha : raw26168step1 = (fun i j => raw26168step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26168step1 raw26168step0; decide +kernel
      have hl : raw26168step1Labels = raw26168step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26168step0 raw26168step0Labels permutation32 permutation6
    mixedMoment B raw26168step1 raw26168step1Labels = mixedMoment B raw26168step2 raw26168step2Labels := by
      have ha : raw26168step2 = raw26168step1 := by apply Matrix.ext; unfold raw26168step2 raw26168step1; decide +kernel
      have hl : raw26168step1Labels = labelEmbedding9 ∘ raw26168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26168step1 raw26168step1Labels raw26168step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4423 node4423Labels := by rfl

def raw26169 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26169Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26169step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw26169step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26169step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26169step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26169 raw26169Labels = mixedMoment B node4221 node4221Labels := by
  calc
    mixedMoment B raw26169 raw26169Labels = mixedMoment B raw26169step0 raw26169step0Labels := by
      have hz : ∀ j, raw26169 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26169step0 = (fun i j => raw26169 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26169step0 raw26169; decide +kernel
      have hl : raw26169step0Labels = raw26169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26169 raw26169Labels permutation265 hz
    mixedMoment B raw26169step0 raw26169step0Labels = mixedMoment B raw26169step1 raw26169step1Labels := by
      have ha : raw26169step1 = (fun i j => raw26169step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26169step1 raw26169step0; decide +kernel
      have hl : raw26169step1Labels = raw26169step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26169step0 raw26169step0Labels permutation34 permutation4
    mixedMoment B raw26169step1 raw26169step1Labels = mixedMoment B raw26169step2 raw26169step2Labels := by
      have ha : raw26169step2 = -raw26169step1 := by apply Matrix.ext; change ∀ i j, raw26169step2 i j = -(raw26169step1 i j); unfold raw26169step2 raw26169step1; decide +kernel
      have hl : raw26169step2Labels = raw26169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26169step2 raw26169step2Labels = mixedMoment B raw26169step3 raw26169step3Labels := by
      have ha : raw26169step3 = raw26169step2 := by apply Matrix.ext; unfold raw26169step3 raw26169step2; decide +kernel
      have hl : raw26169step2Labels = labelEmbedding7 ∘ raw26169step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26169step2 raw26169step2Labels raw26169step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4221 node4221Labels := by rfl

def raw26170 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26170Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw26170step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw26170step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26170 raw26170Labels = mixedMoment B node4387 node4387Labels := by
  calc
    mixedMoment B raw26170 raw26170Labels = mixedMoment B raw26170step0 raw26170step0Labels := by
      have ha : raw26170step0 = (fun i j => raw26170 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26170step0 raw26170; decide +kernel
      have hl : raw26170step0Labels = raw26170Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26170 raw26170Labels permutation154 permutation6
    mixedMoment B raw26170step0 raw26170step0Labels = mixedMoment B raw26170step1 raw26170step1Labels := by
      have ha : raw26170step1 = raw26170step0 := by apply Matrix.ext; unfold raw26170step1 raw26170step0; decide +kernel
      have hl : raw26170step0Labels = labelEmbedding9 ∘ raw26170step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26170step0 raw26170step0Labels raw26170step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4387 node4387Labels := by rfl

def raw26171 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26171Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26171step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw26171step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw26171step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26171 raw26171Labels = mixedMoment B node4381 node4381Labels := by
  calc
    mixedMoment B raw26171 raw26171Labels = mixedMoment B raw26171step0 raw26171step0Labels := by
      have hz : ∀ j, raw26171 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26171step0 = (fun i j => raw26171 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26171step0 raw26171; decide +kernel
      have hl : raw26171step0Labels = raw26171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26171 raw26171Labels permutation265 hz
    mixedMoment B raw26171step0 raw26171step0Labels = mixedMoment B raw26171step1 raw26171step1Labels := by
      have ha : raw26171step1 = (fun i j => raw26171step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26171step1 raw26171step0; decide +kernel
      have hl : raw26171step1Labels = raw26171step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26171step0 raw26171step0Labels permutation34 permutation6
    mixedMoment B raw26171step1 raw26171step1Labels = mixedMoment B raw26171step2 raw26171step2Labels := by
      have ha : raw26171step2 = raw26171step1 := by apply Matrix.ext; unfold raw26171step2 raw26171step1; decide +kernel
      have hl : raw26171step1Labels = labelEmbedding9 ∘ raw26171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26171step1 raw26171step1Labels raw26171step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4381 node4381Labels := by rfl

def raw26172 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw26172Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw26172step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw26172step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26172step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26172step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26172step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26172 raw26172Labels = mixedMoment B node4221 node4221Labels := by
  calc
    mixedMoment B raw26172 raw26172Labels = mixedMoment B raw26172step0 raw26172step0Labels := by
      have hz : ∀ j, raw26172 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26172step0 = (fun i j => raw26172 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26172step0 raw26172; decide +kernel
      have hl : raw26172step0Labels = raw26172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26172 raw26172Labels permutation265 hz
    mixedMoment B raw26172step0 raw26172step0Labels = mixedMoment B raw26172step1 raw26172step1Labels := by
      have ha : raw26172step1 = (fun i j => raw26172step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26172step1 raw26172step0; decide +kernel
      have hl : raw26172step1Labels = raw26172step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26172step0 raw26172step0Labels permutation32 permutation4
    mixedMoment B raw26172step1 raw26172step1Labels = mixedMoment B raw26172step2 raw26172step2Labels := by
      have ha : raw26172step2 = -raw26172step1 := by apply Matrix.ext; change ∀ i j, raw26172step2 i j = -(raw26172step1 i j); unfold raw26172step2 raw26172step1; decide +kernel
      have hl : raw26172step2Labels = raw26172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26172step2 raw26172step2Labels = mixedMoment B raw26172step3 raw26172step3Labels := by
      have ha : raw26172step3 = raw26172step2 := by apply Matrix.ext; unfold raw26172step3 raw26172step2; decide +kernel
      have hl : raw26172step2Labels = labelEmbedding7 ∘ raw26172step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26172step2 raw26172step2Labels raw26172step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4221 node4221Labels := by rfl

def raw26173 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw26173Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw26173step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw26173step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26173 raw26173Labels = mixedMoment B node4387 node4387Labels := by
  calc
    mixedMoment B raw26173 raw26173Labels = mixedMoment B raw26173step0 raw26173step0Labels := by
      have ha : raw26173step0 = (fun i j => raw26173 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26173step0 raw26173; decide +kernel
      have hl : raw26173step0Labels = raw26173Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26173 raw26173Labels permutation152 permutation6
    mixedMoment B raw26173step0 raw26173step0Labels = mixedMoment B raw26173step1 raw26173step1Labels := by
      have ha : raw26173step1 = raw26173step0 := by apply Matrix.ext; unfold raw26173step1 raw26173step0; decide +kernel
      have hl : raw26173step0Labels = labelEmbedding9 ∘ raw26173step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26173step0 raw26173step0Labels raw26173step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4387 node4387Labels := by rfl

def raw26174 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw26174Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw26174step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw26174step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw26174step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26174 raw26174Labels = mixedMoment B node4381 node4381Labels := by
  calc
    mixedMoment B raw26174 raw26174Labels = mixedMoment B raw26174step0 raw26174step0Labels := by
      have hz : ∀ j, raw26174 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26174step0 = (fun i j => raw26174 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26174step0 raw26174; decide +kernel
      have hl : raw26174step0Labels = raw26174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26174 raw26174Labels permutation265 hz
    mixedMoment B raw26174step0 raw26174step0Labels = mixedMoment B raw26174step1 raw26174step1Labels := by
      have ha : raw26174step1 = (fun i j => raw26174step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26174step1 raw26174step0; decide +kernel
      have hl : raw26174step1Labels = raw26174step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26174step0 raw26174step0Labels permutation32 permutation6
    mixedMoment B raw26174step1 raw26174step1Labels = mixedMoment B raw26174step2 raw26174step2Labels := by
      have ha : raw26174step2 = raw26174step1 := by apply Matrix.ext; unfold raw26174step2 raw26174step1; decide +kernel
      have hl : raw26174step1Labels = labelEmbedding9 ∘ raw26174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26174step1 raw26174step1Labels raw26174step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4381 node4381Labels := by rfl

def raw26175 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw26175Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw26175step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26175step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw26175step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26175 raw26175Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw26175 raw26175Labels = mixedMoment B raw26175step0 raw26175step0Labels := by
      have hz : ∀ j, raw26175 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26175step0 = (fun i j => raw26175 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26175step0 raw26175; decide +kernel
      have hl : raw26175step0Labels = raw26175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26175 raw26175Labels permutation265 hz
    mixedMoment B raw26175step0 raw26175step0Labels = mixedMoment B raw26175step1 raw26175step1Labels := by
      have ha : raw26175step1 = (fun i j => raw26175step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26175step1 raw26175step0; decide +kernel
      have hl : raw26175step1Labels = raw26175step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26175step0 raw26175step0Labels permutation32 permutation6
    mixedMoment B raw26175step1 raw26175step1Labels = mixedMoment B raw26175step2 raw26175step2Labels := by
      have ha : raw26175step2 = raw26175step1 := by apply Matrix.ext; unfold raw26175step2 raw26175step1; decide +kernel
      have hl : raw26175step1Labels = labelEmbedding9 ∘ raw26175step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26175step1 raw26175step1Labels raw26175step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw26176 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26176Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26176step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw26176step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26176step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26176step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26176 raw26176Labels = mixedMoment B node4218 node4218Labels := by
  calc
    mixedMoment B raw26176 raw26176Labels = mixedMoment B raw26176step0 raw26176step0Labels := by
      have hz : ∀ j, raw26176 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26176step0 = (fun i j => raw26176 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26176step0 raw26176; decide +kernel
      have hl : raw26176step0Labels = raw26176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26176 raw26176Labels permutation265 hz
    mixedMoment B raw26176step0 raw26176step0Labels = mixedMoment B raw26176step1 raw26176step1Labels := by
      have ha : raw26176step1 = (fun i j => raw26176step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26176step1 raw26176step0; decide +kernel
      have hl : raw26176step1Labels = raw26176step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26176step0 raw26176step0Labels permutation32 permutation4
    mixedMoment B raw26176step1 raw26176step1Labels = mixedMoment B raw26176step2 raw26176step2Labels := by
      have ha : raw26176step2 = -raw26176step1 := by apply Matrix.ext; change ∀ i j, raw26176step2 i j = -(raw26176step1 i j); unfold raw26176step2 raw26176step1; decide +kernel
      have hl : raw26176step2Labels = raw26176step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26176step2 raw26176step2Labels = mixedMoment B raw26176step3 raw26176step3Labels := by
      have ha : raw26176step3 = raw26176step2 := by apply Matrix.ext; unfold raw26176step3 raw26176step2; decide +kernel
      have hl : raw26176step2Labels = labelEmbedding7 ∘ raw26176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26176step2 raw26176step2Labels raw26176step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4218 node4218Labels := by rfl

def raw26177 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26177Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw26177step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw26177step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26177 raw26177Labels = mixedMoment B node4386 node4386Labels := by
  calc
    mixedMoment B raw26177 raw26177Labels = mixedMoment B raw26177step0 raw26177step0Labels := by
      have ha : raw26177step0 = (fun i j => raw26177 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26177step0 raw26177; decide +kernel
      have hl : raw26177step0Labels = raw26177Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26177 raw26177Labels permutation152 permutation6
    mixedMoment B raw26177step0 raw26177step0Labels = mixedMoment B raw26177step1 raw26177step1Labels := by
      have ha : raw26177step1 = raw26177step0 := by apply Matrix.ext; unfold raw26177step1 raw26177step0; decide +kernel
      have hl : raw26177step0Labels = labelEmbedding9 ∘ raw26177step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26177step0 raw26177step0Labels raw26177step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4386 node4386Labels := by rfl

def raw26178 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26178Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw26178step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw26178step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw26178step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26178 raw26178Labels = mixedMoment B node4380 node4380Labels := by
  calc
    mixedMoment B raw26178 raw26178Labels = mixedMoment B raw26178step0 raw26178step0Labels := by
      have hz : ∀ j, raw26178 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26178step0 = (fun i j => raw26178 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26178step0 raw26178; decide +kernel
      have hl : raw26178step0Labels = raw26178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26178 raw26178Labels permutation265 hz
    mixedMoment B raw26178step0 raw26178step0Labels = mixedMoment B raw26178step1 raw26178step1Labels := by
      have ha : raw26178step1 = (fun i j => raw26178step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26178step1 raw26178step0; decide +kernel
      have hl : raw26178step1Labels = raw26178step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26178step0 raw26178step0Labels permutation32 permutation6
    mixedMoment B raw26178step1 raw26178step1Labels = mixedMoment B raw26178step2 raw26178step2Labels := by
      have ha : raw26178step2 = raw26178step1 := by apply Matrix.ext; unfold raw26178step2 raw26178step1; decide +kernel
      have hl : raw26178step1Labels = labelEmbedding9 ∘ raw26178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26178step1 raw26178step1Labels raw26178step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4380 node4380Labels := by rfl

def raw26179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26179Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26179 raw26179Labels = mixedMoment B node999 node999Labels := by
  calc
    mixedMoment B raw26179 raw26179Labels = mixedMoment B raw26179step0 raw26179step0Labels := by
      have hz : ∀ j, raw26179 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26179step0 = (fun i j => raw26179 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26179step0 raw26179; decide +kernel
      have hl : raw26179step0Labels = raw26179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26179 raw26179Labels permutation265 hz
    mixedMoment B raw26179step0 raw26179step0Labels = mixedMoment B raw26179step1 raw26179step1Labels := by
      have ha : raw26179step1 = (fun i j => raw26179step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26179step1 raw26179step0; decide +kernel
      have hl : raw26179step1Labels = raw26179step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26179step0 raw26179step0Labels permutation34 permutation2
    _ = mixedMoment B node999 node999Labels := by rfl

def raw26180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26180Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26180step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26180 raw26180Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw26180 raw26180Labels = mixedMoment B raw26180step0 raw26180step0Labels := by
      have ha : raw26180step0 = (fun i j => raw26180 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26180step0 raw26180; decide +kernel
      have hl : raw26180step0Labels = raw26180Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26180 raw26180Labels permutation154 permutation2
    _ = mixedMoment B node1996 node1996Labels := by rfl

def raw26181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26181Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26181step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw26181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26181 raw26181Labels = mixedMoment B node1944 node1944Labels := by
  calc
    mixedMoment B raw26181 raw26181Labels = mixedMoment B raw26181step0 raw26181step0Labels := by
      have hz : ∀ j, raw26181 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26181step0 = (fun i j => raw26181 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26181step0 raw26181; decide +kernel
      have hl : raw26181step0Labels = raw26181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26181 raw26181Labels permutation265 hz
    mixedMoment B raw26181step0 raw26181step0Labels = mixedMoment B raw26181step1 raw26181step1Labels := by
      have ha : raw26181step1 = (fun i j => raw26181step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26181step1 raw26181step0; decide +kernel
      have hl : raw26181step1Labels = raw26181step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26181step0 raw26181step0Labels permutation34 permutation2
    _ = mixedMoment B node1944 node1944Labels := by rfl

def raw26182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26182Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw26182step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26182 raw26182Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw26182 raw26182Labels = mixedMoment B raw26182step0 raw26182step0Labels := by
      have hz : ∀ j, raw26182 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26182step0 = (fun i j => raw26182 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26182step0 raw26182; decide +kernel
      have hl : raw26182step0Labels = raw26182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26182 raw26182Labels permutation265 hz
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw26183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 1, -3]]
def raw26183Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw26183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw26183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26183 raw26183Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw26183 raw26183Labels = mixedMoment B raw26183step0 raw26183step0Labels := by
      have hz : ∀ j, raw26183 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26183step0 = (fun i j => raw26183 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26183step0 raw26183; decide +kernel
      have hl : raw26183step0Labels = raw26183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26183 raw26183Labels permutation520 hz
    mixedMoment B raw26183step0 raw26183step0Labels = mixedMoment B raw26183step1 raw26183step1Labels := by
      have hz : ∀ j, raw26183step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26183step1 = (fun i j => raw26183step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26183step1 raw26183step0; decide +kernel
      have hl : raw26183step1Labels = raw26183step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26183step0 raw26183step0Labels permutation56 hz
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw26184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw26184Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 2, -3]]
def raw26184step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26184 raw26184Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw26184 raw26184Labels = mixedMoment B raw26184step0 raw26184step0Labels := by
      have hz : ∀ j, raw26184 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26184step0 = (fun i j => raw26184 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26184step0 raw26184; decide +kernel
      have hl : raw26184step0Labels = raw26184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26184 raw26184Labels permutation265 hz
    mixedMoment B raw26184step0 raw26184step0Labels = mixedMoment B raw26184step1 raw26184step1Labels := by
      have ha : raw26184step1 = (fun i j => raw26184step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26184step1 raw26184step0; decide +kernel
      have hl : raw26184step1Labels = raw26184step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26184step0 raw26184step0Labels permutation34 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw26185 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![0, 0], ![3, -3]]
def raw26185Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26185step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![3, -3]]
def raw26185step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26185step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw26185step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26185 raw26185Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw26185 raw26185Labels = mixedMoment B raw26185step0 raw26185step0Labels := by
      have hz : ∀ j, raw26185 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26185step0 = (fun i j => raw26185 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26185step0 raw26185; decide +kernel
      have hl : raw26185step0Labels = raw26185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26185 raw26185Labels permutation520 hz
    mixedMoment B raw26185step0 raw26185step0Labels = mixedMoment B raw26185step1 raw26185step1Labels := by
      have hz : ∀ j, raw26185step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26185step1 = (fun i j => raw26185step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26185step1 raw26185step0; decide +kernel
      have hl : raw26185step1Labels = raw26185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26185step0 raw26185step0Labels permutation56 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw26186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26186Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26186step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26186 raw26186Labels = mixedMoment B node557 node557Labels := by
  calc
    mixedMoment B raw26186 raw26186Labels = mixedMoment B raw26186step0 raw26186step0Labels := by
      have hz : ∀ j, raw26186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26186step0 = (fun i j => raw26186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26186step0 raw26186; decide +kernel
      have hl : raw26186step0Labels = raw26186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26186 raw26186Labels permutation346 hz
    mixedMoment B raw26186step0 raw26186step0Labels = mixedMoment B raw26186step1 raw26186step1Labels := by
      have ha : raw26186step1 = (fun i j => raw26186step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26186step1 raw26186step0; decide +kernel
      have hl : raw26186step1Labels = raw26186step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26186step0 raw26186step0Labels permutation40 permutation2
    _ = mixedMoment B node557 node557Labels := by rfl

def raw26187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26187Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26187step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26187 raw26187Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw26187 raw26187Labels = mixedMoment B raw26187step0 raw26187step0Labels := by
      have hz : ∀ j, raw26187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26187step0 = (fun i j => raw26187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26187step0 raw26187; decide +kernel
      have hl : raw26187step0Labels = raw26187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26187 raw26187Labels permutation346 hz
    _ = mixedMoment B node827 node827Labels := by rfl

def raw26188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26188Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26188step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26188 raw26188Labels = mixedMoment B node719 node719Labels := by
  calc
    mixedMoment B raw26188 raw26188Labels = mixedMoment B raw26188step0 raw26188step0Labels := by
      have ha : raw26188step0 = (fun i j => raw26188 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26188step0 raw26188; decide +kernel
      have hl : raw26188step0Labels = raw26188Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26188 raw26188Labels permutation184 permutation2
    _ = mixedMoment B node719 node719Labels := by rfl

def raw26189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26189Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26189step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26189step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26189 raw26189Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw26189 raw26189Labels = mixedMoment B raw26189step0 raw26189step0Labels := by
      have hz : ∀ j, raw26189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26189step0 = (fun i j => raw26189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26189step0 raw26189; decide +kernel
      have hl : raw26189step0Labels = raw26189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26189 raw26189Labels permutation346 hz
    mixedMoment B raw26189step0 raw26189step0Labels = mixedMoment B raw26189step1 raw26189step1Labels := by
      have ha : raw26189step1 = (fun i j => raw26189step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26189step1 raw26189step0; decide +kernel
      have hl : raw26189step1Labels = raw26189step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26189step0 raw26189step0Labels permutation40 permutation2
    _ = mixedMoment B node811 node811Labels := by rfl

def raw26190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26190Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26190step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26190step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26190 raw26190Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw26190 raw26190Labels = mixedMoment B raw26190step0 raw26190step0Labels := by
      have hz : ∀ j, raw26190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26190step0 = (fun i j => raw26190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26190step0 raw26190; decide +kernel
      have hl : raw26190step0Labels = raw26190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26190 raw26190Labels permutation346 hz
    mixedMoment B raw26190step0 raw26190step0Labels = mixedMoment B raw26190step1 raw26190step1Labels := by
      have ha : raw26190step1 = (fun i j => raw26190step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26190step1 raw26190step0; decide +kernel
      have hl : raw26190step1Labels = raw26190step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26190step0 raw26190step0Labels permutation46 permutation2
    _ = mixedMoment B node811 node811Labels := by rfl

def raw26191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26191Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26191step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26191step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26191 raw26191Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw26191 raw26191Labels = mixedMoment B raw26191step0 raw26191step0Labels := by
      have hz : ∀ j, raw26191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26191step0 = (fun i j => raw26191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26191step0 raw26191; decide +kernel
      have hl : raw26191step0Labels = raw26191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26191 raw26191Labels permutation346 hz
    mixedMoment B raw26191step0 raw26191step0Labels = mixedMoment B raw26191step1 raw26191step1Labels := by
      have ha : raw26191step1 = (fun i j => raw26191step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26191step1 raw26191step0; decide +kernel
      have hl : raw26191step1Labels = raw26191step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26191step0 raw26191step0Labels permutation53 permutation2
    _ = mixedMoment B node850 node850Labels := by rfl

def raw26192 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]
def raw26192Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26192step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![0, 0], ![1, -1], ![1, -1]]
def raw26192step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26192step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw26192step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26192step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26192step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26192 raw26192Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw26192 raw26192Labels = mixedMoment B raw26192step0 raw26192step0Labels := by
      have hz : ∀ j, raw26192 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw26192step0 = (fun i j => raw26192 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw26192step0 raw26192; decide +kernel
      have hl : raw26192step0Labels = raw26192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26192 raw26192Labels permutation590 hz
    mixedMoment B raw26192step0 raw26192step0Labels = mixedMoment B raw26192step1 raw26192step1Labels := by
      have hz : ∀ j, raw26192step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw26192step1 = (fun i j => raw26192step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw26192step1 raw26192step0; decide +kernel
      have hl : raw26192step1Labels = raw26192step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26192step0 raw26192step0Labels permutation80 hz
    mixedMoment B raw26192step1 raw26192step1Labels = mixedMoment B raw26192step2 raw26192step2Labels := by
      have ha : raw26192step2 = (fun i j => raw26192step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26192step2 raw26192step1; decide +kernel
      have hl : raw26192step2Labels = raw26192step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26192step1 raw26192step1Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw26193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26193 raw26193Labels = mixedMoment B node1638 node1638Labels := by
  calc
    _ = mixedMoment B node1638 node1638Labels := by rfl

def raw26194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26194 raw26194Labels = mixedMoment B node1638 node1638Labels := by
  calc
    mixedMoment B raw26194 raw26194Labels = mixedMoment B raw26194step0 raw26194step0Labels := by
      have ha : raw26194step0 = (fun i j => raw26194 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26194step0 raw26194; decide +kernel
      have hl : raw26194step0Labels = raw26194Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26194 raw26194Labels permutation176 permutation2
    _ = mixedMoment B node1638 node1638Labels := by rfl

def raw26195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26195 raw26195Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw26195 raw26195Labels = mixedMoment B raw26195step0 raw26195step0Labels := by
      have ha : raw26195step0 = (fun i j => raw26195 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26195step0 raw26195; decide +kernel
      have hl : raw26195step0Labels = raw26195Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26195 raw26195Labels permutation154 permutation2
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw26196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26196 raw26196Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26196 raw26196Labels = mixedMoment B raw26196step0 raw26196step0Labels := by
      have ha : raw26196step0 = (fun i j => raw26196 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26196step0 raw26196; decide +kernel
      have hl : raw26196step0Labels = raw26196Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26196 raw26196Labels permutation156 permutation2
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw26197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26197 raw26197Labels = mixedMoment B node541 node541Labels := by
  calc
    mixedMoment B raw26197 raw26197Labels = mixedMoment B raw26197step0 raw26197step0Labels := by
      have ha : raw26197step0 = (fun i j => raw26197 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26197step0 raw26197; decide +kernel
      have hl : raw26197step0Labels = raw26197Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26197 raw26197Labels permutation176 permutation2
    _ = mixedMoment B node541 node541Labels := by rfl

def raw26198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26198 raw26198Labels = mixedMoment B node736 node736Labels := by
  calc
    mixedMoment B raw26198 raw26198Labels = mixedMoment B raw26198step0 raw26198step0Labels := by
      have ha : raw26198step0 = (fun i j => raw26198 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26198step0 raw26198; decide +kernel
      have hl : raw26198step0Labels = raw26198Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26198 raw26198Labels permutation176 permutation2
    _ = mixedMoment B node736 node736Labels := by rfl

def raw26199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw26199Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw26199step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26199 raw26199Labels = mixedMoment B node786 node786Labels := by
  calc
    mixedMoment B raw26199 raw26199Labels = mixedMoment B raw26199step0 raw26199step0Labels := by
      have ha : raw26199step0 = (fun i j => raw26199 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26199step0 raw26199; decide +kernel
      have hl : raw26199step0Labels = raw26199Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26199 raw26199Labels permutation188 permutation2
    _ = mixedMoment B node786 node786Labels := by rfl

def raw26200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26200 raw26200Labels = mixedMoment B node805 node805Labels := by
  calc
    mixedMoment B raw26200 raw26200Labels = mixedMoment B raw26200step0 raw26200step0Labels := by
      have ha : raw26200step0 = (fun i j => raw26200 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26200step0 raw26200; decide +kernel
      have hl : raw26200step0Labels = raw26200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26200 raw26200Labels permutation194 permutation2
    _ = mixedMoment B node805 node805Labels := by rfl

def raw26201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26201 raw26201Labels = mixedMoment B node805 node805Labels := by
  calc
    mixedMoment B raw26201 raw26201Labels = mixedMoment B raw26201step0 raw26201step0Labels := by
      have ha : raw26201step0 = (fun i j => raw26201 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26201step0 raw26201; decide +kernel
      have hl : raw26201step0Labels = raw26201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26201 raw26201Labels permutation170 permutation2
    _ = mixedMoment B node805 node805Labels := by rfl

def raw26202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw26202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26202 raw26202Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw26202 raw26202Labels = mixedMoment B raw26202step0 raw26202step0Labels := by
      have ha : raw26202step0 = (fun i j => raw26202 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26202step0 raw26202; decide +kernel
      have hl : raw26202step0Labels = raw26202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26202 raw26202Labels permutation157 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

def raw26203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw26203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26203 raw26203Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw26203 raw26203Labels = mixedMoment B raw26203step0 raw26203step0Labels := by
      have ha : raw26203step0 = (fun i j => raw26203 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26203step0 raw26203; decide +kernel
      have hl : raw26203step0Labels = raw26203Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26203 raw26203Labels permutation156 permutation2
    _ = mixedMoment B node783 node783Labels := by rfl

def raw26204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26204 raw26204Labels = mixedMoment B node550 node550Labels := by
  calc
    mixedMoment B raw26204 raw26204Labels = mixedMoment B raw26204step0 raw26204step0Labels := by
      have ha : raw26204step0 = (fun i j => raw26204 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26204step0 raw26204; decide +kernel
      have hl : raw26204step0Labels = raw26204Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26204 raw26204Labels permutation152 permutation4
    mixedMoment B raw26204step0 raw26204step0Labels = mixedMoment B raw26204step1 raw26204step1Labels := by
      have ha : raw26204step1 = -raw26204step0 := by apply Matrix.ext; change ∀ i j, raw26204step1 i j = -(raw26204step0 i j); unfold raw26204step1 raw26204step0; decide +kernel
      have hl : raw26204step1Labels = raw26204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node550 node550Labels := by rfl

def raw26205 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26205step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26205step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26205 raw26205Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw26205 raw26205Labels = mixedMoment B raw26205step0 raw26205step0Labels := by
      have hz : ∀ j, raw26205 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26205step0 = (fun i j => raw26205 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26205step0 raw26205; decide +kernel
      have hl : raw26205step0Labels = raw26205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26205 raw26205Labels permutation265 hz
    mixedMoment B raw26205step0 raw26205step0Labels = mixedMoment B raw26205step1 raw26205step1Labels := by
      have ha : raw26205step1 = (fun i j => raw26205step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26205step1 raw26205step0; decide +kernel
      have hl : raw26205step1Labels = raw26205step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26205step0 raw26205step0Labels permutation32 permutation4
    mixedMoment B raw26205step1 raw26205step1Labels = mixedMoment B raw26205step2 raw26205step2Labels := by
      have ha : raw26205step2 = -raw26205step1 := by apply Matrix.ext; change ∀ i j, raw26205step2 i j = -(raw26205step1 i j); unfold raw26205step2 raw26205step1; decide +kernel
      have hl : raw26205step2Labels = raw26205step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node850 node850Labels := by rfl

def raw26206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26206step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26206 raw26206Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw26206 raw26206Labels = mixedMoment B raw26206step0 raw26206step0Labels := by
      have ha : raw26206step0 = (fun i j => raw26206 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26206step0 raw26206; decide +kernel
      have hl : raw26206step0Labels = raw26206Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26206 raw26206Labels permutation154 permutation2
    _ = mixedMoment B node1636 node1636Labels := by rfl

def raw26207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26207 raw26207Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw26207 raw26207Labels = mixedMoment B raw26207step0 raw26207step0Labels := by
      have ha : raw26207step0 = (fun i j => raw26207 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26207step0 raw26207; decide +kernel
      have hl : raw26207step0Labels = raw26207Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26207 raw26207Labels permutation178 permutation2
    _ = mixedMoment B node1636 node1636Labels := by rfl

def raw26208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw26208Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26208step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26208 raw26208Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw26208 raw26208Labels = mixedMoment B raw26208step0 raw26208step0Labels := by
      have hz : ∀ j, raw26208 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26208step0 = (fun i j => raw26208 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26208step0 raw26208; decide +kernel
      have hl : raw26208step0Labels = raw26208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26208 raw26208Labels permutation520 hz
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw26209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw26209Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw26209step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26209 raw26209Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw26209 raw26209Labels = mixedMoment B raw26209step0 raw26209step0Labels := by
      have ha : raw26209step0 = (fun i j => raw26209 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26209step0 raw26209; decide +kernel
      have hl : raw26209step0Labels = raw26209Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26209 raw26209Labels permutation154 permutation2
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw26210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26210Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26210step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26210 raw26210Labels = mixedMoment B node537 node537Labels := by
  calc
    mixedMoment B raw26210 raw26210Labels = mixedMoment B raw26210step0 raw26210step0Labels := by
      have ha : raw26210step0 = (fun i j => raw26210 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26210step0 raw26210; decide +kernel
      have hl : raw26210step0Labels = raw26210Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26210 raw26210Labels permutation188 permutation2
    _ = mixedMoment B node537 node537Labels := by rfl

def raw26211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw26211Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26211step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26211 raw26211Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw26211 raw26211Labels = mixedMoment B raw26211step0 raw26211step0Labels := by
      have ha : raw26211step0 = (fun i j => raw26211 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26211step0 raw26211; decide +kernel
      have hl : raw26211step0Labels = raw26211Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26211 raw26211Labels permutation188 permutation2
    _ = mixedMoment B node732 node732Labels := by rfl

def raw26212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw26212Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26212step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26212 raw26212Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw26212 raw26212Labels = mixedMoment B raw26212step0 raw26212step0Labels := by
      have hz : ∀ j, raw26212 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26212step0 = (fun i j => raw26212 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26212step0 raw26212; decide +kernel
      have hl : raw26212step0Labels = raw26212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26212 raw26212Labels permutation520 hz
    mixedMoment B raw26212step0 raw26212step0Labels = mixedMoment B raw26212step1 raw26212step1Labels := by
      have ha : raw26212step1 = (fun i j => raw26212step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26212step1 raw26212step0; decide +kernel
      have hl : raw26212step1Labels = raw26212step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26212step0 raw26212step0Labels permutation38 permutation2
    _ = mixedMoment B node810 node810Labels := by rfl

def raw26213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw26213Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26213step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26213 raw26213Labels = mixedMoment B node805 node805Labels := by
  calc
    mixedMoment B raw26213 raw26213Labels = mixedMoment B raw26213step0 raw26213step0Labels := by
      have ha : raw26213step0 = (fun i j => raw26213 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26213step0 raw26213; decide +kernel
      have hl : raw26213step0Labels = raw26213Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26213 raw26213Labels permutation188 permutation2
    _ = mixedMoment B node805 node805Labels := by rfl

def raw26214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26214step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26214step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26214step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26214 raw26214Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw26214 raw26214Labels = mixedMoment B raw26214step0 raw26214step0Labels := by
      have hz : ∀ j, raw26214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26214step0 = (fun i j => raw26214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26214step0 raw26214; decide +kernel
      have hl : raw26214step0Labels = raw26214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26214 raw26214Labels permutation346 hz
    mixedMoment B raw26214step0 raw26214step0Labels = mixedMoment B raw26214step1 raw26214step1Labels := by
      have ha : raw26214step1 = (fun i j => raw26214step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26214step1 raw26214step0; decide +kernel
      have hl : raw26214step1Labels = raw26214step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26214step0 raw26214step0Labels permutation32 permutation7
    mixedMoment B raw26214step1 raw26214step1Labels = mixedMoment B raw26214step2 raw26214step2Labels := by
      have ha : raw26214step2 = -raw26214step1 := by apply Matrix.ext; change ∀ i j, raw26214step2 i j = -(raw26214step1 i j); unfold raw26214step2 raw26214step1; decide +kernel
      have hl : raw26214step2Labels = raw26214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26214step2 raw26214step2Labels = mixedMoment B raw26214step3 raw26214step3Labels := by
      have ha : raw26214step3 = raw26214step2 := by apply Matrix.ext; unfold raw26214step3 raw26214step2; decide +kernel
      have hl : raw26214step2Labels = labelEmbedding10 ∘ raw26214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26214step2 raw26214step2Labels raw26214step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw26215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26215step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26215step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26215step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26215 raw26215Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw26215 raw26215Labels = mixedMoment B raw26215step0 raw26215step0Labels := by
      have ha : raw26215step0 = (fun i j => raw26215 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26215step0 raw26215; decide +kernel
      have hl : raw26215step0Labels = raw26215Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26215 raw26215Labels permutation176 permutation7
    mixedMoment B raw26215step0 raw26215step0Labels = mixedMoment B raw26215step1 raw26215step1Labels := by
      have ha : raw26215step1 = -raw26215step0 := by apply Matrix.ext; change ∀ i j, raw26215step1 i j = -(raw26215step0 i j); unfold raw26215step1 raw26215step0; decide +kernel
      have hl : raw26215step1Labels = raw26215step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26215step1 raw26215step1Labels = mixedMoment B raw26215step2 raw26215step2Labels := by
      have ha : raw26215step2 = raw26215step1 := by apply Matrix.ext; unfold raw26215step2 raw26215step1; decide +kernel
      have hl : raw26215step1Labels = labelEmbedding10 ∘ raw26215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26215step1 raw26215step1Labels raw26215step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw26216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26216step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26216step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26216step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26216step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26216 raw26216Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26216 raw26216Labels = mixedMoment B raw26216step0 raw26216step0Labels := by
      have hz : ∀ j, raw26216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26216step0 = (fun i j => raw26216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26216step0 raw26216; decide +kernel
      have hl : raw26216step0Labels = raw26216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26216 raw26216Labels permutation346 hz
    mixedMoment B raw26216step0 raw26216step0Labels = mixedMoment B raw26216step1 raw26216step1Labels := by
      have ha : raw26216step1 = (fun i j => raw26216step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26216step1 raw26216step0; decide +kernel
      have hl : raw26216step1Labels = raw26216step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26216step0 raw26216step0Labels permutation32 permutation7
    mixedMoment B raw26216step1 raw26216step1Labels = mixedMoment B raw26216step2 raw26216step2Labels := by
      have ha : raw26216step2 = -raw26216step1 := by apply Matrix.ext; change ∀ i j, raw26216step2 i j = -(raw26216step1 i j); unfold raw26216step2 raw26216step1; decide +kernel
      have hl : raw26216step2Labels = raw26216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26216step2 raw26216step2Labels = mixedMoment B raw26216step3 raw26216step3Labels := by
      have ha : raw26216step3 = raw26216step2 := by apply Matrix.ext; unfold raw26216step3 raw26216step2; decide +kernel
      have hl : raw26216step2Labels = labelEmbedding10 ∘ raw26216step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26216step2 raw26216step2Labels raw26216step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw26217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26217step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26217step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26217step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26217step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26217 raw26217Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw26217 raw26217Labels = mixedMoment B raw26217step0 raw26217step0Labels := by
      have hz : ∀ j, raw26217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26217step0 = (fun i j => raw26217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26217step0 raw26217; decide +kernel
      have hl : raw26217step0Labels = raw26217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26217 raw26217Labels permutation346 hz
    mixedMoment B raw26217step0 raw26217step0Labels = mixedMoment B raw26217step1 raw26217step1Labels := by
      have ha : raw26217step1 = (fun i j => raw26217step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26217step1 raw26217step0; decide +kernel
      have hl : raw26217step1Labels = raw26217step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26217step0 raw26217step0Labels permutation34 permutation7
    mixedMoment B raw26217step1 raw26217step1Labels = mixedMoment B raw26217step2 raw26217step2Labels := by
      have ha : raw26217step2 = -raw26217step1 := by apply Matrix.ext; change ∀ i j, raw26217step2 i j = -(raw26217step1 i j); unfold raw26217step2 raw26217step1; decide +kernel
      have hl : raw26217step2Labels = raw26217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26217step2 raw26217step2Labels = mixedMoment B raw26217step3 raw26217step3Labels := by
      have ha : raw26217step3 = raw26217step2 := by apply Matrix.ext; unfold raw26217step3 raw26217step2; decide +kernel
      have hl : raw26217step2Labels = labelEmbedding10 ∘ raw26217step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26217step2 raw26217step2Labels raw26217step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw26218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26218step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26218step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26218step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26218 raw26218Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw26218 raw26218Labels = mixedMoment B raw26218step0 raw26218step0Labels := by
      have hz : ∀ j, raw26218 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26218step0 = (fun i j => raw26218 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26218step0 raw26218; decide +kernel
      have hl : raw26218step0Labels = raw26218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26218 raw26218Labels permutation346 hz
    mixedMoment B raw26218step0 raw26218step0Labels = mixedMoment B raw26218step1 raw26218step1Labels := by
      have ha : raw26218step1 = (fun i j => raw26218step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26218step1 raw26218step0; decide +kernel
      have hl : raw26218step1Labels = raw26218step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26218step0 raw26218step0Labels permutation32 permutation7
    mixedMoment B raw26218step1 raw26218step1Labels = mixedMoment B raw26218step2 raw26218step2Labels := by
      have ha : raw26218step2 = -raw26218step1 := by apply Matrix.ext; change ∀ i j, raw26218step2 i j = -(raw26218step1 i j); unfold raw26218step2 raw26218step1; decide +kernel
      have hl : raw26218step2Labels = raw26218step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26218step2 raw26218step2Labels = mixedMoment B raw26218step3 raw26218step3Labels := by
      have ha : raw26218step3 = raw26218step2 := by apply Matrix.ext; unfold raw26218step3 raw26218step2; decide +kernel
      have hl : raw26218step2Labels = labelEmbedding10 ∘ raw26218step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26218step2 raw26218step2Labels raw26218step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw26219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26219 raw26219Labels = mixedMoment B node4125 node4125Labels := by
  calc
    mixedMoment B raw26219 raw26219Labels = mixedMoment B raw26219step0 raw26219step0Labels := by
      have hz : ∀ j, raw26219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26219step0 = (fun i j => raw26219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26219step0 raw26219; decide +kernel
      have hl : raw26219step0Labels = raw26219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26219 raw26219Labels permutation346 hz
    _ = mixedMoment B node4125 node4125Labels := by rfl

def raw26220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26220 raw26220Labels = mixedMoment B node4216 node4216Labels := by
  calc
    mixedMoment B raw26220 raw26220Labels = mixedMoment B raw26220step0 raw26220step0Labels := by
      have ha : raw26220step0 = (fun i j => raw26220 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26220step0 raw26220; decide +kernel
      have hl : raw26220step0Labels = raw26220Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26220 raw26220Labels permutation176 permutation2
    _ = mixedMoment B node4216 node4216Labels := by rfl

def raw26221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26221 raw26221Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26221 raw26221Labels = mixedMoment B raw26221step0 raw26221step0Labels := by
      have hz : ∀ j, raw26221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26221step0 = (fun i j => raw26221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26221step0 raw26221; decide +kernel
      have hl : raw26221step0Labels = raw26221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26221 raw26221Labels permutation346 hz
    mixedMoment B raw26221step0 raw26221step0Labels = mixedMoment B raw26221step1 raw26221step1Labels := by
      have ha : raw26221step1 = (fun i j => raw26221step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26221step1 raw26221step0; decide +kernel
      have hl : raw26221step1Labels = raw26221step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26221step0 raw26221step0Labels permutation38 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw26222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26222 raw26222Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26222 raw26222Labels = mixedMoment B raw26222step0 raw26222step0Labels := by
      have hz : ∀ j, raw26222 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26222step0 = (fun i j => raw26222 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26222step0 raw26222; decide +kernel
      have hl : raw26222step0Labels = raw26222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26222 raw26222Labels permutation346 hz
    mixedMoment B raw26222step0 raw26222step0Labels = mixedMoment B raw26222step1 raw26222step1Labels := by
      have ha : raw26222step1 = (fun i j => raw26222step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26222step1 raw26222step0; decide +kernel
      have hl : raw26222step1Labels = raw26222step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26222step0 raw26222step0Labels permutation44 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw26223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26223step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26223step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw26223step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26223step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26223 raw26223Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw26223 raw26223Labels = mixedMoment B raw26223step0 raw26223step0Labels := by
      have hz : ∀ j, raw26223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26223step0 = (fun i j => raw26223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26223step0 raw26223; decide +kernel
      have hl : raw26223step0Labels = raw26223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26223 raw26223Labels permutation346 hz
    mixedMoment B raw26223step0 raw26223step0Labels = mixedMoment B raw26223step1 raw26223step1Labels := by
      have hz : ∀ i, raw26223step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw26223step1 = (fun i j => raw26223step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw26223step1 raw26223step0; decide +kernel
      have hl : raw26223step1Labels = (fun j => raw26223step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26223step0 raw26223step0Labels permutation4 hz
    mixedMoment B raw26223step1 raw26223step1Labels = mixedMoment B raw26223step2 raw26223step2Labels := by
      have ha : raw26223step2 = raw26223step1 := by apply Matrix.ext; unfold raw26223step2 raw26223step1; decide +kernel
      have hl : raw26223step1Labels = labelEmbedding2 ∘ raw26223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26223step1 raw26223step1Labels raw26223step2Labels labelEmbedding2 hl
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw26224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26224 raw26224Labels = mixedMoment B node4100 node4100Labels := by
  calc
    _ = mixedMoment B node4100 node4100Labels := by rfl

def raw26225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26225 raw26225Labels = mixedMoment B node4232 node4232Labels := by
  calc
    _ = mixedMoment B node4232 node4232Labels := by rfl

def raw26226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26226 raw26226Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw26226 raw26226Labels = mixedMoment B raw26226step0 raw26226step0Labels := by
      have ha : raw26226step0 = (fun i j => raw26226 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26226step0 raw26226; decide +kernel
      have hl : raw26226step0Labels = raw26226Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26226 raw26226Labels permutation158 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw26227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26227 raw26227Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw26227 raw26227Labels = mixedMoment B raw26227step0 raw26227step0Labels := by
      have ha : raw26227step0 = (fun i j => raw26227 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26227step0 raw26227; decide +kernel
      have hl : raw26227step0Labels = raw26227Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26227 raw26227Labels permutation164 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw26228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26228 raw26228Labels = mixedMoment B node4263 node4263Labels := by
  calc
    _ = mixedMoment B node4263 node4263Labels := by rfl

def raw26229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26229 raw26229Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw26229 raw26229Labels = mixedMoment B raw26229step0 raw26229step0Labels := by
      have hz : ∀ j, raw26229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26229step0 = (fun i j => raw26229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26229step0 raw26229; decide +kernel
      have hl : raw26229step0Labels = raw26229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26229 raw26229Labels permutation346 hz
    mixedMoment B raw26229step0 raw26229step0Labels = mixedMoment B raw26229step1 raw26229step1Labels := by
      have ha : raw26229step1 = (fun i j => raw26229step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26229step1 raw26229step0; decide +kernel
      have hl : raw26229step1Labels = raw26229step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26229step0 raw26229step0Labels permutation34 permutation2
    _ = mixedMoment B node4107 node4107Labels := by rfl

def raw26230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26230 raw26230Labels = mixedMoment B node4239 node4239Labels := by
  calc
    mixedMoment B raw26230 raw26230Labels = mixedMoment B raw26230step0 raw26230step0Labels := by
      have hz : ∀ j, raw26230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26230step0 = (fun i j => raw26230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26230step0 raw26230; decide +kernel
      have hl : raw26230step0Labels = raw26230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26230 raw26230Labels permutation346 hz
    mixedMoment B raw26230step0 raw26230step0Labels = mixedMoment B raw26230step1 raw26230step1Labels := by
      have ha : raw26230step1 = (fun i j => raw26230step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26230step1 raw26230step0; decide +kernel
      have hl : raw26230step1Labels = raw26230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26230step0 raw26230step0Labels permutation34 permutation2
    _ = mixedMoment B node4239 node4239Labels := by rfl

def raw26231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26231 raw26231Labels = mixedMoment B node4201 node4201Labels := by
  calc
    mixedMoment B raw26231 raw26231Labels = mixedMoment B raw26231step0 raw26231step0Labels := by
      have ha : raw26231step0 = (fun i j => raw26231 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26231step0 raw26231; decide +kernel
      have hl : raw26231step0Labels = raw26231Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26231 raw26231Labels permutation178 permutation2
    _ = mixedMoment B node4201 node4201Labels := by rfl

def raw26232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26232 raw26232Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw26232 raw26232Labels = mixedMoment B raw26232step0 raw26232step0Labels := by
      have hz : ∀ j, raw26232 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26232step0 = (fun i j => raw26232 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26232step0 raw26232; decide +kernel
      have hl : raw26232step0Labels = raw26232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26232 raw26232Labels permutation346 hz
    mixedMoment B raw26232step0 raw26232step0Labels = mixedMoment B raw26232step1 raw26232step1Labels := by
      have ha : raw26232step1 = (fun i j => raw26232step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26232step1 raw26232step0; decide +kernel
      have hl : raw26232step1Labels = raw26232step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26232step0 raw26232step0Labels permutation34 permutation2
    _ = mixedMoment B node4256 node4256Labels := by rfl

def raw26233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26233 raw26233Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26233 raw26233Labels = mixedMoment B raw26233step0 raw26233step0Labels := by
      have hz : ∀ j, raw26233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26233step0 = (fun i j => raw26233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26233step0 raw26233; decide +kernel
      have hl : raw26233step0Labels = raw26233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26233 raw26233Labels permutation346 hz
    mixedMoment B raw26233step0 raw26233step0Labels = mixedMoment B raw26233step1 raw26233step1Labels := by
      have ha : raw26233step1 = (fun i j => raw26233step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26233step1 raw26233step0; decide +kernel
      have hl : raw26233step1Labels = raw26233step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26233step0 raw26233step0Labels permutation35 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw26234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26234 raw26234Labels = mixedMoment B node4107 node4107Labels := by
  calc
    mixedMoment B raw26234 raw26234Labels = mixedMoment B raw26234step0 raw26234step0Labels := by
      have hz : ∀ j, raw26234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26234step0 = (fun i j => raw26234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26234step0 raw26234; decide +kernel
      have hl : raw26234step0Labels = raw26234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26234 raw26234Labels permutation346 hz
    _ = mixedMoment B node4107 node4107Labels := by rfl

def raw26235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26235 raw26235Labels = mixedMoment B node4239 node4239Labels := by
  calc
    mixedMoment B raw26235 raw26235Labels = mixedMoment B raw26235step0 raw26235step0Labels := by
      have hz : ∀ j, raw26235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26235step0 = (fun i j => raw26235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26235step0 raw26235; decide +kernel
      have hl : raw26235step0Labels = raw26235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26235 raw26235Labels permutation346 hz
    _ = mixedMoment B node4239 node4239Labels := by rfl

def raw26236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26236 raw26236Labels = mixedMoment B node4201 node4201Labels := by
  calc
    mixedMoment B raw26236 raw26236Labels = mixedMoment B raw26236step0 raw26236step0Labels := by
      have ha : raw26236step0 = (fun i j => raw26236 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26236step0 raw26236; decide +kernel
      have hl : raw26236step0Labels = raw26236Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26236 raw26236Labels permutation176 permutation2
    _ = mixedMoment B node4201 node4201Labels := by rfl

def raw26237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26237 raw26237Labels = mixedMoment B node4256 node4256Labels := by
  calc
    mixedMoment B raw26237 raw26237Labels = mixedMoment B raw26237step0 raw26237step0Labels := by
      have hz : ∀ j, raw26237 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26237step0 = (fun i j => raw26237 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26237step0 raw26237; decide +kernel
      have hl : raw26237step0Labels = raw26237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26237 raw26237Labels permutation346 hz
    _ = mixedMoment B node4256 node4256Labels := by rfl

def raw26238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26238 raw26238Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26238 raw26238Labels = mixedMoment B raw26238step0 raw26238step0Labels := by
      have hz : ∀ j, raw26238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26238step0 = (fun i j => raw26238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26238step0 raw26238; decide +kernel
      have hl : raw26238step0Labels = raw26238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26238 raw26238Labels permutation346 hz
    mixedMoment B raw26238step0 raw26238step0Labels = mixedMoment B raw26238step1 raw26238step1Labels := by
      have ha : raw26238step1 = (fun i j => raw26238step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26238step1 raw26238step0; decide +kernel
      have hl : raw26238step1Labels = raw26238step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26238step0 raw26238step0Labels permutation33 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw26239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26239 raw26239Labels = mixedMoment B node4105 node4105Labels := by
  calc
    mixedMoment B raw26239 raw26239Labels = mixedMoment B raw26239step0 raw26239step0Labels := by
      have hz : ∀ j, raw26239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26239step0 = (fun i j => raw26239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26239step0 raw26239; decide +kernel
      have hl : raw26239step0Labels = raw26239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26239 raw26239Labels permutation346 hz
    _ = mixedMoment B node4105 node4105Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
