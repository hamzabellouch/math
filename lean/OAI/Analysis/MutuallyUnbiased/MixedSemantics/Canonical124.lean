import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw15872 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15872step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15872 raw15872Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw15872 raw15872Labels = mixedMoment B raw15872step0 raw15872step0Labels := by
      have hz : ∀ j, raw15872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15872step0 = (fun i j => raw15872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15872step0 raw15872; decide +kernel
      have hl : raw15872step0Labels = raw15872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15872 raw15872Labels permutation346 hz
    mixedMoment B raw15872step0 raw15872step0Labels = mixedMoment B raw15872step1 raw15872step1Labels := by
      have ha : raw15872step1 = (fun i j => raw15872step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15872step1 raw15872step0; decide +kernel
      have hl : raw15872step1Labels = raw15872step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15872step0 raw15872step0Labels permutation32 permutation6
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw15873 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15873 raw15873Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw15873 raw15873Labels = mixedMoment B raw15873step0 raw15873step0Labels := by
      have hz : ∀ j, raw15873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15873step0 = (fun i j => raw15873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15873step0 raw15873; decide +kernel
      have hl : raw15873step0Labels = raw15873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15873 raw15873Labels permutation434 hz
    mixedMoment B raw15873step0 raw15873step0Labels = mixedMoment B raw15873step1 raw15873step1Labels := by
      have ha : raw15873step1 = (fun i j => raw15873step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15873step1 raw15873step0; decide +kernel
      have hl : raw15873step1Labels = raw15873step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15873step0 raw15873step0Labels permutation32 permutation6
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw15874 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15874step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15874 raw15874Labels = mixedMoment B node2996 node2996Labels := by
  calc
    mixedMoment B raw15874 raw15874Labels = mixedMoment B raw15874step0 raw15874step0Labels := by
      have ha : raw15874step0 = (fun i j => raw15874 (permutation665 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15874step0 raw15874; decide +kernel
      have hl : raw15874step0Labels = raw15874Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15874 raw15874Labels permutation665 permutation3
    _ = mixedMoment B node2996 node2996Labels := by rfl

def raw15875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15875step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15875 raw15875Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw15875 raw15875Labels = mixedMoment B raw15875step0 raw15875step0Labels := by
      have ha : raw15875step0 = (fun i j => raw15875 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15875step0 raw15875; decide +kernel
      have hl : raw15875step0Labels = raw15875Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15875 raw15875Labels permutation152 permutation6
    _ = mixedMoment B node3567 node3567Labels := by rfl

def raw15876 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15876step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15876 raw15876Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw15876 raw15876Labels = mixedMoment B raw15876step0 raw15876step0Labels := by
      have hz : ∀ j, raw15876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15876step0 = (fun i j => raw15876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15876step0 raw15876; decide +kernel
      have hl : raw15876step0Labels = raw15876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15876 raw15876Labels permutation346 hz
    mixedMoment B raw15876step0 raw15876step0Labels = mixedMoment B raw15876step1 raw15876step1Labels := by
      have ha : raw15876step1 = (fun i j => raw15876step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15876step1 raw15876step0; decide +kernel
      have hl : raw15876step1Labels = raw15876step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15876step0 raw15876step0Labels permutation32 permutation6
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw15877 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15877 raw15877Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw15877 raw15877Labels = mixedMoment B raw15877step0 raw15877step0Labels := by
      have hz : ∀ j, raw15877 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15877step0 = (fun i j => raw15877 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15877step0 raw15877; decide +kernel
      have hl : raw15877step0Labels = raw15877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15877 raw15877Labels permutation434 hz
    mixedMoment B raw15877step0 raw15877step0Labels = mixedMoment B raw15877step1 raw15877step1Labels := by
      have ha : raw15877step1 = (fun i j => raw15877step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15877step1 raw15877step0; decide +kernel
      have hl : raw15877step1Labels = raw15877step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15877step0 raw15877step0Labels permutation32 permutation6
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw15878 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15878 raw15878Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw15878 raw15878Labels = mixedMoment B raw15878step0 raw15878step0Labels := by
      have ha : raw15878step0 = (fun i j => raw15878 (permutation668 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15878step0 raw15878; decide +kernel
      have hl : raw15878step0Labels = raw15878Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15878 raw15878Labels permutation668 permutation3
    _ = mixedMoment B node2976 node2976Labels := by rfl

def raw15879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15879 raw15879Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw15879 raw15879Labels = mixedMoment B raw15879step0 raw15879step0Labels := by
      have ha : raw15879step0 = (fun i j => raw15879 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15879step0 raw15879; decide +kernel
      have hl : raw15879step0Labels = raw15879Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15879 raw15879Labels permutation158 permutation6
    _ = mixedMoment B node3528 node3528Labels := by rfl

def raw15880 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15880step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15880 raw15880Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw15880 raw15880Labels = mixedMoment B raw15880step0 raw15880step0Labels := by
      have ha : raw15880step0 = (fun i j => raw15880 (permutation385 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15880step0 raw15880; decide +kernel
      have hl : raw15880step0Labels = raw15880Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15880 raw15880Labels permutation385 permutation3
    mixedMoment B raw15880step0 raw15880step0Labels = mixedMoment B raw15880step1 raw15880step1Labels := by
      have ha : raw15880step1 = -raw15880step0 := by apply Matrix.ext; change ∀ i j, raw15880step1 i j = -(raw15880step0 i j); unfold raw15880step1 raw15880step0; decide +kernel
      have hl : raw15880step1Labels = raw15880step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw15881 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15881 raw15881Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw15881 raw15881Labels = mixedMoment B raw15881step0 raw15881step0Labels := by
      have hz : ∀ j, raw15881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15881step0 = (fun i j => raw15881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15881step0 raw15881; decide +kernel
      have hl : raw15881step0Labels = raw15881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15881 raw15881Labels permutation434 hz
    mixedMoment B raw15881step0 raw15881step0Labels = mixedMoment B raw15881step1 raw15881step1Labels := by
      have ha : raw15881step1 = (fun i j => raw15881step0 (permutation86 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15881step1 raw15881step0; decide +kernel
      have hl : raw15881step1Labels = raw15881step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15881step0 raw15881step0Labels permutation86 permutation3
    mixedMoment B raw15881step1 raw15881step1Labels = mixedMoment B raw15881step2 raw15881step2Labels := by
      have ha : raw15881step2 = -raw15881step1 := by apply Matrix.ext; change ∀ i j, raw15881step2 i j = -(raw15881step1 i j); unfold raw15881step2 raw15881step1; decide +kernel
      have hl : raw15881step2Labels = raw15881step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw15882 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15882step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15882 raw15882Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw15882 raw15882Labels = mixedMoment B raw15882step0 raw15882step0Labels := by
      have ha : raw15882step0 = (fun i j => raw15882 (permutation666 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15882step0 raw15882; decide +kernel
      have hl : raw15882step0Labels = raw15882Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15882 raw15882Labels permutation666 permutation3
    _ = mixedMoment B node2974 node2974Labels := by rfl

def raw15883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15883step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15883 raw15883Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw15883 raw15883Labels = mixedMoment B raw15883step0 raw15883step0Labels := by
      have ha : raw15883step0 = (fun i j => raw15883 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15883step0 raw15883; decide +kernel
      have hl : raw15883step0Labels = raw15883Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15883 raw15883Labels permutation152 permutation6
    _ = mixedMoment B node3528 node3528Labels := by rfl

def raw15884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15884step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15884 raw15884Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw15884 raw15884Labels = mixedMoment B raw15884step0 raw15884step0Labels := by
      have ha : raw15884step0 = (fun i j => raw15884 (permutation470 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15884step0 raw15884; decide +kernel
      have hl : raw15884step0Labels = raw15884Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15884 raw15884Labels permutation470 permutation3
    mixedMoment B raw15884step0 raw15884step0Labels = mixedMoment B raw15884step1 raw15884step1Labels := by
      have ha : raw15884step1 = -raw15884step0 := by apply Matrix.ext; change ∀ i j, raw15884step1 i j = -(raw15884step0 i j); unfold raw15884step1 raw15884step0; decide +kernel
      have hl : raw15884step1Labels = raw15884step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw15885 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15885step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw15885step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15885step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15885 raw15885Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw15885 raw15885Labels = mixedMoment B raw15885step0 raw15885step0Labels := by
      have hz : ∀ j, raw15885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15885step0 = (fun i j => raw15885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15885step0 raw15885; decide +kernel
      have hl : raw15885step0Labels = raw15885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15885 raw15885Labels permutation346 hz
    mixedMoment B raw15885step0 raw15885step0Labels = mixedMoment B raw15885step1 raw15885step1Labels := by
      have ha : raw15885step1 = (fun i j => raw15885step0 (permutation86 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15885step1 raw15885step0; decide +kernel
      have hl : raw15885step1Labels = raw15885step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15885step0 raw15885step0Labels permutation86 permutation3
    mixedMoment B raw15885step1 raw15885step1Labels = mixedMoment B raw15885step2 raw15885step2Labels := by
      have ha : raw15885step2 = -raw15885step1 := by apply Matrix.ext; change ∀ i j, raw15885step2 i j = -(raw15885step1 i j); unfold raw15885step2 raw15885step1; decide +kernel
      have hl : raw15885step2Labels = raw15885step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw15886 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw15886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15886 raw15886Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw15886 raw15886Labels = mixedMoment B raw15886step0 raw15886step0Labels := by
      have ha : raw15886step0 = (fun i j => raw15886 (permutation665 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15886step0 raw15886; decide +kernel
      have hl : raw15886step0Labels = raw15886Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15886 raw15886Labels permutation665 permutation3
    _ = mixedMoment B node2974 node2974Labels := by rfl

def raw15887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15887step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15887 raw15887Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw15887 raw15887Labels = mixedMoment B raw15887step0 raw15887step0Labels := by
      have ha : raw15887step0 = (fun i j => raw15887 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15887step0 raw15887; decide +kernel
      have hl : raw15887step0Labels = raw15887Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15887 raw15887Labels permutation152 permutation6
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw15888 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15888 raw15888Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw15888 raw15888Labels = mixedMoment B raw15888step0 raw15888step0Labels := by
      have ha : raw15888step0 = (fun i j => raw15888 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15888step0 raw15888; decide +kernel
      have hl : raw15888step0Labels = raw15888Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15888 raw15888Labels permutation152 permutation6
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw15889 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15889 raw15889Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw15889 raw15889Labels = mixedMoment B raw15889step0 raw15889step0Labels := by
      have hz : ∀ j, raw15889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15889step0 = (fun i j => raw15889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15889step0 raw15889; decide +kernel
      have hl : raw15889step0Labels = raw15889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15889 raw15889Labels permutation434 hz
    mixedMoment B raw15889step0 raw15889step0Labels = mixedMoment B raw15889step1 raw15889step1Labels := by
      have ha : raw15889step1 = (fun i j => raw15889step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15889step1 raw15889step0; decide +kernel
      have hl : raw15889step1Labels = raw15889step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15889step0 raw15889step0Labels permutation32 permutation6
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw15890 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15890 raw15890Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw15890 raw15890Labels = mixedMoment B raw15890step0 raw15890step0Labels := by
      have ha : raw15890step0 = (fun i j => raw15890 (permutation599 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15890step0 raw15890; decide +kernel
      have hl : raw15890step0Labels = raw15890Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15890 raw15890Labels permutation599 permutation3
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw15891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw15891Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15891 raw15891Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw15891 raw15891Labels = mixedMoment B raw15891step0 raw15891step0Labels := by
      have ha : raw15891step0 = (fun i j => raw15891 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15891step0 raw15891; decide +kernel
      have hl : raw15891step0Labels = raw15891Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15891 raw15891Labels permutation152 permutation6
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw15892 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw15892step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15892step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15892step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15892 raw15892Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw15892 raw15892Labels = mixedMoment B raw15892step0 raw15892step0Labels := by
      have ha : raw15892step0 = (fun i j => raw15892 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15892step0 raw15892; decide +kernel
      have hl : raw15892step0Labels = raw15892Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15892 raw15892Labels permutation682 permutation7
    mixedMoment B raw15892step0 raw15892step0Labels = mixedMoment B raw15892step1 raw15892step1Labels := by
      have ha : raw15892step1 = -raw15892step0 := by apply Matrix.ext; change ∀ i j, raw15892step1 i j = -(raw15892step0 i j); unfold raw15892step1 raw15892step0; decide +kernel
      have hl : raw15892step1Labels = raw15892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15892step1 raw15892step1Labels = mixedMoment B raw15892step2 raw15892step2Labels := by
      have ha : raw15892step2 = raw15892step1 := by apply Matrix.ext; unfold raw15892step2 raw15892step1; decide +kernel
      have hl : raw15892step1Labels = labelEmbedding1 ∘ raw15892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15892step1 raw15892step1Labels raw15892step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw15893 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15893step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15893step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15893 raw15893Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw15893 raw15893Labels = mixedMoment B raw15893step0 raw15893step0Labels := by
      have hz : ∀ j, raw15893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15893step0 = (fun i j => raw15893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15893step0 raw15893; decide +kernel
      have hl : raw15893step0Labels = raw15893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15893 raw15893Labels permutation434 hz
    mixedMoment B raw15893step0 raw15893step0Labels = mixedMoment B raw15893step1 raw15893step1Labels := by
      have ha : raw15893step1 = (fun i j => raw15893step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15893step1 raw15893step0; decide +kernel
      have hl : raw15893step1Labels = raw15893step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15893step0 raw15893step0Labels permutation151 permutation7
    mixedMoment B raw15893step1 raw15893step1Labels = mixedMoment B raw15893step2 raw15893step2Labels := by
      have ha : raw15893step2 = -raw15893step1 := by apply Matrix.ext; change ∀ i j, raw15893step2 i j = -(raw15893step1 i j); unfold raw15893step2 raw15893step1; decide +kernel
      have hl : raw15893step2Labels = raw15893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15893step2 raw15893step2Labels = mixedMoment B raw15893step3 raw15893step3Labels := by
      have ha : raw15893step3 = raw15893step2 := by apply Matrix.ext; unfold raw15893step3 raw15893step2; decide +kernel
      have hl : raw15893step2Labels = labelEmbedding1 ∘ raw15893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15893step2 raw15893step2Labels raw15893step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw15894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw15894step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15894step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15894step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15894 raw15894Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw15894 raw15894Labels = mixedMoment B raw15894step0 raw15894step0Labels := by
      have ha : raw15894step0 = (fun i j => raw15894 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15894step0 raw15894; decide +kernel
      have hl : raw15894step0Labels = raw15894Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15894 raw15894Labels permutation682 permutation7
    mixedMoment B raw15894step0 raw15894step0Labels = mixedMoment B raw15894step1 raw15894step1Labels := by
      have ha : raw15894step1 = -raw15894step0 := by apply Matrix.ext; change ∀ i j, raw15894step1 i j = -(raw15894step0 i j); unfold raw15894step1 raw15894step0; decide +kernel
      have hl : raw15894step1Labels = raw15894step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15894step1 raw15894step1Labels = mixedMoment B raw15894step2 raw15894step2Labels := by
      have ha : raw15894step2 = raw15894step1 := by apply Matrix.ext; unfold raw15894step2 raw15894step1; decide +kernel
      have hl : raw15894step1Labels = labelEmbedding1 ∘ raw15894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15894step1 raw15894step1Labels raw15894step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

def raw15895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15895step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15895step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw15895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15895 raw15895Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw15895 raw15895Labels = mixedMoment B raw15895step0 raw15895step0Labels := by
      have ha : raw15895step0 = (fun i j => raw15895 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15895step0 raw15895; decide +kernel
      have hl : raw15895step0Labels = raw15895Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15895 raw15895Labels permutation263 permutation5
    mixedMoment B raw15895step0 raw15895step0Labels = mixedMoment B raw15895step1 raw15895step1Labels := by
      have ha : raw15895step1 = -raw15895step0 := by apply Matrix.ext; change ∀ i j, raw15895step1 i j = -(raw15895step0 i j); unfold raw15895step1 raw15895step0; decide +kernel
      have hl : raw15895step1Labels = raw15895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15895step1 raw15895step1Labels = mixedMoment B raw15895step2 raw15895step2Labels := by
      have ha : raw15895step2 = raw15895step1 := by apply Matrix.ext; unfold raw15895step2 raw15895step1; decide +kernel
      have hl : raw15895step1Labels = labelEmbedding1 ∘ raw15895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15895step1 raw15895step1Labels raw15895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw15896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15896step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15896step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15896 raw15896Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw15896 raw15896Labels = mixedMoment B raw15896step0 raw15896step0Labels := by
      have hz : ∀ j, raw15896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15896step0 = (fun i j => raw15896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15896step0 raw15896; decide +kernel
      have hl : raw15896step0Labels = raw15896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15896 raw15896Labels permutation434 hz
    mixedMoment B raw15896step0 raw15896step0Labels = mixedMoment B raw15896step1 raw15896step1Labels := by
      have ha : raw15896step1 = (fun i j => raw15896step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15896step1 raw15896step0; decide +kernel
      have hl : raw15896step1Labels = raw15896step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15896step0 raw15896step0Labels permutation151 permutation7
    mixedMoment B raw15896step1 raw15896step1Labels = mixedMoment B raw15896step2 raw15896step2Labels := by
      have ha : raw15896step2 = -raw15896step1 := by apply Matrix.ext; change ∀ i j, raw15896step2 i j = -(raw15896step1 i j); unfold raw15896step2 raw15896step1; decide +kernel
      have hl : raw15896step2Labels = raw15896step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15896step2 raw15896step2Labels = mixedMoment B raw15896step3 raw15896step3Labels := by
      have ha : raw15896step3 = raw15896step2 := by apply Matrix.ext; unfold raw15896step3 raw15896step2; decide +kernel
      have hl : raw15896step2Labels = labelEmbedding1 ∘ raw15896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15896step2 raw15896step2Labels raw15896step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw15897 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15897step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15897step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15897step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15897step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15897 raw15897Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw15897 raw15897Labels = mixedMoment B raw15897step0 raw15897step0Labels := by
      have ha : raw15897step0 = (fun i j => raw15897 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15897step0 raw15897; decide +kernel
      have hl : raw15897step0Labels = raw15897Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15897 raw15897Labels permutation682 permutation7
    mixedMoment B raw15897step0 raw15897step0Labels = mixedMoment B raw15897step1 raw15897step1Labels := by
      have ha : raw15897step1 = -raw15897step0 := by apply Matrix.ext; change ∀ i j, raw15897step1 i j = -(raw15897step0 i j); unfold raw15897step1 raw15897step0; decide +kernel
      have hl : raw15897step1Labels = raw15897step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15897step1 raw15897step1Labels = mixedMoment B raw15897step2 raw15897step2Labels := by
      have ha : raw15897step2 = raw15897step1 := by apply Matrix.ext; unfold raw15897step2 raw15897step1; decide +kernel
      have hl : raw15897step1Labels = labelEmbedding1 ∘ raw15897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15897step1 raw15897step1Labels raw15897step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw15898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15898step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15898step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15898 raw15898Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw15898 raw15898Labels = mixedMoment B raw15898step0 raw15898step0Labels := by
      have ha : raw15898step0 = (fun i j => raw15898 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15898step0 raw15898; decide +kernel
      have hl : raw15898step0Labels = raw15898Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15898 raw15898Labels permutation261 permutation5
    mixedMoment B raw15898step0 raw15898step0Labels = mixedMoment B raw15898step1 raw15898step1Labels := by
      have ha : raw15898step1 = -raw15898step0 := by apply Matrix.ext; change ∀ i j, raw15898step1 i j = -(raw15898step0 i j); unfold raw15898step1 raw15898step0; decide +kernel
      have hl : raw15898step1Labels = raw15898step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15898step1 raw15898step1Labels = mixedMoment B raw15898step2 raw15898step2Labels := by
      have ha : raw15898step2 = raw15898step1 := by apply Matrix.ext; unfold raw15898step2 raw15898step1; decide +kernel
      have hl : raw15898step1Labels = labelEmbedding1 ∘ raw15898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15898step1 raw15898step1Labels raw15898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw15899 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15899step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15899 raw15899Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw15899 raw15899Labels = mixedMoment B raw15899step0 raw15899step0Labels := by
      have ha : raw15899step0 = (fun i j => raw15899 (permutation394 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15899step0 raw15899; decide +kernel
      have hl : raw15899step0Labels = raw15899Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15899 raw15899Labels permutation394 permutation5
    mixedMoment B raw15899step0 raw15899step0Labels = mixedMoment B raw15899step1 raw15899step1Labels := by
      have ha : raw15899step1 = raw15899step0 := by apply Matrix.ext; unfold raw15899step1 raw15899step0; decide +kernel
      have hl : raw15899step0Labels = labelEmbedding1 ∘ raw15899step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15899step0 raw15899step0Labels raw15899step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw15900 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15900step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15900step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15900step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15900step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15900step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15900 raw15900Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw15900 raw15900Labels = mixedMoment B raw15900step0 raw15900step0Labels := by
      have hz : ∀ j, raw15900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15900step0 = (fun i j => raw15900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15900step0 raw15900; decide +kernel
      have hl : raw15900step0Labels = raw15900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15900 raw15900Labels permutation434 hz
    mixedMoment B raw15900step0 raw15900step0Labels = mixedMoment B raw15900step1 raw15900step1Labels := by
      have ha : raw15900step1 = (fun i j => raw15900step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15900step1 raw15900step0; decide +kernel
      have hl : raw15900step1Labels = raw15900step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15900step0 raw15900step0Labels permutation151 permutation7
    mixedMoment B raw15900step1 raw15900step1Labels = mixedMoment B raw15900step2 raw15900step2Labels := by
      have ha : raw15900step2 = -raw15900step1 := by apply Matrix.ext; change ∀ i j, raw15900step2 i j = -(raw15900step1 i j); unfold raw15900step2 raw15900step1; decide +kernel
      have hl : raw15900step2Labels = raw15900step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15900step2 raw15900step2Labels = mixedMoment B raw15900step3 raw15900step3Labels := by
      have ha : raw15900step3 = raw15900step2 := by apply Matrix.ext; unfold raw15900step3 raw15900step2; decide +kernel
      have hl : raw15900step2Labels = labelEmbedding1 ∘ raw15900step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15900step2 raw15900step2Labels raw15900step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw15901 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15901step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15901step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15901step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15901step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15901 raw15901Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw15901 raw15901Labels = mixedMoment B raw15901step0 raw15901step0Labels := by
      have ha : raw15901step0 = (fun i j => raw15901 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15901step0 raw15901; decide +kernel
      have hl : raw15901step0Labels = raw15901Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15901 raw15901Labels permutation688 permutation7
    mixedMoment B raw15901step0 raw15901step0Labels = mixedMoment B raw15901step1 raw15901step1Labels := by
      have ha : raw15901step1 = -raw15901step0 := by apply Matrix.ext; change ∀ i j, raw15901step1 i j = -(raw15901step0 i j); unfold raw15901step1 raw15901step0; decide +kernel
      have hl : raw15901step1Labels = raw15901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15901step1 raw15901step1Labels = mixedMoment B raw15901step2 raw15901step2Labels := by
      have ha : raw15901step2 = raw15901step1 := by apply Matrix.ext; unfold raw15901step2 raw15901step1; decide +kernel
      have hl : raw15901step1Labels = labelEmbedding1 ∘ raw15901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15901step1 raw15901step1Labels raw15901step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw15902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw15902step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15902step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw15902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15902 raw15902Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw15902 raw15902Labels = mixedMoment B raw15902step0 raw15902step0Labels := by
      have ha : raw15902step0 = (fun i j => raw15902 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15902step0 raw15902; decide +kernel
      have hl : raw15902step0Labels = raw15902Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15902 raw15902Labels permutation260 permutation5
    mixedMoment B raw15902step0 raw15902step0Labels = mixedMoment B raw15902step1 raw15902step1Labels := by
      have ha : raw15902step1 = -raw15902step0 := by apply Matrix.ext; change ∀ i j, raw15902step1 i j = -(raw15902step0 i j); unfold raw15902step1 raw15902step0; decide +kernel
      have hl : raw15902step1Labels = raw15902step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15902step1 raw15902step1Labels = mixedMoment B raw15902step2 raw15902step2Labels := by
      have ha : raw15902step2 = raw15902step1 := by apply Matrix.ext; unfold raw15902step2 raw15902step1; decide +kernel
      have hl : raw15902step1Labels = labelEmbedding1 ∘ raw15902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15902step1 raw15902step1Labels raw15902step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw15903 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15903Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15903step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw15903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15903 raw15903Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw15903 raw15903Labels = mixedMoment B raw15903step0 raw15903step0Labels := by
      have ha : raw15903step0 = (fun i j => raw15903 (permutation480 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15903step0 raw15903; decide +kernel
      have hl : raw15903step0Labels = raw15903Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15903 raw15903Labels permutation480 permutation5
    mixedMoment B raw15903step0 raw15903step0Labels = mixedMoment B raw15903step1 raw15903step1Labels := by
      have ha : raw15903step1 = raw15903step0 := by apply Matrix.ext; unfold raw15903step1 raw15903step0; decide +kernel
      have hl : raw15903step0Labels = labelEmbedding1 ∘ raw15903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15903step0 raw15903step0Labels raw15903step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw15904 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15904Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw15904step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15904step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15904step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw15904step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15904 raw15904Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw15904 raw15904Labels = mixedMoment B raw15904step0 raw15904step0Labels := by
      have ha : raw15904step0 = (fun i j => raw15904 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15904step0 raw15904; decide +kernel
      have hl : raw15904step0Labels = raw15904Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15904 raw15904Labels permutation682 permutation7
    mixedMoment B raw15904step0 raw15904step0Labels = mixedMoment B raw15904step1 raw15904step1Labels := by
      have ha : raw15904step1 = -raw15904step0 := by apply Matrix.ext; change ∀ i j, raw15904step1 i j = -(raw15904step0 i j); unfold raw15904step1 raw15904step0; decide +kernel
      have hl : raw15904step1Labels = raw15904step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15904step1 raw15904step1Labels = mixedMoment B raw15904step2 raw15904step2Labels := by
      have ha : raw15904step2 = raw15904step1 := by apply Matrix.ext; unfold raw15904step2 raw15904step1; decide +kernel
      have hl : raw15904step1Labels = labelEmbedding1 ∘ raw15904step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15904step1 raw15904step1Labels raw15904step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw15905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15905Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15905step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15905step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15905step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15905step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15905 raw15905Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw15905 raw15905Labels = mixedMoment B raw15905step0 raw15905step0Labels := by
      have ha : raw15905step0 = (fun i j => raw15905 (permutation250 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15905step0 raw15905; decide +kernel
      have hl : raw15905step0Labels = raw15905Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15905 raw15905Labels permutation250 permutation5
    mixedMoment B raw15905step0 raw15905step0Labels = mixedMoment B raw15905step1 raw15905step1Labels := by
      have ha : raw15905step1 = -raw15905step0 := by apply Matrix.ext; change ∀ i j, raw15905step1 i j = -(raw15905step0 i j); unfold raw15905step1 raw15905step0; decide +kernel
      have hl : raw15905step1Labels = raw15905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15905step1 raw15905step1Labels = mixedMoment B raw15905step2 raw15905step2Labels := by
      have ha : raw15905step2 = raw15905step1 := by apply Matrix.ext; unfold raw15905step2 raw15905step1; decide +kernel
      have hl : raw15905step1Labels = labelEmbedding1 ∘ raw15905step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15905step1 raw15905step1Labels raw15905step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw15906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw15906Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15906step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15906step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15906step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15906 raw15906Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw15906 raw15906Labels = mixedMoment B raw15906step0 raw15906step0Labels := by
      have ha : raw15906step0 = (fun i j => raw15906 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15906step0 raw15906; decide +kernel
      have hl : raw15906step0Labels = raw15906Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15906 raw15906Labels permutation682 permutation7
    mixedMoment B raw15906step0 raw15906step0Labels = mixedMoment B raw15906step1 raw15906step1Labels := by
      have ha : raw15906step1 = -raw15906step0 := by apply Matrix.ext; change ∀ i j, raw15906step1 i j = -(raw15906step0 i j); unfold raw15906step1 raw15906step0; decide +kernel
      have hl : raw15906step1Labels = raw15906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15906step1 raw15906step1Labels = mixedMoment B raw15906step2 raw15906step2Labels := by
      have ha : raw15906step2 = raw15906step1 := by apply Matrix.ext; unfold raw15906step2 raw15906step1; decide +kernel
      have hl : raw15906step1Labels = labelEmbedding1 ∘ raw15906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15906step1 raw15906step1Labels raw15906step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw15907 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw15907Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw15907step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15907step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw15907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15907 raw15907Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw15907 raw15907Labels = mixedMoment B raw15907step0 raw15907step0Labels := by
      have ha : raw15907step0 = (fun i j => raw15907 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15907step0 raw15907; decide +kernel
      have hl : raw15907step0Labels = raw15907Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15907 raw15907Labels permutation682 permutation7
    mixedMoment B raw15907step0 raw15907step0Labels = mixedMoment B raw15907step1 raw15907step1Labels := by
      have ha : raw15907step1 = -raw15907step0 := by apply Matrix.ext; change ∀ i j, raw15907step1 i j = -(raw15907step0 i j); unfold raw15907step1 raw15907step0; decide +kernel
      have hl : raw15907step1Labels = raw15907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15907step1 raw15907step1Labels = mixedMoment B raw15907step2 raw15907step2Labels := by
      have ha : raw15907step2 = raw15907step1 := by apply Matrix.ext; unfold raw15907step2 raw15907step1; decide +kernel
      have hl : raw15907step1Labels = labelEmbedding1 ∘ raw15907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15907step1 raw15907step1Labels raw15907step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw15908 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15908 raw15908Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw15908 raw15908Labels = mixedMoment B raw15908step0 raw15908step0Labels := by
      have ha : raw15908step0 = (fun i j => raw15908 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15908step0 raw15908; decide +kernel
      have hl : raw15908step0Labels = raw15908Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15908 raw15908Labels permutation668 permutation2
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw15909 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15909 raw15909Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw15909 raw15909Labels = mixedMoment B raw15909step0 raw15909step0Labels := by
      have ha : raw15909step0 = (fun i j => raw15909 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15909step0 raw15909; decide +kernel
      have hl : raw15909step0Labels = raw15909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15909 raw15909Labels permutation674 permutation2
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw15910 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15910 raw15910Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw15910 raw15910Labels = mixedMoment B raw15910step0 raw15910step0Labels := by
      have hz : ∀ j, raw15910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw15910step0 = (fun i j => raw15910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw15910step0 raw15910; decide +kernel
      have hl : raw15910step0Labels = raw15910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15910 raw15910Labels permutation346 hz
    mixedMoment B raw15910step0 raw15910step0Labels = mixedMoment B raw15910step1 raw15910step1Labels := by
      have ha : raw15910step1 = (fun i j => raw15910step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15910step1 raw15910step0; decide +kernel
      have hl : raw15910step1Labels = raw15910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15910step0 raw15910step0Labels permutation151 permutation2
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw15911 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw15911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15911 raw15911Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw15911 raw15911Labels = mixedMoment B raw15911step0 raw15911step0Labels := by
      have hz : ∀ j, raw15911 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw15911step0 = (fun i j => raw15911 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw15911step0 raw15911; decide +kernel
      have hl : raw15911step0Labels = raw15911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15911 raw15911Labels permutation434 hz
    mixedMoment B raw15911step0 raw15911step0Labels = mixedMoment B raw15911step1 raw15911step1Labels := by
      have ha : raw15911step1 = (fun i j => raw15911step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15911step1 raw15911step0; decide +kernel
      have hl : raw15911step1Labels = raw15911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15911step0 raw15911step0Labels permutation151 permutation2
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw15912 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw15912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15912 raw15912Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw15912 raw15912Labels = mixedMoment B raw15912step0 raw15912step0Labels := by
      have ha : raw15912step0 = (fun i j => raw15912 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15912step0 raw15912; decide +kernel
      have hl : raw15912step0Labels = raw15912Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15912 raw15912Labels permutation682 permutation2
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw15913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15913step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15913step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15913step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15913step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15913 raw15913Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw15913 raw15913Labels = mixedMoment B raw15913step0 raw15913step0Labels := by
      have ha : raw15913step0 = (fun i j => raw15913 (permutation305 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15913step0 raw15913; decide +kernel
      have hl : raw15913step0Labels = raw15913Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15913 raw15913Labels permutation305 permutation5
    mixedMoment B raw15913step0 raw15913step0Labels = mixedMoment B raw15913step1 raw15913step1Labels := by
      have ha : raw15913step1 = -raw15913step0 := by apply Matrix.ext; change ∀ i j, raw15913step1 i j = -(raw15913step0 i j); unfold raw15913step1 raw15913step0; decide +kernel
      have hl : raw15913step1Labels = raw15913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15913step1 raw15913step1Labels = mixedMoment B raw15913step2 raw15913step2Labels := by
      have ha : raw15913step2 = raw15913step1 := by apply Matrix.ext; unfold raw15913step2 raw15913step1; decide +kernel
      have hl : raw15913step1Labels = labelEmbedding8 ∘ raw15913step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15913step1 raw15913step1Labels raw15913step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw15914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15914step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15914step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15914step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15914 raw15914Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw15914 raw15914Labels = mixedMoment B raw15914step0 raw15914step0Labels := by
      have ha : raw15914step0 = (fun i j => raw15914 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15914step0 raw15914; decide +kernel
      have hl : raw15914step0Labels = raw15914Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15914 raw15914Labels permutation684 permutation3
    mixedMoment B raw15914step0 raw15914step0Labels = mixedMoment B raw15914step1 raw15914step1Labels := by
      have ha : raw15914step1 = -raw15914step0 := by apply Matrix.ext; change ∀ i j, raw15914step1 i j = -(raw15914step0 i j); unfold raw15914step1 raw15914step0; decide +kernel
      have hl : raw15914step1Labels = raw15914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15914step1 raw15914step1Labels = mixedMoment B raw15914step2 raw15914step2Labels := by
      have ha : raw15914step2 = raw15914step1 := by apply Matrix.ext; unfold raw15914step2 raw15914step1; decide +kernel
      have hl : raw15914step1Labels = labelEmbedding6 ∘ raw15914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15914step1 raw15914step1Labels raw15914step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw15915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15915step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15915step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15915step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15915 raw15915Labels = mixedMoment B node5461 node5461Labels := by
  calc
    mixedMoment B raw15915 raw15915Labels = mixedMoment B raw15915step0 raw15915step0Labels := by
      have ha : raw15915step0 = (fun i j => raw15915 (permutation321 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15915step0 raw15915; decide +kernel
      have hl : raw15915step0Labels = raw15915Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15915 raw15915Labels permutation321 permutation4
    mixedMoment B raw15915step0 raw15915step0Labels = mixedMoment B raw15915step1 raw15915step1Labels := by
      have ha : raw15915step1 = -raw15915step0 := by apply Matrix.ext; change ∀ i j, raw15915step1 i j = -(raw15915step0 i j); unfold raw15915step1 raw15915step0; decide +kernel
      have hl : raw15915step1Labels = raw15915step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15915step1 raw15915step1Labels = mixedMoment B raw15915step2 raw15915step2Labels := by
      have ha : raw15915step2 = raw15915step1 := by apply Matrix.ext; unfold raw15915step2 raw15915step1; decide +kernel
      have hl : raw15915step1Labels = labelEmbedding7 ∘ raw15915step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15915step1 raw15915step1Labels raw15915step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5461 node5461Labels := by rfl

def raw15916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15916step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15916step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15916step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15916step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15916 raw15916Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw15916 raw15916Labels = mixedMoment B raw15916step0 raw15916step0Labels := by
      have hz : ∀ j, raw15916 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15916step0 = (fun i j => raw15916 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15916step0 raw15916; decide +kernel
      have hl : raw15916step0Labels = raw15916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15916 raw15916Labels permutation520 hz
    mixedMoment B raw15916step0 raw15916step0Labels = mixedMoment B raw15916step1 raw15916step1Labels := by
      have ha : raw15916step1 = (fun i j => raw15916step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15916step1 raw15916step0; decide +kernel
      have hl : raw15916step1Labels = raw15916step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15916step0 raw15916step0Labels permutation73 permutation4
    mixedMoment B raw15916step1 raw15916step1Labels = mixedMoment B raw15916step2 raw15916step2Labels := by
      have ha : raw15916step2 = -raw15916step1 := by apply Matrix.ext; change ∀ i j, raw15916step2 i j = -(raw15916step1 i j); unfold raw15916step2 raw15916step1; decide +kernel
      have hl : raw15916step2Labels = raw15916step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15916step2 raw15916step2Labels = mixedMoment B raw15916step3 raw15916step3Labels := by
      have ha : raw15916step3 = raw15916step2 := by apply Matrix.ext; unfold raw15916step3 raw15916step2; decide +kernel
      have hl : raw15916step2Labels = labelEmbedding7 ∘ raw15916step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15916step2 raw15916step2Labels raw15916step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw15917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15917step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15917step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw15917step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15917step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15917 raw15917Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw15917 raw15917Labels = mixedMoment B raw15917step0 raw15917step0Labels := by
      have ha : raw15917step0 = (fun i j => raw15917 (permutation321 i) (permutation4 j)) := by apply Matrix.ext; unfold raw15917step0 raw15917; decide +kernel
      have hl : raw15917step0Labels = raw15917Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15917 raw15917Labels permutation321 permutation4
    mixedMoment B raw15917step0 raw15917step0Labels = mixedMoment B raw15917step1 raw15917step1Labels := by
      have ha : raw15917step1 = -raw15917step0 := by apply Matrix.ext; change ∀ i j, raw15917step1 i j = -(raw15917step0 i j); unfold raw15917step1 raw15917step0; decide +kernel
      have hl : raw15917step1Labels = raw15917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15917step1 raw15917step1Labels = mixedMoment B raw15917step2 raw15917step2Labels := by
      have ha : raw15917step2 = raw15917step1 := by apply Matrix.ext; unfold raw15917step2 raw15917step1; decide +kernel
      have hl : raw15917step1Labels = labelEmbedding7 ∘ raw15917step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15917step1 raw15917step1Labels raw15917step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw15918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15918 raw15918Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw15918 raw15918Labels = mixedMoment B raw15918step0 raw15918step0Labels := by
      have ha : raw15918step0 = (fun i j => raw15918 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15918step0 raw15918; decide +kernel
      have hl : raw15918step0Labels = raw15918Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15918 raw15918Labels permutation176 permutation2
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw15919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15919 raw15919Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw15919 raw15919Labels = mixedMoment B raw15919step0 raw15919step0Labels := by
      have ha : raw15919step0 = (fun i j => raw15919 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15919step0 raw15919; decide +kernel
      have hl : raw15919step0Labels = raw15919Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15919 raw15919Labels permutation176 permutation2
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw15920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15920step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15920step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15920step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15920step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15920step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15920 raw15920Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw15920 raw15920Labels = mixedMoment B raw15920step0 raw15920step0Labels := by
      have ha : raw15920step0 = (fun i j => raw15920 (permutation190 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15920step0 raw15920; decide +kernel
      have hl : raw15920step0Labels = raw15920Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15920 raw15920Labels permutation190 permutation7
    mixedMoment B raw15920step0 raw15920step0Labels = mixedMoment B raw15920step1 raw15920step1Labels := by
      have ha : raw15920step1 = -raw15920step0 := by apply Matrix.ext; change ∀ i j, raw15920step1 i j = -(raw15920step0 i j); unfold raw15920step1 raw15920step0; decide +kernel
      have hl : raw15920step1Labels = raw15920step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15920step1 raw15920step1Labels = mixedMoment B raw15920step2 raw15920step2Labels := by
      have ha : raw15920step2 = raw15920step1 := by apply Matrix.ext; unfold raw15920step2 raw15920step1; decide +kernel
      have hl : raw15920step1Labels = labelEmbedding10 ∘ raw15920step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15920step1 raw15920step1Labels raw15920step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw15921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15921step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15921step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15921step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15921 raw15921Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw15921 raw15921Labels = mixedMoment B raw15921step0 raw15921step0Labels := by
      have hz : ∀ j, raw15921 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15921step0 = (fun i j => raw15921 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15921step0 raw15921; decide +kernel
      have hl : raw15921step0Labels = raw15921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15921 raw15921Labels permutation520 hz
    mixedMoment B raw15921step0 raw15921step0Labels = mixedMoment B raw15921step1 raw15921step1Labels := by
      have ha : raw15921step1 = (fun i j => raw15921step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15921step1 raw15921step0; decide +kernel
      have hl : raw15921step1Labels = raw15921step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15921step0 raw15921step0Labels permutation38 permutation7
    mixedMoment B raw15921step1 raw15921step1Labels = mixedMoment B raw15921step2 raw15921step2Labels := by
      have ha : raw15921step2 = -raw15921step1 := by apply Matrix.ext; change ∀ i j, raw15921step2 i j = -(raw15921step1 i j); unfold raw15921step2 raw15921step1; decide +kernel
      have hl : raw15921step2Labels = raw15921step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15921step2 raw15921step2Labels = mixedMoment B raw15921step3 raw15921step3Labels := by
      have ha : raw15921step3 = raw15921step2 := by apply Matrix.ext; unfold raw15921step3 raw15921step2; decide +kernel
      have hl : raw15921step2Labels = labelEmbedding10 ∘ raw15921step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15921step2 raw15921step2Labels raw15921step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw15922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15922step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15922step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15922step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15922step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15922 raw15922Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw15922 raw15922Labels = mixedMoment B raw15922step0 raw15922step0Labels := by
      have ha : raw15922step0 = (fun i j => raw15922 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15922step0 raw15922; decide +kernel
      have hl : raw15922step0Labels = raw15922Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15922 raw15922Labels permutation188 permutation7
    mixedMoment B raw15922step0 raw15922step0Labels = mixedMoment B raw15922step1 raw15922step1Labels := by
      have ha : raw15922step1 = -raw15922step0 := by apply Matrix.ext; change ∀ i j, raw15922step1 i j = -(raw15922step0 i j); unfold raw15922step1 raw15922step0; decide +kernel
      have hl : raw15922step1Labels = raw15922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15922step1 raw15922step1Labels = mixedMoment B raw15922step2 raw15922step2Labels := by
      have ha : raw15922step2 = raw15922step1 := by apply Matrix.ext; unfold raw15922step2 raw15922step1; decide +kernel
      have hl : raw15922step1Labels = labelEmbedding10 ∘ raw15922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15922step1 raw15922step1Labels raw15922step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw15923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw15923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15923 raw15923Labels = mixedMoment B node5190 node5190Labels := by
  calc
    mixedMoment B raw15923 raw15923Labels = mixedMoment B raw15923step0 raw15923step0Labels := by
      have ha : raw15923step0 = (fun i j => raw15923 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15923step0 raw15923; decide +kernel
      have hl : raw15923step0Labels = raw15923Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15923 raw15923Labels permutation158 permutation2
    _ = mixedMoment B node5190 node5190Labels := by rfl

def raw15924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15924step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15924step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15924step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15924step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15924step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15924 raw15924Labels = mixedMoment B node5124 node5124Labels := by
  calc
    mixedMoment B raw15924 raw15924Labels = mixedMoment B raw15924step0 raw15924step0Labels := by
      have ha : raw15924step0 = (fun i j => raw15924 (permutation308 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15924step0 raw15924; decide +kernel
      have hl : raw15924step0Labels = raw15924Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15924 raw15924Labels permutation308 permutation5
    mixedMoment B raw15924step0 raw15924step0Labels = mixedMoment B raw15924step1 raw15924step1Labels := by
      have ha : raw15924step1 = -raw15924step0 := by apply Matrix.ext; change ∀ i j, raw15924step1 i j = -(raw15924step0 i j); unfold raw15924step1 raw15924step0; decide +kernel
      have hl : raw15924step1Labels = raw15924step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15924step1 raw15924step1Labels = mixedMoment B raw15924step2 raw15924step2Labels := by
      have ha : raw15924step2 = raw15924step1 := by apply Matrix.ext; unfold raw15924step2 raw15924step1; decide +kernel
      have hl : raw15924step1Labels = labelEmbedding8 ∘ raw15924step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15924step1 raw15924step1Labels raw15924step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5124 node5124Labels := by rfl

def raw15925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw15925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15925 raw15925Labels = mixedMoment B node5444 node5444Labels := by
  calc
    mixedMoment B raw15925 raw15925Labels = mixedMoment B raw15925step0 raw15925step0Labels := by
      have ha : raw15925step0 = (fun i j => raw15925 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15925step0 raw15925; decide +kernel
      have hl : raw15925step0Labels = raw15925Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15925 raw15925Labels permutation158 permutation2
    _ = mixedMoment B node5444 node5444Labels := by rfl

def raw15926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw15926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15926 raw15926Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw15926 raw15926Labels = mixedMoment B raw15926step0 raw15926step0Labels := by
      have hz : ∀ j, raw15926 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15926step0 = (fun i j => raw15926 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15926step0 raw15926; decide +kernel
      have hl : raw15926step0Labels = raw15926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15926 raw15926Labels permutation520 hz
    mixedMoment B raw15926step0 raw15926step0Labels = mixedMoment B raw15926step1 raw15926step1Labels := by
      have ha : raw15926step1 = (fun i j => raw15926step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15926step1 raw15926step0; decide +kernel
      have hl : raw15926step1Labels = raw15926step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15926step0 raw15926step0Labels permutation34 permutation2
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw15927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15927 raw15927Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw15927 raw15927Labels = mixedMoment B raw15927step0 raw15927step0Labels := by
      have ha : raw15927step0 = (fun i j => raw15927 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15927step0 raw15927; decide +kernel
      have hl : raw15927step0Labels = raw15927Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15927 raw15927Labels permutation158 permutation2
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw15928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15928 raw15928Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw15928 raw15928Labels = mixedMoment B raw15928step0 raw15928step0Labels := by
      have ha : raw15928step0 = (fun i j => raw15928 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15928step0 raw15928; decide +kernel
      have hl : raw15928step0Labels = raw15928Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15928 raw15928Labels permutation154 permutation2
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw15929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15929step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15929step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15929step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15929step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15929 raw15929Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw15929 raw15929Labels = mixedMoment B raw15929step0 raw15929step0Labels := by
      have ha : raw15929step0 = (fun i j => raw15929 (permutation271 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15929step0 raw15929; decide +kernel
      have hl : raw15929step0Labels = raw15929Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15929 raw15929Labels permutation271 permutation5
    mixedMoment B raw15929step0 raw15929step0Labels = mixedMoment B raw15929step1 raw15929step1Labels := by
      have ha : raw15929step1 = -raw15929step0 := by apply Matrix.ext; change ∀ i j, raw15929step1 i j = -(raw15929step0 i j); unfold raw15929step1 raw15929step0; decide +kernel
      have hl : raw15929step1Labels = raw15929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15929step1 raw15929step1Labels = mixedMoment B raw15929step2 raw15929step2Labels := by
      have ha : raw15929step2 = raw15929step1 := by apply Matrix.ext; unfold raw15929step2 raw15929step1; decide +kernel
      have hl : raw15929step1Labels = labelEmbedding8 ∘ raw15929step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15929step1 raw15929step1Labels raw15929step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw15930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15930 raw15930Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw15930 raw15930Labels = mixedMoment B raw15930step0 raw15930step0Labels := by
      have ha : raw15930step0 = (fun i j => raw15930 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw15930step0 raw15930; decide +kernel
      have hl : raw15930step0Labels = raw15930Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15930 raw15930Labels permutation178 permutation2
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw15931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15931step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15931step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15931step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15931step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15931step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15931 raw15931Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw15931 raw15931Labels = mixedMoment B raw15931step0 raw15931step0Labels := by
      have hz : ∀ j, raw15931 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15931step0 = (fun i j => raw15931 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15931step0 raw15931; decide +kernel
      have hl : raw15931step0Labels = raw15931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15931 raw15931Labels permutation520 hz
    mixedMoment B raw15931step0 raw15931step0Labels = mixedMoment B raw15931step1 raw15931step1Labels := by
      have ha : raw15931step1 = (fun i j => raw15931step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15931step1 raw15931step0; decide +kernel
      have hl : raw15931step1Labels = raw15931step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15931step0 raw15931step0Labels permutation38 permutation7
    mixedMoment B raw15931step1 raw15931step1Labels = mixedMoment B raw15931step2 raw15931step2Labels := by
      have ha : raw15931step2 = -raw15931step1 := by apply Matrix.ext; change ∀ i j, raw15931step2 i j = -(raw15931step1 i j); unfold raw15931step2 raw15931step1; decide +kernel
      have hl : raw15931step2Labels = raw15931step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15931step2 raw15931step2Labels = mixedMoment B raw15931step3 raw15931step3Labels := by
      have ha : raw15931step3 = raw15931step2 := by apply Matrix.ext; unfold raw15931step3 raw15931step2; decide +kernel
      have hl : raw15931step2Labels = labelEmbedding10 ∘ raw15931step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15931step2 raw15931step2Labels raw15931step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw15932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15932step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15932step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw15932step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15932step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15932 raw15932Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw15932 raw15932Labels = mixedMoment B raw15932step0 raw15932step0Labels := by
      have ha : raw15932step0 = (fun i j => raw15932 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15932step0 raw15932; decide +kernel
      have hl : raw15932step0Labels = raw15932Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15932 raw15932Labels permutation188 permutation7
    mixedMoment B raw15932step0 raw15932step0Labels = mixedMoment B raw15932step1 raw15932step1Labels := by
      have ha : raw15932step1 = -raw15932step0 := by apply Matrix.ext; change ∀ i j, raw15932step1 i j = -(raw15932step0 i j); unfold raw15932step1 raw15932step0; decide +kernel
      have hl : raw15932step1Labels = raw15932step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15932step1 raw15932step1Labels = mixedMoment B raw15932step2 raw15932step2Labels := by
      have ha : raw15932step2 = raw15932step1 := by apply Matrix.ext; unfold raw15932step2 raw15932step1; decide +kernel
      have hl : raw15932step1Labels = labelEmbedding10 ∘ raw15932step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15932step1 raw15932step1Labels raw15932step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw15933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15933 raw15933Labels = mixedMoment B node5182 node5182Labels := by
  calc
    _ = mixedMoment B node5182 node5182Labels := by rfl

def raw15934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw15934step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15934step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw15934step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw15934step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw15934step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15934 raw15934Labels = mixedMoment B node5122 node5122Labels := by
  calc
    mixedMoment B raw15934 raw15934Labels = mixedMoment B raw15934step0 raw15934step0Labels := by
      have ha : raw15934step0 = (fun i j => raw15934 (permutation306 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15934step0 raw15934; decide +kernel
      have hl : raw15934step0Labels = raw15934Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15934 raw15934Labels permutation306 permutation5
    mixedMoment B raw15934step0 raw15934step0Labels = mixedMoment B raw15934step1 raw15934step1Labels := by
      have ha : raw15934step1 = -raw15934step0 := by apply Matrix.ext; change ∀ i j, raw15934step1 i j = -(raw15934step0 i j); unfold raw15934step1 raw15934step0; decide +kernel
      have hl : raw15934step1Labels = raw15934step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15934step1 raw15934step1Labels = mixedMoment B raw15934step2 raw15934step2Labels := by
      have ha : raw15934step2 = raw15934step1 := by apply Matrix.ext; unfold raw15934step2 raw15934step1; decide +kernel
      have hl : raw15934step1Labels = labelEmbedding8 ∘ raw15934step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15934step1 raw15934step1Labels raw15934step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5122 node5122Labels := by rfl

def raw15935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15935step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15935step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15935step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15935step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15935 raw15935Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw15935 raw15935Labels = mixedMoment B raw15935step0 raw15935step0Labels := by
      have ha : raw15935step0 = (fun i j => raw15935 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15935step0 raw15935; decide +kernel
      have hl : raw15935step0Labels = raw15935Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15935 raw15935Labels permutation589 permutation3
    mixedMoment B raw15935step0 raw15935step0Labels = mixedMoment B raw15935step1 raw15935step1Labels := by
      have ha : raw15935step1 = -raw15935step0 := by apply Matrix.ext; change ∀ i j, raw15935step1 i j = -(raw15935step0 i j); unfold raw15935step1 raw15935step0; decide +kernel
      have hl : raw15935step1Labels = raw15935step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15935step1 raw15935step1Labels = mixedMoment B raw15935step2 raw15935step2Labels := by
      have ha : raw15935step2 = raw15935step1 := by apply Matrix.ext; unfold raw15935step2 raw15935step1; decide +kernel
      have hl : raw15935step1Labels = labelEmbedding6 ∘ raw15935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15935step1 raw15935step1Labels raw15935step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw15936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15936step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15936step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15936step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15936step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15936 raw15936Labels = mixedMoment B node5347 node5347Labels := by
  calc
    mixedMoment B raw15936 raw15936Labels = mixedMoment B raw15936step0 raw15936step0Labels := by
      have ha : raw15936step0 = (fun i j => raw15936 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15936step0 raw15936; decide +kernel
      have hl : raw15936step0Labels = raw15936Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15936 raw15936Labels permutation582 permutation3
    mixedMoment B raw15936step0 raw15936step0Labels = mixedMoment B raw15936step1 raw15936step1Labels := by
      have ha : raw15936step1 = -raw15936step0 := by apply Matrix.ext; change ∀ i j, raw15936step1 i j = -(raw15936step0 i j); unfold raw15936step1 raw15936step0; decide +kernel
      have hl : raw15936step1Labels = raw15936step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15936step1 raw15936step1Labels = mixedMoment B raw15936step2 raw15936step2Labels := by
      have ha : raw15936step2 = raw15936step1 := by apply Matrix.ext; unfold raw15936step2 raw15936step1; decide +kernel
      have hl : raw15936step1Labels = labelEmbedding6 ∘ raw15936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15936step1 raw15936step1Labels raw15936step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5347 node5347Labels := by rfl

def raw15937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15937step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15937step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15937step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15937step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15937 raw15937Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw15937 raw15937Labels = mixedMoment B raw15937step0 raw15937step0Labels := by
      have ha : raw15937step0 = (fun i j => raw15937 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15937step0 raw15937; decide +kernel
      have hl : raw15937step0Labels = raw15937Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15937 raw15937Labels permutation584 permutation3
    mixedMoment B raw15937step0 raw15937step0Labels = mixedMoment B raw15937step1 raw15937step1Labels := by
      have ha : raw15937step1 = -raw15937step0 := by apply Matrix.ext; change ∀ i j, raw15937step1 i j = -(raw15937step0 i j); unfold raw15937step1 raw15937step0; decide +kernel
      have hl : raw15937step1Labels = raw15937step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15937step1 raw15937step1Labels = mixedMoment B raw15937step2 raw15937step2Labels := by
      have ha : raw15937step2 = raw15937step1 := by apply Matrix.ext; unfold raw15937step2 raw15937step1; decide +kernel
      have hl : raw15937step1Labels = labelEmbedding6 ∘ raw15937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15937step1 raw15937step1Labels raw15937step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw15938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw15938step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw15938step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15938step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw15938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15938 raw15938Labels = mixedMoment B node5048 node5048Labels := by
  calc
    mixedMoment B raw15938 raw15938Labels = mixedMoment B raw15938step0 raw15938step0Labels := by
      have ha : raw15938step0 = (fun i j => raw15938 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15938step0 raw15938; decide +kernel
      have hl : raw15938step0Labels = raw15938Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15938 raw15938Labels permutation682 permutation3
    mixedMoment B raw15938step0 raw15938step0Labels = mixedMoment B raw15938step1 raw15938step1Labels := by
      have ha : raw15938step1 = -raw15938step0 := by apply Matrix.ext; change ∀ i j, raw15938step1 i j = -(raw15938step0 i j); unfold raw15938step1 raw15938step0; decide +kernel
      have hl : raw15938step1Labels = raw15938step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15938step1 raw15938step1Labels = mixedMoment B raw15938step2 raw15938step2Labels := by
      have ha : raw15938step2 = raw15938step1 := by apply Matrix.ext; unfold raw15938step2 raw15938step1; decide +kernel
      have hl : raw15938step1Labels = labelEmbedding6 ∘ raw15938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15938step1 raw15938step1Labels raw15938step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5048 node5048Labels := by rfl

def raw15939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw15939step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw15939step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15939step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw15939step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15939 raw15939Labels = mixedMoment B node5049 node5049Labels := by
  calc
    mixedMoment B raw15939 raw15939Labels = mixedMoment B raw15939step0 raw15939step0Labels := by
      have ha : raw15939step0 = (fun i j => raw15939 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15939step0 raw15939; decide +kernel
      have hl : raw15939step0Labels = raw15939Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15939 raw15939Labels permutation681 permutation3
    mixedMoment B raw15939step0 raw15939step0Labels = mixedMoment B raw15939step1 raw15939step1Labels := by
      have ha : raw15939step1 = -raw15939step0 := by apply Matrix.ext; change ∀ i j, raw15939step1 i j = -(raw15939step0 i j); unfold raw15939step1 raw15939step0; decide +kernel
      have hl : raw15939step1Labels = raw15939step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15939step1 raw15939step1Labels = mixedMoment B raw15939step2 raw15939step2Labels := by
      have ha : raw15939step2 = raw15939step1 := by apply Matrix.ext; unfold raw15939step2 raw15939step1; decide +kernel
      have hl : raw15939step1Labels = labelEmbedding6 ∘ raw15939step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15939step1 raw15939step1Labels raw15939step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5049 node5049Labels := by rfl

def raw15940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15940step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15940step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15940step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15940step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15940 raw15940Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw15940 raw15940Labels = mixedMoment B raw15940step0 raw15940step0Labels := by
      have ha : raw15940step0 = (fun i j => raw15940 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15940step0 raw15940; decide +kernel
      have hl : raw15940step0Labels = raw15940Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15940 raw15940Labels permutation688 permutation3
    mixedMoment B raw15940step0 raw15940step0Labels = mixedMoment B raw15940step1 raw15940step1Labels := by
      have ha : raw15940step1 = -raw15940step0 := by apply Matrix.ext; change ∀ i j, raw15940step1 i j = -(raw15940step0 i j); unfold raw15940step1 raw15940step0; decide +kernel
      have hl : raw15940step1Labels = raw15940step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15940step1 raw15940step1Labels = mixedMoment B raw15940step2 raw15940step2Labels := by
      have ha : raw15940step2 = raw15940step1 := by apply Matrix.ext; unfold raw15940step2 raw15940step1; decide +kernel
      have hl : raw15940step1Labels = labelEmbedding6 ∘ raw15940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15940step1 raw15940step1Labels raw15940step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw15941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15941step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15941step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15941step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15941 raw15941Labels = mixedMoment B node5061 node5061Labels := by
  calc
    mixedMoment B raw15941 raw15941Labels = mixedMoment B raw15941step0 raw15941step0Labels := by
      have ha : raw15941step0 = (fun i j => raw15941 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15941step0 raw15941; decide +kernel
      have hl : raw15941step0Labels = raw15941Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15941 raw15941Labels permutation680 permutation3
    mixedMoment B raw15941step0 raw15941step0Labels = mixedMoment B raw15941step1 raw15941step1Labels := by
      have ha : raw15941step1 = -raw15941step0 := by apply Matrix.ext; change ∀ i j, raw15941step1 i j = -(raw15941step0 i j); unfold raw15941step1 raw15941step0; decide +kernel
      have hl : raw15941step1Labels = raw15941step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15941step1 raw15941step1Labels = mixedMoment B raw15941step2 raw15941step2Labels := by
      have ha : raw15941step2 = raw15941step1 := by apply Matrix.ext; unfold raw15941step2 raw15941step1; decide +kernel
      have hl : raw15941step1Labels = labelEmbedding6 ∘ raw15941step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15941step1 raw15941step1Labels raw15941step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5061 node5061Labels := by rfl

def raw15942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw15942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw15942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw15942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15942step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15942step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15942step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw15942step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15942step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical15942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15942 raw15942Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw15942 raw15942Labels = mixedMoment B raw15942step0 raw15942step0Labels := by
      have hz : ∀ j, raw15942 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15942step0 = (fun i j => raw15942 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15942step0 raw15942; decide +kernel
      have hl : raw15942step0Labels = raw15942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15942 raw15942Labels permutation520 hz
    mixedMoment B raw15942step0 raw15942step0Labels = mixedMoment B raw15942step1 raw15942step1Labels := by
      have ha : raw15942step1 = (fun i j => raw15942step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15942step1 raw15942step0; decide +kernel
      have hl : raw15942step1Labels = raw15942step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15942step0 raw15942step0Labels permutation145 permutation3
    mixedMoment B raw15942step1 raw15942step1Labels = mixedMoment B raw15942step2 raw15942step2Labels := by
      have ha : raw15942step2 = -raw15942step1 := by apply Matrix.ext; change ∀ i j, raw15942step2 i j = -(raw15942step1 i j); unfold raw15942step2 raw15942step1; decide +kernel
      have hl : raw15942step2Labels = raw15942step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15942step2 raw15942step2Labels = mixedMoment B raw15942step3 raw15942step3Labels := by
      have ha : raw15942step3 = raw15942step2 := by apply Matrix.ext; unfold raw15942step3 raw15942step2; decide +kernel
      have hl : raw15942step2Labels = labelEmbedding6 ∘ raw15942step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15942step2 raw15942step2Labels raw15942step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw15943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15943step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15943 raw15943Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw15943 raw15943Labels = mixedMoment B raw15943step0 raw15943step0Labels := by
      have ha : raw15943step0 = (fun i j => raw15943 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15943step0 raw15943; decide +kernel
      have hl : raw15943step0Labels = raw15943Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15943 raw15943Labels permutation271 permutation3
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw15944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15944step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15944 raw15944Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw15944 raw15944Labels = mixedMoment B raw15944step0 raw15944step0Labels := by
      have ha : raw15944step0 = (fun i j => raw15944 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15944step0 raw15944; decide +kernel
      have hl : raw15944step0Labels = raw15944Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15944 raw15944Labels permutation684 permutation3
    mixedMoment B raw15944step0 raw15944step0Labels = mixedMoment B raw15944step1 raw15944step1Labels := by
      have ha : raw15944step1 = -raw15944step0 := by apply Matrix.ext; change ∀ i j, raw15944step1 i j = -(raw15944step0 i j); unfold raw15944step1 raw15944step0; decide +kernel
      have hl : raw15944step1Labels = raw15944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw15945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw15945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw15945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15945 raw15945Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw15945 raw15945Labels = mixedMoment B raw15945step0 raw15945step0Labels := by
      have ha : raw15945step0 = (fun i j => raw15945 (permutation677 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15945step0 raw15945; decide +kernel
      have hl : raw15945step0Labels = raw15945Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15945 raw15945Labels permutation677 permutation3
    mixedMoment B raw15945step0 raw15945step0Labels = mixedMoment B raw15945step1 raw15945step1Labels := by
      have ha : raw15945step1 = -raw15945step0 := by apply Matrix.ext; change ∀ i j, raw15945step1 i j = -(raw15945step0 i j); unfold raw15945step1 raw15945step0; decide +kernel
      have hl : raw15945step1Labels = raw15945step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3973 node3973Labels := by rfl

def raw15946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15946step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15946 raw15946Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw15946 raw15946Labels = mixedMoment B raw15946step0 raw15946step0Labels := by
      have hz : ∀ j, raw15946 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15946step0 = (fun i j => raw15946 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15946step0 raw15946; decide +kernel
      have hl : raw15946step0Labels = raw15946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15946 raw15946Labels permutation520 hz
    mixedMoment B raw15946step0 raw15946step0Labels = mixedMoment B raw15946step1 raw15946step1Labels := by
      have ha : raw15946step1 = (fun i j => raw15946step0 (permutation43 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15946step1 raw15946step0; decide +kernel
      have hl : raw15946step1Labels = raw15946step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15946step0 raw15946step0Labels permutation43 permutation6
    mixedMoment B raw15946step1 raw15946step1Labels = mixedMoment B raw15946step2 raw15946step2Labels := by
      have ha : raw15946step2 = -raw15946step1 := by apply Matrix.ext; change ∀ i j, raw15946step2 i j = -(raw15946step1 i j); unfold raw15946step2 raw15946step1; decide +kernel
      have hl : raw15946step2Labels = raw15946step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw15947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15947step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15947step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15947 raw15947Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw15947 raw15947Labels = mixedMoment B raw15947step0 raw15947step0Labels := by
      have ha : raw15947step0 = (fun i j => raw15947 (permutation193 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15947step0 raw15947; decide +kernel
      have hl : raw15947step0Labels = raw15947Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15947 raw15947Labels permutation193 permutation6
    mixedMoment B raw15947step0 raw15947step0Labels = mixedMoment B raw15947step1 raw15947step1Labels := by
      have ha : raw15947step1 = -raw15947step0 := by apply Matrix.ext; change ∀ i j, raw15947step1 i j = -(raw15947step0 i j); unfold raw15947step1 raw15947step0; decide +kernel
      have hl : raw15947step1Labels = raw15947step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw15948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw15948step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15948 raw15948Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw15948 raw15948Labels = mixedMoment B raw15948step0 raw15948step0Labels := by
      have ha : raw15948step0 = (fun i j => raw15948 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15948step0 raw15948; decide +kernel
      have hl : raw15948step0Labels = raw15948Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15948 raw15948Labels permutation158 permutation3
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw15949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw15949step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw15949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15949 raw15949Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw15949 raw15949Labels = mixedMoment B raw15949step0 raw15949step0Labels := by
      have ha : raw15949step0 = (fun i j => raw15949 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15949step0 raw15949; decide +kernel
      have hl : raw15949step0Labels = raw15949Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15949 raw15949Labels permutation676 permutation3
    mixedMoment B raw15949step0 raw15949step0Labels = mixedMoment B raw15949step1 raw15949step1Labels := by
      have ha : raw15949step1 = -raw15949step0 := by apply Matrix.ext; change ∀ i j, raw15949step1 i j = -(raw15949step0 i j); unfold raw15949step1 raw15949step0; decide +kernel
      have hl : raw15949step1Labels = raw15949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw15950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15950step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15950 raw15950Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw15950 raw15950Labels = mixedMoment B raw15950step0 raw15950step0Labels := by
      have ha : raw15950step0 = (fun i j => raw15950 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15950step0 raw15950; decide +kernel
      have hl : raw15950step0Labels = raw15950Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15950 raw15950Labels permutation680 permutation3
    mixedMoment B raw15950step0 raw15950step0Labels = mixedMoment B raw15950step1 raw15950step1Labels := by
      have ha : raw15950step1 = -raw15950step0 := by apply Matrix.ext; change ∀ i j, raw15950step1 i j = -(raw15950step0 i j); unfold raw15950step1 raw15950step0; decide +kernel
      have hl : raw15950step1Labels = raw15950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw15951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw15951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw15951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15951 raw15951Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw15951 raw15951Labels = mixedMoment B raw15951step0 raw15951step0Labels := by
      have hz : ∀ j, raw15951 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15951step0 = (fun i j => raw15951 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15951step0 raw15951; decide +kernel
      have hl : raw15951step0Labels = raw15951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15951 raw15951Labels permutation520 hz
    mixedMoment B raw15951step0 raw15951step0Labels = mixedMoment B raw15951step1 raw15951step1Labels := by
      have ha : raw15951step1 = (fun i j => raw15951step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15951step1 raw15951step0; decide +kernel
      have hl : raw15951step1Labels = raw15951step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15951step0 raw15951step0Labels permutation143 permutation3
    mixedMoment B raw15951step1 raw15951step1Labels = mixedMoment B raw15951step2 raw15951step2Labels := by
      have ha : raw15951step2 = -raw15951step1 := by apply Matrix.ext; change ∀ i j, raw15951step2 i j = -(raw15951step1 i j); unfold raw15951step2 raw15951step1; decide +kernel
      have hl : raw15951step2Labels = raw15951step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw15952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw15952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw15952step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15952 raw15952Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw15952 raw15952Labels = mixedMoment B raw15952step0 raw15952step0Labels := by
      have ha : raw15952step0 = (fun i j => raw15952 (permutation192 i) (permutation6 j)) := by apply Matrix.ext; unfold raw15952step0 raw15952; decide +kernel
      have hl : raw15952step0Labels = raw15952Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15952 raw15952Labels permutation192 permutation6
    mixedMoment B raw15952step0 raw15952step0Labels = mixedMoment B raw15952step1 raw15952step1Labels := by
      have ha : raw15952step1 = -raw15952step0 := by apply Matrix.ext; change ∀ i j, raw15952step1 i j = -(raw15952step0 i j); unfold raw15952step1 raw15952step0; decide +kernel
      have hl : raw15952step1Labels = raw15952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw15953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15953 raw15953Labels = mixedMoment B node2854 node2854Labels := by
  calc
    mixedMoment B raw15953 raw15953Labels = mixedMoment B raw15953step0 raw15953step0Labels := by
      have ha : raw15953step0 = (fun i j => raw15953 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15953step0 raw15953; decide +kernel
      have hl : raw15953step0Labels = raw15953Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15953 raw15953Labels permutation160 permutation3
    _ = mixedMoment B node2854 node2854Labels := by rfl

def raw15954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15954 raw15954Labels = mixedMoment B node3371 node3371Labels := by
  calc
    mixedMoment B raw15954 raw15954Labels = mixedMoment B raw15954step0 raw15954step0Labels := by
      have ha : raw15954step0 = (fun i j => raw15954 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15954step0 raw15954; decide +kernel
      have hl : raw15954step0Labels = raw15954Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15954 raw15954Labels permutation273 permutation3
    _ = mixedMoment B node3371 node3371Labels := by rfl

def raw15955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15955step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15955 raw15955Labels = mixedMoment B node3943 node3943Labels := by
  calc
    mixedMoment B raw15955 raw15955Labels = mixedMoment B raw15955step0 raw15955step0Labels := by
      have ha : raw15955step0 = (fun i j => raw15955 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15955step0 raw15955; decide +kernel
      have hl : raw15955step0Labels = raw15955Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15955 raw15955Labels permutation644 permutation3
    mixedMoment B raw15955step0 raw15955step0Labels = mixedMoment B raw15955step1 raw15955step1Labels := by
      have ha : raw15955step1 = -raw15955step0 := by apply Matrix.ext; change ∀ i j, raw15955step1 i j = -(raw15955step0 i j); unfold raw15955step1 raw15955step0; decide +kernel
      have hl : raw15955step1Labels = raw15955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3943 node3943Labels := by rfl

def raw15956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15956step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15956step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15956 raw15956Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw15956 raw15956Labels = mixedMoment B raw15956step0 raw15956step0Labels := by
      have hz : ∀ j, raw15956 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15956step0 = (fun i j => raw15956 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15956step0 raw15956; decide +kernel
      have hl : raw15956step0Labels = raw15956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15956 raw15956Labels permutation520 hz
    mixedMoment B raw15956step0 raw15956step0Labels = mixedMoment B raw15956step1 raw15956step1Labels := by
      have ha : raw15956step1 = (fun i j => raw15956step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15956step1 raw15956step0; decide +kernel
      have hl : raw15956step1Labels = raw15956step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15956step0 raw15956step0Labels permutation145 permutation3
    mixedMoment B raw15956step1 raw15956step1Labels = mixedMoment B raw15956step2 raw15956step2Labels := by
      have ha : raw15956step2 = -raw15956step1 := by apply Matrix.ext; change ∀ i j, raw15956step2 i j = -(raw15956step1 i j); unfold raw15956step2 raw15956step1; decide +kernel
      have hl : raw15956step2Labels = raw15956step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw15957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15957step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15957 raw15957Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw15957 raw15957Labels = mixedMoment B raw15957step0 raw15957step0Labels := by
      have ha : raw15957step0 = (fun i j => raw15957 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15957step0 raw15957; decide +kernel
      have hl : raw15957step0Labels = raw15957Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15957 raw15957Labels permutation163 permutation3
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw15958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15958step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15958 raw15958Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw15958 raw15958Labels = mixedMoment B raw15958step0 raw15958step0Labels := by
      have ha : raw15958step0 = (fun i j => raw15958 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15958step0 raw15958; decide +kernel
      have hl : raw15958step0Labels = raw15958Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15958 raw15958Labels permutation152 permutation3
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw15959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw15959step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15959 raw15959Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw15959 raw15959Labels = mixedMoment B raw15959step0 raw15959step0Labels := by
      have ha : raw15959step0 = (fun i j => raw15959 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15959step0 raw15959; decide +kernel
      have hl : raw15959step0Labels = raw15959Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15959 raw15959Labels permutation265 permutation3
    _ = mixedMoment B node3376 node3376Labels := by rfl

def raw15960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15960Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15960 raw15960Labels = mixedMoment B node3966 node3966Labels := by
  calc
    mixedMoment B raw15960 raw15960Labels = mixedMoment B raw15960step0 raw15960step0Labels := by
      have ha : raw15960step0 = (fun i j => raw15960 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15960step0 raw15960; decide +kernel
      have hl : raw15960step0Labels = raw15960Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15960 raw15960Labels permutation688 permutation3
    mixedMoment B raw15960step0 raw15960step0Labels = mixedMoment B raw15960step1 raw15960step1Labels := by
      have ha : raw15960step1 = -raw15960step0 := by apply Matrix.ext; change ∀ i j, raw15960step1 i j = -(raw15960step0 i j); unfold raw15960step1 raw15960step0; decide +kernel
      have hl : raw15960step1Labels = raw15960step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3966 node3966Labels := by rfl

def raw15961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw15961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15961 raw15961Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw15961 raw15961Labels = mixedMoment B raw15961step0 raw15961step0Labels := by
      have hz : ∀ j, raw15961 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15961step0 = (fun i j => raw15961 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15961step0 raw15961; decide +kernel
      have hl : raw15961step0Labels = raw15961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15961 raw15961Labels permutation520 hz
    mixedMoment B raw15961step0 raw15961step0Labels = mixedMoment B raw15961step1 raw15961step1Labels := by
      have ha : raw15961step1 = (fun i j => raw15961step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15961step1 raw15961step0; decide +kernel
      have hl : raw15961step1Labels = raw15961step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15961step0 raw15961step0Labels permutation151 permutation3
    mixedMoment B raw15961step1 raw15961step1Labels = mixedMoment B raw15961step2 raw15961step2Labels := by
      have ha : raw15961step2 = -raw15961step1 := by apply Matrix.ext; change ∀ i j, raw15961step2 i j = -(raw15961step1 i j); unfold raw15961step2 raw15961step1; decide +kernel
      have hl : raw15961step2Labels = raw15961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw15962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15962 raw15962Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw15962 raw15962Labels = mixedMoment B raw15962step0 raw15962step0Labels := by
      have ha : raw15962step0 = (fun i j => raw15962 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15962step0 raw15962; decide +kernel
      have hl : raw15962step0Labels = raw15962Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15962 raw15962Labels permutation153 permutation3
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw15963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw15963step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15963 raw15963Labels = mixedMoment B node2850 node2850Labels := by
  calc
    mixedMoment B raw15963 raw15963Labels = mixedMoment B raw15963step0 raw15963step0Labels := by
      have ha : raw15963step0 = (fun i j => raw15963 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15963step0 raw15963; decide +kernel
      have hl : raw15963step0Labels = raw15963Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15963 raw15963Labels permutation159 permutation3
    _ = mixedMoment B node2850 node2850Labels := by rfl

def raw15964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw15964step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15964 raw15964Labels = mixedMoment B node3367 node3367Labels := by
  calc
    mixedMoment B raw15964 raw15964Labels = mixedMoment B raw15964step0 raw15964step0Labels := by
      have ha : raw15964step0 = (fun i j => raw15964 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15964step0 raw15964; decide +kernel
      have hl : raw15964step0Labels = raw15964Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15964 raw15964Labels permutation272 permutation3
    _ = mixedMoment B node3367 node3367Labels := by rfl

def raw15965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15965 raw15965Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw15965 raw15965Labels = mixedMoment B raw15965step0 raw15965step0Labels := by
      have ha : raw15965step0 = (fun i j => raw15965 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15965step0 raw15965; decide +kernel
      have hl : raw15965step0Labels = raw15965Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15965 raw15965Labels permutation589 permutation3
    mixedMoment B raw15965step0 raw15965step0Labels = mixedMoment B raw15965step1 raw15965step1Labels := by
      have ha : raw15965step1 = -raw15965step0 := by apply Matrix.ext; change ∀ i j, raw15965step1 i j = -(raw15965step0 i j); unfold raw15965step1 raw15965step0; decide +kernel
      have hl : raw15965step1Labels = raw15965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3691 node3691Labels := by rfl

def raw15966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15966step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15966step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15966 raw15966Labels = mixedMoment B node3684 node3684Labels := by
  calc
    mixedMoment B raw15966 raw15966Labels = mixedMoment B raw15966step0 raw15966step0Labels := by
      have ha : raw15966step0 = (fun i j => raw15966 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15966step0 raw15966; decide +kernel
      have hl : raw15966step0Labels = raw15966Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15966 raw15966Labels permutation582 permutation3
    mixedMoment B raw15966step0 raw15966step0Labels = mixedMoment B raw15966step1 raw15966step1Labels := by
      have ha : raw15966step1 = -raw15966step0 := by apply Matrix.ext; change ∀ i j, raw15966step1 i j = -(raw15966step0 i j); unfold raw15966step1 raw15966step0; decide +kernel
      have hl : raw15966step1Labels = raw15966step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3684 node3684Labels := by rfl

def raw15967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15967step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15967 raw15967Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw15967 raw15967Labels = mixedMoment B raw15967step0 raw15967step0Labels := by
      have ha : raw15967step0 = (fun i j => raw15967 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15967step0 raw15967; decide +kernel
      have hl : raw15967step0Labels = raw15967Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15967 raw15967Labels permutation584 permutation3
    mixedMoment B raw15967step0 raw15967step0Labels = mixedMoment B raw15967step1 raw15967step1Labels := by
      have ha : raw15967step1 = -raw15967step0 := by apply Matrix.ext; change ∀ i j, raw15967step1 i j = -(raw15967step0 i j); unfold raw15967step1 raw15967step0; decide +kernel
      have hl : raw15967step1Labels = raw15967step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw15968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw15968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw15968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15968 raw15968Labels = mixedMoment B node2450 node2450Labels := by
  calc
    mixedMoment B raw15968 raw15968Labels = mixedMoment B raw15968step0 raw15968step0Labels := by
      have ha : raw15968step0 = (fun i j => raw15968 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15968step0 raw15968; decide +kernel
      have hl : raw15968step0Labels = raw15968Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15968 raw15968Labels permutation682 permutation3
    mixedMoment B raw15968step0 raw15968step0Labels = mixedMoment B raw15968step1 raw15968step1Labels := by
      have ha : raw15968step1 = -raw15968step0 := by apply Matrix.ext; change ∀ i j, raw15968step1 i j = -(raw15968step0 i j); unfold raw15968step1 raw15968step0; decide +kernel
      have hl : raw15968step1Labels = raw15968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2450 node2450Labels := by rfl

def raw15969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw15969step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw15969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15969 raw15969Labels = mixedMoment B node2451 node2451Labels := by
  calc
    mixedMoment B raw15969 raw15969Labels = mixedMoment B raw15969step0 raw15969step0Labels := by
      have ha : raw15969step0 = (fun i j => raw15969 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15969step0 raw15969; decide +kernel
      have hl : raw15969step0Labels = raw15969Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15969 raw15969Labels permutation681 permutation3
    mixedMoment B raw15969step0 raw15969step0Labels = mixedMoment B raw15969step1 raw15969step1Labels := by
      have ha : raw15969step1 = -raw15969step0 := by apply Matrix.ext; change ∀ i j, raw15969step1 i j = -(raw15969step0 i j); unfold raw15969step1 raw15969step0; decide +kernel
      have hl : raw15969step1Labels = raw15969step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2451 node2451Labels := by rfl

def raw15970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw15970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw15970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15970 raw15970Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw15970 raw15970Labels = mixedMoment B raw15970step0 raw15970step0Labels := by
      have ha : raw15970step0 = (fun i j => raw15970 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15970step0 raw15970; decide +kernel
      have hl : raw15970step0Labels = raw15970Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15970 raw15970Labels permutation688 permutation3
    mixedMoment B raw15970step0 raw15970step0Labels = mixedMoment B raw15970step1 raw15970step1Labels := by
      have ha : raw15970step1 = -raw15970step0 := by apply Matrix.ext; change ∀ i j, raw15970step1 i j = -(raw15970step0 i j); unfold raw15970step1 raw15970step0; decide +kernel
      have hl : raw15970step1Labels = raw15970step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw15971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw15971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw15971step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15971 raw15971Labels = mixedMoment B node2464 node2464Labels := by
  calc
    mixedMoment B raw15971 raw15971Labels = mixedMoment B raw15971step0 raw15971step0Labels := by
      have ha : raw15971step0 = (fun i j => raw15971 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15971step0 raw15971; decide +kernel
      have hl : raw15971step0Labels = raw15971Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15971 raw15971Labels permutation680 permutation3
    mixedMoment B raw15971step0 raw15971step0Labels = mixedMoment B raw15971step1 raw15971step1Labels := by
      have ha : raw15971step1 = -raw15971step0 := by apply Matrix.ext; change ∀ i j, raw15971step1 i j = -(raw15971step0 i j); unfold raw15971step1 raw15971step0; decide +kernel
      have hl : raw15971step1Labels = raw15971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2464 node2464Labels := by rfl

def raw15972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw15972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw15972step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw15972step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw15972step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw15972step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw15972step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15972 raw15972Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw15972 raw15972Labels = mixedMoment B raw15972step0 raw15972step0Labels := by
      have hz : ∀ j, raw15972 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15972step0 = (fun i j => raw15972 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15972step0 raw15972; decide +kernel
      have hl : raw15972step0Labels = raw15972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15972 raw15972Labels permutation520 hz
    mixedMoment B raw15972step0 raw15972step0Labels = mixedMoment B raw15972step1 raw15972step1Labels := by
      have ha : raw15972step1 = (fun i j => raw15972step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw15972step1 raw15972step0; decide +kernel
      have hl : raw15972step1Labels = raw15972step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15972step0 raw15972step0Labels permutation145 permutation3
    mixedMoment B raw15972step1 raw15972step1Labels = mixedMoment B raw15972step2 raw15972step2Labels := by
      have ha : raw15972step2 = -raw15972step1 := by apply Matrix.ext; change ∀ i j, raw15972step2 i j = -(raw15972step1 i j); unfold raw15972step2 raw15972step1; decide +kernel
      have hl : raw15972step2Labels = raw15972step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw15973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15973step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15973step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15973step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15973step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15973step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15973 raw15973Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw15973 raw15973Labels = mixedMoment B raw15973step0 raw15973step0Labels := by
      have ha : raw15973step0 = (fun i j => raw15973 (permutation305 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15973step0 raw15973; decide +kernel
      have hl : raw15973step0Labels = raw15973Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15973 raw15973Labels permutation305 permutation5
    mixedMoment B raw15973step0 raw15973step0Labels = mixedMoment B raw15973step1 raw15973step1Labels := by
      have ha : raw15973step1 = -raw15973step0 := by apply Matrix.ext; change ∀ i j, raw15973step1 i j = -(raw15973step0 i j); unfold raw15973step1 raw15973step0; decide +kernel
      have hl : raw15973step1Labels = raw15973step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15973step1 raw15973step1Labels = mixedMoment B raw15973step2 raw15973step2Labels := by
      have ha : raw15973step2 = raw15973step1 := by apply Matrix.ext; unfold raw15973step2 raw15973step1; decide +kernel
      have hl : raw15973step1Labels = labelEmbedding1 ∘ raw15973step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15973step1 raw15973step1Labels raw15973step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2587 node2587Labels := by rfl

def raw15974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15974step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15974step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15974step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15974 raw15974Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw15974 raw15974Labels = mixedMoment B raw15974step0 raw15974step0Labels := by
      have ha : raw15974step0 = (fun i j => raw15974 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15974step0 raw15974; decide +kernel
      have hl : raw15974step0Labels = raw15974Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15974 raw15974Labels permutation188 permutation7
    mixedMoment B raw15974step0 raw15974step0Labels = mixedMoment B raw15974step1 raw15974step1Labels := by
      have ha : raw15974step1 = -raw15974step0 := by apply Matrix.ext; change ∀ i j, raw15974step1 i j = -(raw15974step0 i j); unfold raw15974step1 raw15974step0; decide +kernel
      have hl : raw15974step1Labels = raw15974step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15974step1 raw15974step1Labels = mixedMoment B raw15974step2 raw15974step2Labels := by
      have ha : raw15974step2 = raw15974step1 := by apply Matrix.ext; unfold raw15974step2 raw15974step1; decide +kernel
      have hl : raw15974step1Labels = labelEmbedding1 ∘ raw15974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15974step1 raw15974step1Labels raw15974step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw15975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15975step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15975step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15975step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15975step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15975 raw15975Labels = mixedMoment B node3927 node3927Labels := by
  calc
    mixedMoment B raw15975 raw15975Labels = mixedMoment B raw15975step0 raw15975step0Labels := by
      have ha : raw15975step0 = (fun i j => raw15975 (permutation305 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15975step0 raw15975; decide +kernel
      have hl : raw15975step0Labels = raw15975Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15975 raw15975Labels permutation305 permutation5
    mixedMoment B raw15975step0 raw15975step0Labels = mixedMoment B raw15975step1 raw15975step1Labels := by
      have ha : raw15975step1 = -raw15975step0 := by apply Matrix.ext; change ∀ i j, raw15975step1 i j = -(raw15975step0 i j); unfold raw15975step1 raw15975step0; decide +kernel
      have hl : raw15975step1Labels = raw15975step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15975step1 raw15975step1Labels = mixedMoment B raw15975step2 raw15975step2Labels := by
      have ha : raw15975step2 = raw15975step1 := by apply Matrix.ext; unfold raw15975step2 raw15975step1; decide +kernel
      have hl : raw15975step1Labels = labelEmbedding1 ∘ raw15975step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15975step1 raw15975step1Labels raw15975step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3927 node3927Labels := by rfl

def raw15976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15976step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15976step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15976step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15976 raw15976Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw15976 raw15976Labels = mixedMoment B raw15976step0 raw15976step0Labels := by
      have hz : ∀ j, raw15976 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15976step0 = (fun i j => raw15976 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15976step0 raw15976; decide +kernel
      have hl : raw15976step0Labels = raw15976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15976 raw15976Labels permutation520 hz
    mixedMoment B raw15976step0 raw15976step0Labels = mixedMoment B raw15976step1 raw15976step1Labels := by
      have ha : raw15976step1 = (fun i j => raw15976step0 (permutation68 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15976step1 raw15976step0; decide +kernel
      have hl : raw15976step1Labels = raw15976step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15976step0 raw15976step0Labels permutation68 permutation5
    mixedMoment B raw15976step1 raw15976step1Labels = mixedMoment B raw15976step2 raw15976step2Labels := by
      have ha : raw15976step2 = -raw15976step1 := by apply Matrix.ext; change ∀ i j, raw15976step2 i j = -(raw15976step1 i j); unfold raw15976step2 raw15976step1; decide +kernel
      have hl : raw15976step2Labels = raw15976step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15976step2 raw15976step2Labels = mixedMoment B raw15976step3 raw15976step3Labels := by
      have ha : raw15976step3 = raw15976step2 := by apply Matrix.ext; unfold raw15976step3 raw15976step2; decide +kernel
      have hl : raw15976step2Labels = labelEmbedding1 ∘ raw15976step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15976step2 raw15976step2Labels raw15976step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw15977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15977step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15977step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15977step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15977step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15977step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15977 raw15977Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw15977 raw15977Labels = mixedMoment B raw15977step0 raw15977step0Labels := by
      have ha : raw15977step0 = (fun i j => raw15977 (permutation318 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15977step0 raw15977; decide +kernel
      have hl : raw15977step0Labels = raw15977Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15977 raw15977Labels permutation318 permutation5
    mixedMoment B raw15977step0 raw15977step0Labels = mixedMoment B raw15977step1 raw15977step1Labels := by
      have ha : raw15977step1 = -raw15977step0 := by apply Matrix.ext; change ∀ i j, raw15977step1 i j = -(raw15977step0 i j); unfold raw15977step1 raw15977step0; decide +kernel
      have hl : raw15977step1Labels = raw15977step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15977step1 raw15977step1Labels = mixedMoment B raw15977step2 raw15977step2Labels := by
      have ha : raw15977step2 = raw15977step1 := by apply Matrix.ext; unfold raw15977step2 raw15977step1; decide +kernel
      have hl : raw15977step1Labels = labelEmbedding1 ∘ raw15977step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15977step1 raw15977step1Labels raw15977step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw15978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15978step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15978step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15978step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15978step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15978 raw15978Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw15978 raw15978Labels = mixedMoment B raw15978step0 raw15978step0Labels := by
      have ha : raw15978step0 = (fun i j => raw15978 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15978step0 raw15978; decide +kernel
      have hl : raw15978step0Labels = raw15978Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15978 raw15978Labels permutation188 permutation7
    mixedMoment B raw15978step0 raw15978step0Labels = mixedMoment B raw15978step1 raw15978step1Labels := by
      have ha : raw15978step1 = -raw15978step0 := by apply Matrix.ext; change ∀ i j, raw15978step1 i j = -(raw15978step0 i j); unfold raw15978step1 raw15978step0; decide +kernel
      have hl : raw15978step1Labels = raw15978step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15978step1 raw15978step1Labels = mixedMoment B raw15978step2 raw15978step2Labels := by
      have ha : raw15978step2 = raw15978step1 := by apply Matrix.ext; unfold raw15978step2 raw15978step1; decide +kernel
      have hl : raw15978step1Labels = labelEmbedding1 ∘ raw15978step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15978step1 raw15978step1Labels raw15978step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

def raw15979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15979step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15979step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15979step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15979 raw15979Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw15979 raw15979Labels = mixedMoment B raw15979step0 raw15979step0Labels := by
      have ha : raw15979step0 = (fun i j => raw15979 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15979step0 raw15979; decide +kernel
      have hl : raw15979step0Labels = raw15979Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15979 raw15979Labels permutation188 permutation7
    mixedMoment B raw15979step0 raw15979step0Labels = mixedMoment B raw15979step1 raw15979step1Labels := by
      have ha : raw15979step1 = -raw15979step0 := by apply Matrix.ext; change ∀ i j, raw15979step1 i j = -(raw15979step0 i j); unfold raw15979step1 raw15979step0; decide +kernel
      have hl : raw15979step1Labels = raw15979step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15979step1 raw15979step1Labels = mixedMoment B raw15979step2 raw15979step2Labels := by
      have ha : raw15979step2 = raw15979step1 := by apply Matrix.ext; unfold raw15979step2 raw15979step1; decide +kernel
      have hl : raw15979step1Labels = labelEmbedding1 ∘ raw15979step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15979step1 raw15979step1Labels raw15979step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw15980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15980step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15980step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15980step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15980 raw15980Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw15980 raw15980Labels = mixedMoment B raw15980step0 raw15980step0Labels := by
      have ha : raw15980step0 = (fun i j => raw15980 (permutation190 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15980step0 raw15980; decide +kernel
      have hl : raw15980step0Labels = raw15980Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15980 raw15980Labels permutation190 permutation7
    mixedMoment B raw15980step0 raw15980step0Labels = mixedMoment B raw15980step1 raw15980step1Labels := by
      have ha : raw15980step1 = -raw15980step0 := by apply Matrix.ext; change ∀ i j, raw15980step1 i j = -(raw15980step0 i j); unfold raw15980step1 raw15980step0; decide +kernel
      have hl : raw15980step1Labels = raw15980step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15980step1 raw15980step1Labels = mixedMoment B raw15980step2 raw15980step2Labels := by
      have ha : raw15980step2 = raw15980step1 := by apply Matrix.ext; unfold raw15980step2 raw15980step1; decide +kernel
      have hl : raw15980step1Labels = labelEmbedding1 ∘ raw15980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15980step1 raw15980step1Labels raw15980step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw15981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw15981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw15981step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15981 raw15981Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw15981 raw15981Labels = mixedMoment B raw15981step0 raw15981step0Labels := by
      have hz : ∀ j, raw15981 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15981step0 = (fun i j => raw15981 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15981step0 raw15981; decide +kernel
      have hl : raw15981step0Labels = raw15981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15981 raw15981Labels permutation520 hz
    mixedMoment B raw15981step0 raw15981step0Labels = mixedMoment B raw15981step1 raw15981step1Labels := by
      have ha : raw15981step1 = (fun i j => raw15981step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15981step1 raw15981step0; decide +kernel
      have hl : raw15981step1Labels = raw15981step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15981step0 raw15981step0Labels permutation38 permutation7
    mixedMoment B raw15981step1 raw15981step1Labels = mixedMoment B raw15981step2 raw15981step2Labels := by
      have ha : raw15981step2 = -raw15981step1 := by apply Matrix.ext; change ∀ i j, raw15981step2 i j = -(raw15981step1 i j); unfold raw15981step2 raw15981step1; decide +kernel
      have hl : raw15981step2Labels = raw15981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15981step2 raw15981step2Labels = mixedMoment B raw15981step3 raw15981step3Labels := by
      have ha : raw15981step3 = raw15981step2 := by apply Matrix.ext; unfold raw15981step3 raw15981step2; decide +kernel
      have hl : raw15981step2Labels = labelEmbedding1 ∘ raw15981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15981step2 raw15981step2Labels raw15981step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw15982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw15982step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15982step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15982step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw15982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15982 raw15982Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw15982 raw15982Labels = mixedMoment B raw15982step0 raw15982step0Labels := by
      have ha : raw15982step0 = (fun i j => raw15982 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15982step0 raw15982; decide +kernel
      have hl : raw15982step0Labels = raw15982Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15982 raw15982Labels permutation188 permutation7
    mixedMoment B raw15982step0 raw15982step0Labels = mixedMoment B raw15982step1 raw15982step1Labels := by
      have ha : raw15982step1 = -raw15982step0 := by apply Matrix.ext; change ∀ i j, raw15982step1 i j = -(raw15982step0 i j); unfold raw15982step1 raw15982step0; decide +kernel
      have hl : raw15982step1Labels = raw15982step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15982step1 raw15982step1Labels = mixedMoment B raw15982step2 raw15982step2Labels := by
      have ha : raw15982step2 = raw15982step1 := by apply Matrix.ext; unfold raw15982step2 raw15982step1; decide +kernel
      have hl : raw15982step1Labels = labelEmbedding1 ∘ raw15982step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15982step1 raw15982step1Labels raw15982step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw15983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15983step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15983step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15983step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15983step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15983 raw15983Labels = mixedMoment B node3568 node3568Labels := by
  calc
    mixedMoment B raw15983 raw15983Labels = mixedMoment B raw15983step0 raw15983step0Labels := by
      have ha : raw15983step0 = (fun i j => raw15983 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15983step0 raw15983; decide +kernel
      have hl : raw15983step0Labels = raw15983Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15983 raw15983Labels permutation188 permutation7
    mixedMoment B raw15983step0 raw15983step0Labels = mixedMoment B raw15983step1 raw15983step1Labels := by
      have ha : raw15983step1 = -raw15983step0 := by apply Matrix.ext; change ∀ i j, raw15983step1 i j = -(raw15983step0 i j); unfold raw15983step1 raw15983step0; decide +kernel
      have hl : raw15983step1Labels = raw15983step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15983step1 raw15983step1Labels = mixedMoment B raw15983step2 raw15983step2Labels := by
      have ha : raw15983step2 = raw15983step1 := by apply Matrix.ext; unfold raw15983step2 raw15983step1; decide +kernel
      have hl : raw15983step1Labels = labelEmbedding1 ∘ raw15983step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15983step1 raw15983step1Labels raw15983step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3568 node3568Labels := by rfl

def raw15984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw15984step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15984step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15984step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw15984step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15984 raw15984Labels = mixedMoment B node2537 node2537Labels := by
  calc
    mixedMoment B raw15984 raw15984Labels = mixedMoment B raw15984step0 raw15984step0Labels := by
      have ha : raw15984step0 = (fun i j => raw15984 (permutation308 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15984step0 raw15984; decide +kernel
      have hl : raw15984step0Labels = raw15984Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15984 raw15984Labels permutation308 permutation5
    mixedMoment B raw15984step0 raw15984step0Labels = mixedMoment B raw15984step1 raw15984step1Labels := by
      have ha : raw15984step1 = -raw15984step0 := by apply Matrix.ext; change ∀ i j, raw15984step1 i j = -(raw15984step0 i j); unfold raw15984step1 raw15984step0; decide +kernel
      have hl : raw15984step1Labels = raw15984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15984step1 raw15984step1Labels = mixedMoment B raw15984step2 raw15984step2Labels := by
      have ha : raw15984step2 = raw15984step1 := by apply Matrix.ext; unfold raw15984step2 raw15984step1; decide +kernel
      have hl : raw15984step1Labels = labelEmbedding1 ∘ raw15984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15984step1 raw15984step1Labels raw15984step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2537 node2537Labels := by rfl

def raw15985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 2, -1], ![-1, -1, 2]]
def raw15985step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw15985step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15985step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw15985step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15985 raw15985Labels = mixedMoment B node3879 node3879Labels := by
  calc
    mixedMoment B raw15985 raw15985Labels = mixedMoment B raw15985step0 raw15985step0Labels := by
      have ha : raw15985step0 = (fun i j => raw15985 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15985step0 raw15985; decide +kernel
      have hl : raw15985step0Labels = raw15985Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15985 raw15985Labels permutation188 permutation7
    mixedMoment B raw15985step0 raw15985step0Labels = mixedMoment B raw15985step1 raw15985step1Labels := by
      have ha : raw15985step1 = -raw15985step0 := by apply Matrix.ext; change ∀ i j, raw15985step1 i j = -(raw15985step0 i j); unfold raw15985step1 raw15985step0; decide +kernel
      have hl : raw15985step1Labels = raw15985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15985step1 raw15985step1Labels = mixedMoment B raw15985step2 raw15985step2Labels := by
      have ha : raw15985step2 = raw15985step1 := by apply Matrix.ext; unfold raw15985step2 raw15985step1; decide +kernel
      have hl : raw15985step1Labels = labelEmbedding1 ∘ raw15985step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15985step1 raw15985step1Labels raw15985step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3879 node3879Labels := by rfl

def raw15986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw15986step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15986 raw15986Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw15986 raw15986Labels = mixedMoment B raw15986step0 raw15986step0Labels := by
      have hz : ∀ j, raw15986 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15986step0 = (fun i j => raw15986 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15986step0 raw15986; decide +kernel
      have hl : raw15986step0Labels = raw15986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15986 raw15986Labels permutation520 hz
    mixedMoment B raw15986step0 raw15986step0Labels = mixedMoment B raw15986step1 raw15986step1Labels := by
      have ha : raw15986step1 = (fun i j => raw15986step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15986step1 raw15986step0; decide +kernel
      have hl : raw15986step1Labels = raw15986step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15986step0 raw15986step0Labels permutation38 permutation7
    mixedMoment B raw15986step1 raw15986step1Labels = mixedMoment B raw15986step2 raw15986step2Labels := by
      have ha : raw15986step2 = -raw15986step1 := by apply Matrix.ext; change ∀ i j, raw15986step2 i j = -(raw15986step1 i j); unfold raw15986step2 raw15986step1; decide +kernel
      have hl : raw15986step2Labels = raw15986step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15986step2 raw15986step2Labels = mixedMoment B raw15986step3 raw15986step3Labels := by
      have ha : raw15986step3 = raw15986step2 := by apply Matrix.ext; unfold raw15986step3 raw15986step2; decide +kernel
      have hl : raw15986step2Labels = labelEmbedding1 ∘ raw15986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15986step2 raw15986step2Labels raw15986step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw15987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw15987step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15987step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw15987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15987 raw15987Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw15987 raw15987Labels = mixedMoment B raw15987step0 raw15987step0Labels := by
      have ha : raw15987step0 = (fun i j => raw15987 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15987step0 raw15987; decide +kernel
      have hl : raw15987step0Labels = raw15987Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15987 raw15987Labels permutation188 permutation7
    mixedMoment B raw15987step0 raw15987step0Labels = mixedMoment B raw15987step1 raw15987step1Labels := by
      have ha : raw15987step1 = -raw15987step0 := by apply Matrix.ext; change ∀ i j, raw15987step1 i j = -(raw15987step0 i j); unfold raw15987step1 raw15987step0; decide +kernel
      have hl : raw15987step1Labels = raw15987step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15987step1 raw15987step1Labels = mixedMoment B raw15987step2 raw15987step2Labels := by
      have ha : raw15987step2 = raw15987step1 := by apply Matrix.ext; unfold raw15987step2 raw15987step1; decide +kernel
      have hl : raw15987step1Labels = labelEmbedding1 ∘ raw15987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15987step1 raw15987step1Labels raw15987step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw15988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15988step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15988step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15988step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15988 raw15988Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw15988 raw15988Labels = mixedMoment B raw15988step0 raw15988step0Labels := by
      have ha : raw15988step0 = (fun i j => raw15988 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15988step0 raw15988; decide +kernel
      have hl : raw15988step0Labels = raw15988Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15988 raw15988Labels permutation188 permutation7
    mixedMoment B raw15988step0 raw15988step0Labels = mixedMoment B raw15988step1 raw15988step1Labels := by
      have ha : raw15988step1 = -raw15988step0 := by apply Matrix.ext; change ∀ i j, raw15988step1 i j = -(raw15988step0 i j); unfold raw15988step1 raw15988step0; decide +kernel
      have hl : raw15988step1Labels = raw15988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15988step1 raw15988step1Labels = mixedMoment B raw15988step2 raw15988step2Labels := by
      have ha : raw15988step2 = raw15988step1 := by apply Matrix.ext; unfold raw15988step2 raw15988step1; decide +kernel
      have hl : raw15988step1Labels = labelEmbedding1 ∘ raw15988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15988step1 raw15988step1Labels raw15988step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw15989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw15989step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15989step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw15989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15989 raw15989Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw15989 raw15989Labels = mixedMoment B raw15989step0 raw15989step0Labels := by
      have ha : raw15989step0 = (fun i j => raw15989 (permutation271 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15989step0 raw15989; decide +kernel
      have hl : raw15989step0Labels = raw15989Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15989 raw15989Labels permutation271 permutation5
    mixedMoment B raw15989step0 raw15989step0Labels = mixedMoment B raw15989step1 raw15989step1Labels := by
      have ha : raw15989step1 = -raw15989step0 := by apply Matrix.ext; change ∀ i j, raw15989step1 i j = -(raw15989step0 i j); unfold raw15989step1 raw15989step0; decide +kernel
      have hl : raw15989step1Labels = raw15989step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15989step1 raw15989step1Labels = mixedMoment B raw15989step2 raw15989step2Labels := by
      have ha : raw15989step2 = raw15989step1 := by apply Matrix.ext; unfold raw15989step2 raw15989step1; decide +kernel
      have hl : raw15989step1Labels = labelEmbedding1 ∘ raw15989step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15989step1 raw15989step1Labels raw15989step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw15990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw15990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15990step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15990step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15990step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15990 raw15990Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw15990 raw15990Labels = mixedMoment B raw15990step0 raw15990step0Labels := by
      have ha : raw15990step0 = (fun i j => raw15990 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15990step0 raw15990; decide +kernel
      have hl : raw15990step0Labels = raw15990Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15990 raw15990Labels permutation188 permutation7
    mixedMoment B raw15990step0 raw15990step0Labels = mixedMoment B raw15990step1 raw15990step1Labels := by
      have ha : raw15990step1 = -raw15990step0 := by apply Matrix.ext; change ∀ i j, raw15990step1 i j = -(raw15990step0 i j); unfold raw15990step1 raw15990step0; decide +kernel
      have hl : raw15990step1Labels = raw15990step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15990step1 raw15990step1Labels = mixedMoment B raw15990step2 raw15990step2Labels := by
      have ha : raw15990step2 = raw15990step1 := by apply Matrix.ext; unfold raw15990step2 raw15990step1; decide +kernel
      have hl : raw15990step1Labels = labelEmbedding1 ∘ raw15990step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15990step1 raw15990step1Labels raw15990step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw15991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw15991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw15991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw15991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15991step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw15991step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15991 raw15991Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw15991 raw15991Labels = mixedMoment B raw15991step0 raw15991step0Labels := by
      have hz : ∀ j, raw15991 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw15991step0 = (fun i j => raw15991 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw15991step0 raw15991; decide +kernel
      have hl : raw15991step0Labels = raw15991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw15991 raw15991Labels permutation520 hz
    mixedMoment B raw15991step0 raw15991step0Labels = mixedMoment B raw15991step1 raw15991step1Labels := by
      have ha : raw15991step1 = (fun i j => raw15991step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15991step1 raw15991step0; decide +kernel
      have hl : raw15991step1Labels = raw15991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15991step0 raw15991step0Labels permutation38 permutation7
    mixedMoment B raw15991step1 raw15991step1Labels = mixedMoment B raw15991step2 raw15991step2Labels := by
      have ha : raw15991step2 = -raw15991step1 := by apply Matrix.ext; change ∀ i j, raw15991step2 i j = -(raw15991step1 i j); unfold raw15991step2 raw15991step1; decide +kernel
      have hl : raw15991step2Labels = raw15991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15991step2 raw15991step2Labels = mixedMoment B raw15991step3 raw15991step3Labels := by
      have ha : raw15991step3 = raw15991step2 := by apply Matrix.ext; unfold raw15991step3 raw15991step2; decide +kernel
      have hl : raw15991step2Labels = labelEmbedding1 ∘ raw15991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15991step2 raw15991step2Labels raw15991step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw15992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw15992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw15992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15992step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw15992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15992 raw15992Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw15992 raw15992Labels = mixedMoment B raw15992step0 raw15992step0Labels := by
      have ha : raw15992step0 = (fun i j => raw15992 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15992step0 raw15992; decide +kernel
      have hl : raw15992step0Labels = raw15992Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15992 raw15992Labels permutation188 permutation7
    mixedMoment B raw15992step0 raw15992step0Labels = mixedMoment B raw15992step1 raw15992step1Labels := by
      have ha : raw15992step1 = -raw15992step0 := by apply Matrix.ext; change ∀ i j, raw15992step1 i j = -(raw15992step0 i j); unfold raw15992step1 raw15992step0; decide +kernel
      have hl : raw15992step1Labels = raw15992step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15992step1 raw15992step1Labels = mixedMoment B raw15992step2 raw15992step2Labels := by
      have ha : raw15992step2 = raw15992step1 := by apply Matrix.ext; unfold raw15992step2 raw15992step1; decide +kernel
      have hl : raw15992step1Labels = labelEmbedding1 ∘ raw15992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15992step1 raw15992step1Labels raw15992step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw15993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw15993step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15993step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw15993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15993 raw15993Labels = mixedMoment B node3536 node3536Labels := by
  calc
    mixedMoment B raw15993 raw15993Labels = mixedMoment B raw15993step0 raw15993step0Labels := by
      have ha : raw15993step0 = (fun i j => raw15993 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw15993step0 raw15993; decide +kernel
      have hl : raw15993step0Labels = raw15993Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15993 raw15993Labels permutation188 permutation7
    mixedMoment B raw15993step0 raw15993step0Labels = mixedMoment B raw15993step1 raw15993step1Labels := by
      have ha : raw15993step1 = -raw15993step0 := by apply Matrix.ext; change ∀ i j, raw15993step1 i j = -(raw15993step0 i j); unfold raw15993step1 raw15993step0; decide +kernel
      have hl : raw15993step1Labels = raw15993step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15993step1 raw15993step1Labels = mixedMoment B raw15993step2 raw15993step2Labels := by
      have ha : raw15993step2 = raw15993step1 := by apply Matrix.ext; unfold raw15993step2 raw15993step1; decide +kernel
      have hl : raw15993step1Labels = labelEmbedding1 ∘ raw15993step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15993step1 raw15993step1Labels raw15993step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3536 node3536Labels := by rfl

def raw15994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw15994step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15994step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw15994step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15994step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw15994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15994 raw15994Labels = mixedMoment B node2535 node2535Labels := by
  calc
    mixedMoment B raw15994 raw15994Labels = mixedMoment B raw15994step0 raw15994step0Labels := by
      have ha : raw15994step0 = (fun i j => raw15994 (permutation306 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15994step0 raw15994; decide +kernel
      have hl : raw15994step0Labels = raw15994Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15994 raw15994Labels permutation306 permutation5
    mixedMoment B raw15994step0 raw15994step0Labels = mixedMoment B raw15994step1 raw15994step1Labels := by
      have ha : raw15994step1 = -raw15994step0 := by apply Matrix.ext; change ∀ i j, raw15994step1 i j = -(raw15994step0 i j); unfold raw15994step1 raw15994step0; decide +kernel
      have hl : raw15994step1Labels = raw15994step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15994step1 raw15994step1Labels = mixedMoment B raw15994step2 raw15994step2Labels := by
      have ha : raw15994step2 = raw15994step1 := by apply Matrix.ext; unfold raw15994step2 raw15994step1; decide +kernel
      have hl : raw15994step1Labels = labelEmbedding1 ∘ raw15994step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15994step1 raw15994step1Labels raw15994step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2535 node2535Labels := by rfl

def raw15995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15995step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15995step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15995 raw15995Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw15995 raw15995Labels = mixedMoment B raw15995step0 raw15995step0Labels := by
      have ha : raw15995step0 = (fun i j => raw15995 (permutation581 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15995step0 raw15995; decide +kernel
      have hl : raw15995step0Labels = raw15995Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15995 raw15995Labels permutation581 permutation5
    mixedMoment B raw15995step0 raw15995step0Labels = mixedMoment B raw15995step1 raw15995step1Labels := by
      have ha : raw15995step1 = raw15995step0 := by apply Matrix.ext; unfold raw15995step1 raw15995step0; decide +kernel
      have hl : raw15995step0Labels = labelEmbedding1 ∘ raw15995step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15995step0 raw15995step0Labels raw15995step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw15996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw15996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw15996step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15996step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw15996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15996 raw15996Labels = mixedMoment B node3743 node3743Labels := by
  calc
    mixedMoment B raw15996 raw15996Labels = mixedMoment B raw15996step0 raw15996step0Labels := by
      have ha : raw15996step0 = (fun i j => raw15996 (permutation580 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15996step0 raw15996; decide +kernel
      have hl : raw15996step0Labels = raw15996Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15996 raw15996Labels permutation580 permutation5
    mixedMoment B raw15996step0 raw15996step0Labels = mixedMoment B raw15996step1 raw15996step1Labels := by
      have ha : raw15996step1 = raw15996step0 := by apply Matrix.ext; unfold raw15996step1 raw15996step0; decide +kernel
      have hl : raw15996step0Labels = labelEmbedding1 ∘ raw15996step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15996step0 raw15996step0Labels raw15996step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3743 node3743Labels := by rfl

def raw15997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw15997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15997step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw15997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15997 raw15997Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw15997 raw15997Labels = mixedMoment B raw15997step0 raw15997step0Labels := by
      have ha : raw15997step0 = (fun i j => raw15997 (permutation548 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15997step0 raw15997; decide +kernel
      have hl : raw15997step0Labels = raw15997Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15997 raw15997Labels permutation548 permutation5
    mixedMoment B raw15997step0 raw15997step0Labels = mixedMoment B raw15997step1 raw15997step1Labels := by
      have ha : raw15997step1 = raw15997step0 := by apply Matrix.ext; unfold raw15997step1 raw15997step0; decide +kernel
      have hl : raw15997step0Labels = labelEmbedding1 ∘ raw15997step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15997step0 raw15997step0Labels raw15997step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw15998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw15998step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw15998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15998 raw15998Labels = mixedMoment B node3434 node3434Labels := by
  calc
    mixedMoment B raw15998 raw15998Labels = mixedMoment B raw15998step0 raw15998step0Labels := by
      have ha : raw15998step0 = (fun i j => raw15998 (permutation681 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15998step0 raw15998; decide +kernel
      have hl : raw15998step0Labels = raw15998Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15998 raw15998Labels permutation681 permutation5
    mixedMoment B raw15998step0 raw15998step0Labels = mixedMoment B raw15998step1 raw15998step1Labels := by
      have ha : raw15998step1 = raw15998step0 := by apply Matrix.ext; unfold raw15998step1 raw15998step0; decide +kernel
      have hl : raw15998step0Labels = labelEmbedding1 ∘ raw15998step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15998step0 raw15998step0Labels raw15998step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3434 node3434Labels := by rfl

def raw15999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw15999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw15999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw15999step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw15999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw15999step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw15999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical15999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw15999 raw15999Labels = mixedMoment B node2534 node2534Labels := by
  calc
    mixedMoment B raw15999 raw15999Labels = mixedMoment B raw15999step0 raw15999step0Labels := by
      have ha : raw15999step0 = (fun i j => raw15999 (permutation305 i) (permutation5 j)) := by apply Matrix.ext; unfold raw15999step0 raw15999; decide +kernel
      have hl : raw15999step0Labels = raw15999Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw15999 raw15999Labels permutation305 permutation5
    mixedMoment B raw15999step0 raw15999step0Labels = mixedMoment B raw15999step1 raw15999step1Labels := by
      have ha : raw15999step1 = -raw15999step0 := by apply Matrix.ext; change ∀ i j, raw15999step1 i j = -(raw15999step0 i j); unfold raw15999step1 raw15999step0; decide +kernel
      have hl : raw15999step1Labels = raw15999step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw15999step1 raw15999step1Labels = mixedMoment B raw15999step2 raw15999step2Labels := by
      have ha : raw15999step2 = raw15999step1 := by apply Matrix.ext; unfold raw15999step2 raw15999step1; decide +kernel
      have hl : raw15999step1Labels = labelEmbedding1 ∘ raw15999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw15999step1 raw15999step1Labels raw15999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2534 node2534Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
