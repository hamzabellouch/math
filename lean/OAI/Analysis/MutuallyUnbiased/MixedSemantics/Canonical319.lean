import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw40832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw40832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw40832step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40832step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40832 raw40832Labels = mixedMoment B node3723 node3723Labels := by
  calc
    mixedMoment B raw40832 raw40832Labels = mixedMoment B raw40832step0 raw40832step0Labels := by
      have ha : raw40832step0 = (fun i j => raw40832 (permutation439 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40832step0 raw40832; decide +kernel
      have hl : raw40832step0Labels = raw40832Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40832 raw40832Labels permutation439 permutation6
    mixedMoment B raw40832step0 raw40832step0Labels = mixedMoment B raw40832step1 raw40832step1Labels := by
      have ha : raw40832step1 = -raw40832step0 := by apply Matrix.ext; change ∀ i j, raw40832step1 i j = -(raw40832step0 i j); unfold raw40832step1 raw40832step0; decide +kernel
      have hl : raw40832step1Labels = raw40832step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3723 node3723Labels := by rfl

def raw40833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40833step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40833 raw40833Labels = mixedMoment B node3715 node3715Labels := by
  calc
    mixedMoment B raw40833 raw40833Labels = mixedMoment B raw40833step0 raw40833step0Labels := by
      have ha : raw40833step0 = (fun i j => raw40833 (permutation422 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40833step0 raw40833; decide +kernel
      have hl : raw40833step0Labels = raw40833Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40833 raw40833Labels permutation422 permutation6
    _ = mixedMoment B node3715 node3715Labels := by rfl

def raw40834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40834step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40834 raw40834Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw40834 raw40834Labels = mixedMoment B raw40834step0 raw40834step0Labels := by
      have ha : raw40834step0 = (fun i j => raw40834 (permutation387 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40834step0 raw40834; decide +kernel
      have hl : raw40834step0Labels = raw40834Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40834 raw40834Labels permutation387 permutation6
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw40835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40835step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40835step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40835 raw40835Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw40835 raw40835Labels = mixedMoment B raw40835step0 raw40835step0Labels := by
      have ha : raw40835step0 = (fun i j => raw40835 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40835step0 raw40835; decide +kernel
      have hl : raw40835step0Labels = raw40835Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40835 raw40835Labels permutation682 permutation3
    mixedMoment B raw40835step0 raw40835step0Labels = mixedMoment B raw40835step1 raw40835step1Labels := by
      have ha : raw40835step1 = -raw40835step0 := by apply Matrix.ext; change ∀ i j, raw40835step1 i j = -(raw40835step0 i j); unfold raw40835step1 raw40835step0; decide +kernel
      have hl : raw40835step1Labels = raw40835step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3030 node3030Labels := by rfl

def raw40836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40836step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw40836step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40836step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40836 raw40836Labels = mixedMoment B node3378 node3378Labels := by
  calc
    mixedMoment B raw40836 raw40836Labels = mixedMoment B raw40836step0 raw40836step0Labels := by
      have ha : raw40836step0 = (fun i j => raw40836 (permutation520 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40836step0 raw40836; decide +kernel
      have hl : raw40836step0Labels = raw40836Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40836 raw40836Labels permutation520 permutation6
    mixedMoment B raw40836step0 raw40836step0Labels = mixedMoment B raw40836step1 raw40836step1Labels := by
      have ha : raw40836step1 = -raw40836step0 := by apply Matrix.ext; change ∀ i j, raw40836step1 i j = -(raw40836step0 i j); unfold raw40836step1 raw40836step0; decide +kernel
      have hl : raw40836step1Labels = raw40836step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3378 node3378Labels := by rfl

def raw40837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw40837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40837 raw40837Labels = mixedMoment B node2930 node2930Labels := by
  calc
    mixedMoment B raw40837 raw40837Labels = mixedMoment B raw40837step0 raw40837step0Labels := by
      have hz : ∀ j, raw40837 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40837step0 = (fun i j => raw40837 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40837step0 raw40837; decide +kernel
      have hl : raw40837step0Labels = raw40837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40837 raw40837Labels permutation434 hz
    mixedMoment B raw40837step0 raw40837step0Labels = mixedMoment B raw40837step1 raw40837step1Labels := by
      have ha : raw40837step1 = (fun i j => raw40837step0 (permutation142 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40837step1 raw40837step0; decide +kernel
      have hl : raw40837step1Labels = raw40837step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40837step0 raw40837step0Labels permutation142 permutation6
    _ = mixedMoment B node2930 node2930Labels := by rfl

def raw40838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40838 raw40838Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw40838 raw40838Labels = mixedMoment B raw40838step0 raw40838step0Labels := by
      have ha : raw40838step0 = (fun i j => raw40838 (permutation632 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40838step0 raw40838; decide +kernel
      have hl : raw40838step0Labels = raw40838Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40838 raw40838Labels permutation632 permutation6
    _ = mixedMoment B node2928 node2928Labels := by rfl

def raw40839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40839step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40839step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40839 raw40839Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw40839 raw40839Labels = mixedMoment B raw40839step0 raw40839step0Labels := by
      have ha : raw40839step0 = (fun i j => raw40839 (permutation633 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40839step0 raw40839; decide +kernel
      have hl : raw40839step0Labels = raw40839Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40839 raw40839Labels permutation633 permutation6
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw40840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40840step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40840step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40840step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw40840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40840 raw40840Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw40840 raw40840Labels = mixedMoment B raw40840step0 raw40840step0Labels := by
      have hz : ∀ j, raw40840 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40840step0 = (fun i j => raw40840 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40840step0 raw40840; decide +kernel
      have hl : raw40840step0Labels = raw40840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40840 raw40840Labels permutation434 hz
    mixedMoment B raw40840step0 raw40840step0Labels = mixedMoment B raw40840step1 raw40840step1Labels := by
      have hz : ∀ j, raw40840step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40840step1 = (fun i j => raw40840step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40840step1 raw40840step0; decide +kernel
      have hl : raw40840step1Labels = raw40840step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40840step0 raw40840step0Labels permutation80 hz
    mixedMoment B raw40840step1 raw40840step1Labels = mixedMoment B raw40840step2 raw40840step2Labels := by
      have ha : raw40840step2 = (fun i j => raw40840step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40840step2 raw40840step1; decide +kernel
      have hl : raw40840step2Labels = raw40840step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40840step1 raw40840step1Labels permutation28 permutation6
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw40841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40841 raw40841Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw40841 raw40841Labels = mixedMoment B raw40841step0 raw40841step0Labels := by
      have hz : ∀ j, raw40841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40841step0 = (fun i j => raw40841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40841step0 raw40841; decide +kernel
      have hl : raw40841step0Labels = raw40841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40841 raw40841Labels permutation346 hz
    mixedMoment B raw40841step0 raw40841step0Labels = mixedMoment B raw40841step1 raw40841step1Labels := by
      have ha : raw40841step1 = (fun i j => raw40841step0 (permutation115 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40841step1 raw40841step0; decide +kernel
      have hl : raw40841step1Labels = raw40841step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40841step0 raw40841step0Labels permutation115 permutation6
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw40842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40842 raw40842Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw40842 raw40842Labels = mixedMoment B raw40842step0 raw40842step0Labels := by
      have hz : ∀ j, raw40842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40842step0 = (fun i j => raw40842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40842step0 raw40842; decide +kernel
      have hl : raw40842step0Labels = raw40842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40842 raw40842Labels permutation346 hz
    mixedMoment B raw40842step0 raw40842step0Labels = mixedMoment B raw40842step1 raw40842step1Labels := by
      have ha : raw40842step1 = (fun i j => raw40842step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40842step1 raw40842step0; decide +kernel
      have hl : raw40842step1Labels = raw40842step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40842step0 raw40842step0Labels permutation137 permutation6
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw40843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40843step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw40843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40843 raw40843Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw40843 raw40843Labels = mixedMoment B raw40843step0 raw40843step0Labels := by
      have hz : ∀ j, raw40843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40843step0 = (fun i j => raw40843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40843step0 raw40843; decide +kernel
      have hl : raw40843step0Labels = raw40843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40843 raw40843Labels permutation346 hz
    mixedMoment B raw40843step0 raw40843step0Labels = mixedMoment B raw40843step1 raw40843step1Labels := by
      have ha : raw40843step1 = (fun i j => raw40843step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40843step1 raw40843step0; decide +kernel
      have hl : raw40843step1Labels = raw40843step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40843step0 raw40843step0Labels permutation124 permutation6
    _ = mixedMoment B node2620 node2620Labels := by rfl

def raw40844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40844 raw40844Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw40844 raw40844Labels = mixedMoment B raw40844step0 raw40844step0Labels := by
      have hz : ∀ j, raw40844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40844step0 = (fun i j => raw40844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40844step0 raw40844; decide +kernel
      have hl : raw40844step0Labels = raw40844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40844 raw40844Labels permutation346 hz
    mixedMoment B raw40844step0 raw40844step0Labels = mixedMoment B raw40844step1 raw40844step1Labels := by
      have ha : raw40844step1 = (fun i j => raw40844step0 (permutation138 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40844step1 raw40844step0; decide +kernel
      have hl : raw40844step1Labels = raw40844step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40844step0 raw40844step0Labels permutation138 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw40845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40845step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40845 raw40845Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw40845 raw40845Labels = mixedMoment B raw40845step0 raw40845step0Labels := by
      have ha : raw40845step0 = (fun i j => raw40845 (permutation577 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40845step0 raw40845; decide +kernel
      have hl : raw40845step0Labels = raw40845Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40845 raw40845Labels permutation577 permutation6
    _ = mixedMoment B node2617 node2617Labels := by rfl

def raw40846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40846step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40846 raw40846Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw40846 raw40846Labels = mixedMoment B raw40846step0 raw40846step0Labels := by
      have ha : raw40846step0 = (fun i j => raw40846 (permutation620 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40846step0 raw40846; decide +kernel
      have hl : raw40846step0Labels = raw40846Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40846 raw40846Labels permutation620 permutation6
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw40847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40847step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40847 raw40847Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw40847 raw40847Labels = mixedMoment B raw40847step0 raw40847step0Labels := by
      have ha : raw40847step0 = (fun i j => raw40847 (permutation492 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40847step0 raw40847; decide +kernel
      have hl : raw40847step0Labels = raw40847Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40847 raw40847Labels permutation492 permutation6
    _ = mixedMoment B node2557 node2557Labels := by rfl

def raw40848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40848step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40848 raw40848Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw40848 raw40848Labels = mixedMoment B raw40848step0 raw40848step0Labels := by
      have ha : raw40848step0 = (fun i j => raw40848 (permutation463 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40848step0 raw40848; decide +kernel
      have hl : raw40848step0Labels = raw40848Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40848 raw40848Labels permutation463 permutation6
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw40849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40849 raw40849Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw40849 raw40849Labels = mixedMoment B raw40849step0 raw40849step0Labels := by
      have ha : raw40849step0 = (fun i j => raw40849 (permutation493 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40849step0 raw40849; decide +kernel
      have hl : raw40849step0Labels = raw40849Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40849 raw40849Labels permutation493 permutation6
    _ = mixedMoment B node2545 node2545Labels := by rfl

def raw40850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw40850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw40850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![3, -3, 0]]
def raw40850step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40850step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -3, 3], ![-1, 1, 0], ![-2, 2, 0]]
def raw40850step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40850step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw40850step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40850 raw40850Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw40850 raw40850Labels = mixedMoment B raw40850step0 raw40850step0Labels := by
      have hz : ∀ j, raw40850 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40850step0 = (fun i j => raw40850 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40850step0 raw40850; decide +kernel
      have hl : raw40850step0Labels = raw40850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40850 raw40850Labels permutation520 hz
    mixedMoment B raw40850step0 raw40850step0Labels = mixedMoment B raw40850step1 raw40850step1Labels := by
      have hz : ∀ j, raw40850step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40850step1 = (fun i j => raw40850step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40850step1 raw40850step0; decide +kernel
      have hl : raw40850step1Labels = raw40850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40850step0 raw40850step0Labels permutation104 hz
    mixedMoment B raw40850step1 raw40850step1Labels = mixedMoment B raw40850step2 raw40850step2Labels := by
      have ha : raw40850step2 = (fun i j => raw40850step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40850step2 raw40850step1; decide +kernel
      have hl : raw40850step2Labels = raw40850step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40850step1 raw40850step1Labels permutation31 permutation3
    mixedMoment B raw40850step2 raw40850step2Labels = mixedMoment B raw40850step3 raw40850step3Labels := by
      have ha : raw40850step3 = -raw40850step2 := by apply Matrix.ext; change ∀ i j, raw40850step3 i j = -(raw40850step2 i j); unfold raw40850step3 raw40850step2; decide +kernel
      have hl : raw40850step3Labels = raw40850step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2284 node2284Labels := by rfl

def raw40851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![3, -2, -1]]
def raw40851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![3, -2, -1]]
def raw40851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40851 raw40851Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw40851 raw40851Labels = mixedMoment B raw40851step0 raw40851step0Labels := by
      have hz : ∀ j, raw40851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40851step0 = (fun i j => raw40851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40851step0 raw40851; decide +kernel
      have hl : raw40851step0Labels = raw40851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40851 raw40851Labels permutation434 hz
    mixedMoment B raw40851step0 raw40851step0Labels = mixedMoment B raw40851step1 raw40851step1Labels := by
      have ha : raw40851step1 = (fun i j => raw40851step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40851step1 raw40851step0; decide +kernel
      have hl : raw40851step1Labels = raw40851step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40851step0 raw40851step0Labels permutation101 permutation6
    _ = mixedMoment B node2133 node2133Labels := by rfl

def raw40852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw40852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![3, -1, -2]]
def raw40852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40852 raw40852Labels = mixedMoment B node1826 node1826Labels := by
  calc
    mixedMoment B raw40852 raw40852Labels = mixedMoment B raw40852step0 raw40852step0Labels := by
      have hz : ∀ j, raw40852 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40852step0 = (fun i j => raw40852 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40852step0 raw40852; decide +kernel
      have hl : raw40852step0Labels = raw40852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40852 raw40852Labels permutation434 hz
    mixedMoment B raw40852step0 raw40852step0Labels = mixedMoment B raw40852step1 raw40852step1Labels := by
      have ha : raw40852step1 = (fun i j => raw40852step0 (permutation100 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40852step1 raw40852step0; decide +kernel
      have hl : raw40852step1Labels = raw40852step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40852step0 raw40852step0Labels permutation100 permutation6
    _ = mixedMoment B node1826 node1826Labels := by rfl

def raw40853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw40853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw40853step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40853step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40853 raw40853Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw40853 raw40853Labels = mixedMoment B raw40853step0 raw40853step0Labels := by
      have hz : ∀ j, raw40853 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40853step0 = (fun i j => raw40853 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40853step0 raw40853; decide +kernel
      have hl : raw40853step0Labels = raw40853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40853 raw40853Labels permutation434 hz
    mixedMoment B raw40853step0 raw40853step0Labels = mixedMoment B raw40853step1 raw40853step1Labels := by
      have ha : raw40853step1 = (fun i j => raw40853step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40853step1 raw40853step0; decide +kernel
      have hl : raw40853step1Labels = raw40853step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40853step0 raw40853step0Labels permutation97 permutation6
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw40854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw40854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw40854step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40854step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40854 raw40854Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw40854 raw40854Labels = mixedMoment B raw40854step0 raw40854step0Labels := by
      have hz : ∀ j, raw40854 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40854step0 = (fun i j => raw40854 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40854step0 raw40854; decide +kernel
      have hl : raw40854step0Labels = raw40854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40854 raw40854Labels permutation434 hz
    mixedMoment B raw40854step0 raw40854step0Labels = mixedMoment B raw40854step1 raw40854step1Labels := by
      have ha : raw40854step1 = (fun i j => raw40854step0 (permutation101 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40854step1 raw40854step0; decide +kernel
      have hl : raw40854step1Labels = raw40854step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40854step0 raw40854step0Labels permutation101 permutation6
    _ = mixedMoment B node2108 node2108Labels := by rfl

def raw40855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw40855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw40855step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40855step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40855 raw40855Labels = mixedMoment B node1809 node1809Labels := by
  calc
    mixedMoment B raw40855 raw40855Labels = mixedMoment B raw40855step0 raw40855step0Labels := by
      have hz : ∀ j, raw40855 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40855step0 = (fun i j => raw40855 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40855step0 raw40855; decide +kernel
      have hl : raw40855step0Labels = raw40855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40855 raw40855Labels permutation434 hz
    mixedMoment B raw40855step0 raw40855step0Labels = mixedMoment B raw40855step1 raw40855step1Labels := by
      have ha : raw40855step1 = (fun i j => raw40855step0 (permutation100 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40855step1 raw40855step0; decide +kernel
      have hl : raw40855step1Labels = raw40855step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40855step0 raw40855step0Labels permutation100 permutation6
    _ = mixedMoment B node1809 node1809Labels := by rfl

def raw40856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw40856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40856 raw40856Labels = mixedMoment B node1824 node1824Labels := by
  calc
    mixedMoment B raw40856 raw40856Labels = mixedMoment B raw40856step0 raw40856step0Labels := by
      have ha : raw40856step0 = (fun i j => raw40856 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40856step0 raw40856; decide +kernel
      have hl : raw40856step0Labels = raw40856Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40856 raw40856Labels permutation421 permutation6
    _ = mixedMoment B node1824 node1824Labels := by rfl

def raw40857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw40857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40857 raw40857Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw40857 raw40857Labels = mixedMoment B raw40857step0 raw40857step0Labels := by
      have ha : raw40857step0 = (fun i j => raw40857 (permutation431 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40857step0 raw40857; decide +kernel
      have hl : raw40857step0Labels = raw40857Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40857 raw40857Labels permutation431 permutation6
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw40858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw40858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40858step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40858 raw40858Labels = mixedMoment B node1806 node1806Labels := by
  calc
    mixedMoment B raw40858 raw40858Labels = mixedMoment B raw40858step0 raw40858step0Labels := by
      have ha : raw40858step0 = (fun i j => raw40858 (permutation421 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40858step0 raw40858; decide +kernel
      have hl : raw40858step0Labels = raw40858Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40858 raw40858Labels permutation421 permutation6
    _ = mixedMoment B node1806 node1806Labels := by rfl

def raw40859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw40859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40859step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40859 raw40859Labels = mixedMoment B node1791 node1791Labels := by
  calc
    mixedMoment B raw40859 raw40859Labels = mixedMoment B raw40859step0 raw40859step0Labels := by
      have ha : raw40859step0 = (fun i j => raw40859 (permutation430 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40859step0 raw40859; decide +kernel
      have hl : raw40859step0Labels = raw40859Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40859 raw40859Labels permutation430 permutation6
    _ = mixedMoment B node1791 node1791Labels := by rfl

def raw40860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw40860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw40860step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw40860step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40860 raw40860Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw40860 raw40860Labels = mixedMoment B raw40860step0 raw40860step0Labels := by
      have hz : ∀ j, raw40860 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40860step0 = (fun i j => raw40860 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40860step0 raw40860; decide +kernel
      have hl : raw40860step0Labels = raw40860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40860 raw40860Labels permutation520 hz
    mixedMoment B raw40860step0 raw40860step0Labels = mixedMoment B raw40860step1 raw40860step1Labels := by
      have ha : raw40860step1 = (fun i j => raw40860step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40860step1 raw40860step0; decide +kernel
      have hl : raw40860step1Labels = raw40860step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40860step0 raw40860step0Labels permutation151 permutation3
    mixedMoment B raw40860step1 raw40860step1Labels = mixedMoment B raw40860step2 raw40860step2Labels := by
      have ha : raw40860step2 = -raw40860step1 := by apply Matrix.ext; change ∀ i j, raw40860step2 i j = -(raw40860step1 i j); unfold raw40860step2 raw40860step1; decide +kernel
      have hl : raw40860step2Labels = raw40860step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw40861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw40861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40861step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw40861step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40861step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40861 raw40861Labels = mixedMoment B node2714 node2714Labels := by
  calc
    mixedMoment B raw40861 raw40861Labels = mixedMoment B raw40861step0 raw40861step0Labels := by
      have ha : raw40861step0 = (fun i j => raw40861 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40861step0 raw40861; decide +kernel
      have hl : raw40861step0Labels = raw40861Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40861 raw40861Labels permutation688 permutation3
    mixedMoment B raw40861step0 raw40861step0Labels = mixedMoment B raw40861step1 raw40861step1Labels := by
      have ha : raw40861step1 = -raw40861step0 := by apply Matrix.ext; change ∀ i j, raw40861step1 i j = -(raw40861step0 i j); unfold raw40861step1 raw40861step0; decide +kernel
      have hl : raw40861step1Labels = raw40861step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2714 node2714Labels := by rfl

def raw40862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw40862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw40862step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40862 raw40862Labels = mixedMoment B node3032 node3032Labels := by
  calc
    mixedMoment B raw40862 raw40862Labels = mixedMoment B raw40862step0 raw40862step0Labels := by
      have ha : raw40862step0 = (fun i j => raw40862 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40862step0 raw40862; decide +kernel
      have hl : raw40862step0Labels = raw40862Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40862 raw40862Labels permutation688 permutation3
    mixedMoment B raw40862step0 raw40862step0Labels = mixedMoment B raw40862step1 raw40862step1Labels := by
      have ha : raw40862step1 = -raw40862step0 := by apply Matrix.ext; change ∀ i j, raw40862step1 i j = -(raw40862step0 i j); unfold raw40862step1 raw40862step0; decide +kernel
      have hl : raw40862step1Labels = raw40862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3032 node3032Labels := by rfl

def raw40863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw40863step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40863 raw40863Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw40863 raw40863Labels = mixedMoment B raw40863step0 raw40863step0Labels := by
      have ha : raw40863step0 = (fun i j => raw40863 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40863step0 raw40863; decide +kernel
      have hl : raw40863step0Labels = raw40863Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40863 raw40863Labels permutation688 permutation3
    mixedMoment B raw40863step0 raw40863step0Labels = mixedMoment B raw40863step1 raw40863step1Labels := by
      have ha : raw40863step1 = -raw40863step0 := by apply Matrix.ext; change ∀ i j, raw40863step1 i j = -(raw40863step0 i j); unfold raw40863step1 raw40863step0; decide +kernel
      have hl : raw40863step1Labels = raw40863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw40864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw40864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40864step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40864 raw40864Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw40864 raw40864Labels = mixedMoment B raw40864step0 raw40864step0Labels := by
      have ha : raw40864step0 = (fun i j => raw40864 (permutation397 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40864step0 raw40864; decide +kernel
      have hl : raw40864step0Labels = raw40864Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40864 raw40864Labels permutation397 permutation6
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw40865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw40865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40865step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40865 raw40865Labels = mixedMoment B node3365 node3365Labels := by
  calc
    mixedMoment B raw40865 raw40865Labels = mixedMoment B raw40865step0 raw40865step0Labels := by
      have ha : raw40865step0 = (fun i j => raw40865 (permutation523 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40865step0 raw40865; decide +kernel
      have hl : raw40865step0Labels = raw40865Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40865 raw40865Labels permutation523 permutation6
    mixedMoment B raw40865step0 raw40865step0Labels = mixedMoment B raw40865step1 raw40865step1Labels := by
      have ha : raw40865step1 = -raw40865step0 := by apply Matrix.ext; change ∀ i j, raw40865step1 i j = -(raw40865step0 i j); unfold raw40865step1 raw40865step0; decide +kernel
      have hl : raw40865step1Labels = raw40865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3365 node3365Labels := by rfl

def raw40866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw40866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw40866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw40866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw40866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40866 raw40866Labels = mixedMoment B node3577 node3577Labels := by
  calc
    mixedMoment B raw40866 raw40866Labels = mixedMoment B raw40866step0 raw40866step0Labels := by
      have hz : ∀ j, raw40866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40866step0 = (fun i j => raw40866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40866step0 raw40866; decide +kernel
      have hl : raw40866step0Labels = raw40866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40866 raw40866Labels permutation434 hz
    mixedMoment B raw40866step0 raw40866step0Labels = mixedMoment B raw40866step1 raw40866step1Labels := by
      have ha : raw40866step1 = (fun i j => raw40866step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40866step1 raw40866step0; decide +kernel
      have hl : raw40866step1Labels = raw40866step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40866step0 raw40866step0Labels permutation151 permutation3
    mixedMoment B raw40866step1 raw40866step1Labels = mixedMoment B raw40866step2 raw40866step2Labels := by
      have ha : raw40866step2 = -raw40866step1 := by apply Matrix.ext; change ∀ i j, raw40866step2 i j = -(raw40866step1 i j); unfold raw40866step2 raw40866step1; decide +kernel
      have hl : raw40866step2Labels = raw40866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3577 node3577Labels := by rfl

def raw40867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw40867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw40867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40867 raw40867Labels = mixedMoment B node2812 node2812Labels := by
  calc
    mixedMoment B raw40867 raw40867Labels = mixedMoment B raw40867step0 raw40867step0Labels := by
      have hz : ∀ j, raw40867 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40867step0 = (fun i j => raw40867 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40867step0 raw40867; decide +kernel
      have hl : raw40867step0Labels = raw40867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40867 raw40867Labels permutation434 hz
    mixedMoment B raw40867step0 raw40867step0Labels = mixedMoment B raw40867step1 raw40867step1Labels := by
      have ha : raw40867step1 = (fun i j => raw40867step0 (permutation142 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40867step1 raw40867step0; decide +kernel
      have hl : raw40867step1Labels = raw40867step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40867step0 raw40867step0Labels permutation142 permutation6
    _ = mixedMoment B node2812 node2812Labels := by rfl

def raw40868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw40868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40868step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40868 raw40868Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw40868 raw40868Labels = mixedMoment B raw40868step0 raw40868step0Labels := by
      have ha : raw40868step0 = (fun i j => raw40868 (permutation412 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40868step0 raw40868; decide +kernel
      have hl : raw40868step0Labels = raw40868Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40868 raw40868Labels permutation412 permutation6
    _ = mixedMoment B node3698 node3698Labels := by rfl

def raw40869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw40869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40869step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40869 raw40869Labels = mixedMoment B node2810 node2810Labels := by
  calc
    mixedMoment B raw40869 raw40869Labels = mixedMoment B raw40869step0 raw40869step0Labels := by
      have ha : raw40869step0 = (fun i j => raw40869 (permutation632 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40869step0 raw40869; decide +kernel
      have hl : raw40869step0Labels = raw40869Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40869 raw40869Labels permutation632 permutation6
    _ = mixedMoment B node2810 node2810Labels := by rfl

def raw40870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw40870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40870 raw40870Labels = mixedMoment B node3674 node3674Labels := by
  calc
    mixedMoment B raw40870 raw40870Labels = mixedMoment B raw40870step0 raw40870step0Labels := by
      have ha : raw40870step0 = (fun i j => raw40870 (permutation411 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40870step0 raw40870; decide +kernel
      have hl : raw40870step0Labels = raw40870Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40870 raw40870Labels permutation411 permutation6
    _ = mixedMoment B node3674 node3674Labels := by rfl

def raw40871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw40871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40871step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40871 raw40871Labels = mixedMoment B node2798 node2798Labels := by
  calc
    mixedMoment B raw40871 raw40871Labels = mixedMoment B raw40871step0 raw40871step0Labels := by
      have ha : raw40871step0 = (fun i j => raw40871 (permutation643 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40871step0 raw40871; decide +kernel
      have hl : raw40871step0Labels = raw40871Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40871 raw40871Labels permutation643 permutation6
    _ = mixedMoment B node2798 node2798Labels := by rfl

def raw40872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw40872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw40872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw40872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40872 raw40872Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw40872 raw40872Labels = mixedMoment B raw40872step0 raw40872step0Labels := by
      have ha : raw40872step0 = (fun i j => raw40872 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40872step0 raw40872; decide +kernel
      have hl : raw40872step0Labels = raw40872Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40872 raw40872Labels permutation640 permutation3
    mixedMoment B raw40872step0 raw40872step0Labels = mixedMoment B raw40872step1 raw40872step1Labels := by
      have ha : raw40872step1 = -raw40872step0 := by apply Matrix.ext; change ∀ i j, raw40872step1 i j = -(raw40872step0 i j); unfold raw40872step1 raw40872step0; decide +kernel
      have hl : raw40872step1Labels = raw40872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2233 node2233Labels := by rfl

def raw40873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw40873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40873step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40873 raw40873Labels = mixedMoment B node2892 node2892Labels := by
  calc
    mixedMoment B raw40873 raw40873Labels = mixedMoment B raw40873step0 raw40873step0Labels := by
      have ha : raw40873step0 = (fun i j => raw40873 (permutation637 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40873step0 raw40873; decide +kernel
      have hl : raw40873step0Labels = raw40873Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40873 raw40873Labels permutation637 permutation6
    _ = mixedMoment B node2892 node2892Labels := by rfl

def raw40874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw40874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw40874step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40874 raw40874Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw40874 raw40874Labels = mixedMoment B raw40874step0 raw40874step0Labels := by
      have hz : ∀ j, raw40874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40874step0 = (fun i j => raw40874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40874step0 raw40874; decide +kernel
      have hl : raw40874step0Labels = raw40874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40874 raw40874Labels permutation434 hz
    mixedMoment B raw40874step0 raw40874step0Labels = mixedMoment B raw40874step1 raw40874step1Labels := by
      have ha : raw40874step1 = (fun i j => raw40874step0 (permutation119 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40874step1 raw40874step0; decide +kernel
      have hl : raw40874step1Labels = raw40874step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40874step0 raw40874step0Labels permutation119 permutation6
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw40875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw40875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 2, -4]]
def raw40875step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40875 raw40875Labels = mixedMoment B node1133 node1133Labels := by
  calc
    mixedMoment B raw40875 raw40875Labels = mixedMoment B raw40875step0 raw40875step0Labels := by
      have hz : ∀ j, raw40875 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40875step0 = (fun i j => raw40875 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40875step0 raw40875; decide +kernel
      have hl : raw40875step0Labels = raw40875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40875 raw40875Labels permutation434 hz
    mixedMoment B raw40875step0 raw40875step0Labels = mixedMoment B raw40875step1 raw40875step1Labels := by
      have ha : raw40875step1 = (fun i j => raw40875step0 (permutation142 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40875step1 raw40875step0; decide +kernel
      have hl : raw40875step1Labels = raw40875step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40875step0 raw40875step0Labels permutation142 permutation6
    _ = mixedMoment B node1133 node1133Labels := by rfl

def raw40876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw40876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40876 raw40876Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw40876 raw40876Labels = mixedMoment B raw40876step0 raw40876step0Labels := by
      have ha : raw40876step0 = (fun i j => raw40876 (permutation550 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40876step0 raw40876; decide +kernel
      have hl : raw40876step0Labels = raw40876Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40876 raw40876Labels permutation550 permutation6
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw40877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw40877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40877step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40877 raw40877Labels = mixedMoment B node1130 node1130Labels := by
  calc
    mixedMoment B raw40877 raw40877Labels = mixedMoment B raw40877step0 raw40877step0Labels := by
      have ha : raw40877step0 = (fun i j => raw40877 (permutation632 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40877step0 raw40877; decide +kernel
      have hl : raw40877step0Labels = raw40877Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40877 raw40877Labels permutation632 permutation6
    _ = mixedMoment B node1130 node1130Labels := by rfl

def raw40878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, 2, -3], ![2, -1, -1]]
def raw40878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40878step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40878 raw40878Labels = mixedMoment B node2438 node2438Labels := by
  calc
    mixedMoment B raw40878 raw40878Labels = mixedMoment B raw40878step0 raw40878step0Labels := by
      have ha : raw40878step0 = (fun i j => raw40878 (permutation549 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40878step0 raw40878; decide +kernel
      have hl : raw40878step0Labels = raw40878Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40878 raw40878Labels permutation549 permutation6
    _ = mixedMoment B node2438 node2438Labels := by rfl

def raw40879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw40879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40879step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40879 raw40879Labels = mixedMoment B node1113 node1113Labels := by
  calc
    mixedMoment B raw40879 raw40879Labels = mixedMoment B raw40879step0 raw40879step0Labels := by
      have ha : raw40879step0 = (fun i j => raw40879 (permutation643 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40879step0 raw40879; decide +kernel
      have hl : raw40879step0Labels = raw40879Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40879 raw40879Labels permutation643 permutation6
    _ = mixedMoment B node1113 node1113Labels := by rfl

def raw40880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw40880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 3, -5]]
def raw40880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40880step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -3, 2], ![2, 3, -5]]
def raw40880step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40880step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw40880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40880 raw40880Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw40880 raw40880Labels = mixedMoment B raw40880step0 raw40880step0Labels := by
      have hz : ∀ j, raw40880 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40880step0 = (fun i j => raw40880 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40880step0 raw40880; decide +kernel
      have hl : raw40880step0Labels = raw40880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40880 raw40880Labels permutation434 hz
    mixedMoment B raw40880step0 raw40880step0Labels = mixedMoment B raw40880step1 raw40880step1Labels := by
      have hz : ∀ j, raw40880step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40880step1 = (fun i j => raw40880step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40880step1 raw40880step0; decide +kernel
      have hl : raw40880step1Labels = raw40880step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40880step0 raw40880step0Labels permutation80 hz
    mixedMoment B raw40880step1 raw40880step1Labels = mixedMoment B raw40880step2 raw40880step2Labels := by
      have ha : raw40880step2 = (fun i j => raw40880step1 (permutation28 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40880step2 raw40880step1; decide +kernel
      have hl : raw40880step2Labels = raw40880step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40880step1 raw40880step1Labels permutation28 permutation6
    _ = mixedMoment B node607 node607Labels := by rfl

def raw40881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw40881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 3, -4], ![2, -2, 0]]
def raw40881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40881step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40881 raw40881Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw40881 raw40881Labels = mixedMoment B raw40881step0 raw40881step0Labels := by
      have hz : ∀ j, raw40881 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40881step0 = (fun i j => raw40881 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40881step0 raw40881; decide +kernel
      have hl : raw40881step0Labels = raw40881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40881 raw40881Labels permutation346 hz
    mixedMoment B raw40881step0 raw40881step0Labels = mixedMoment B raw40881step1 raw40881step1Labels := by
      have ha : raw40881step1 = (fun i j => raw40881step0 (permutation125 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40881step1 raw40881step0; decide +kernel
      have hl : raw40881step1Labels = raw40881step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40881step0 raw40881step0Labels permutation125 permutation6
    _ = mixedMoment B node1058 node1058Labels := by rfl

def raw40882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 3, -5]]
def raw40882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40882step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40882 raw40882Labels = mixedMoment B node604 node604Labels := by
  calc
    mixedMoment B raw40882 raw40882Labels = mixedMoment B raw40882step0 raw40882step0Labels := by
      have hz : ∀ j, raw40882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40882step0 = (fun i j => raw40882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40882step0 raw40882; decide +kernel
      have hl : raw40882step0Labels = raw40882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40882 raw40882Labels permutation346 hz
    mixedMoment B raw40882step0 raw40882step0Labels = mixedMoment B raw40882step1 raw40882step1Labels := by
      have ha : raw40882step1 = (fun i j => raw40882step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40882step1 raw40882step0; decide +kernel
      have hl : raw40882step1Labels = raw40882step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40882step0 raw40882step0Labels permutation137 permutation6
    _ = mixedMoment B node604 node604Labels := by rfl

def raw40883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]
def raw40883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 3, -4], ![2, -1, -1]]
def raw40883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40883 raw40883Labels = mixedMoment B node946 node946Labels := by
  calc
    mixedMoment B raw40883 raw40883Labels = mixedMoment B raw40883step0 raw40883step0Labels := by
      have hz : ∀ j, raw40883 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40883step0 = (fun i j => raw40883 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40883step0 raw40883; decide +kernel
      have hl : raw40883step0Labels = raw40883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40883 raw40883Labels permutation346 hz
    mixedMoment B raw40883step0 raw40883step0Labels = mixedMoment B raw40883step1 raw40883step1Labels := by
      have ha : raw40883step1 = (fun i j => raw40883step0 (permutation124 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40883step1 raw40883step0; decide +kernel
      have hl : raw40883step1Labels = raw40883step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40883step0 raw40883step0Labels permutation124 permutation6
    _ = mixedMoment B node946 node946Labels := by rfl

def raw40884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 3, -5]]
def raw40884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw40884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40884 raw40884Labels = mixedMoment B node582 node582Labels := by
  calc
    mixedMoment B raw40884 raw40884Labels = mixedMoment B raw40884step0 raw40884step0Labels := by
      have hz : ∀ j, raw40884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40884step0 = (fun i j => raw40884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40884step0 raw40884; decide +kernel
      have hl : raw40884step0Labels = raw40884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40884 raw40884Labels permutation346 hz
    mixedMoment B raw40884step0 raw40884step0Labels = mixedMoment B raw40884step1 raw40884step1Labels := by
      have ha : raw40884step1 = (fun i j => raw40884step0 (permutation148 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40884step1 raw40884step0; decide +kernel
      have hl : raw40884step1Labels = raw40884step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40884step0 raw40884step0Labels permutation148 permutation6
    _ = mixedMoment B node582 node582Labels := by rfl

def raw40885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40885Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40885step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40885 raw40885Labels = mixedMoment B node944 node944Labels := by
  calc
    mixedMoment B raw40885 raw40885Labels = mixedMoment B raw40885step0 raw40885step0Labels := by
      have ha : raw40885step0 = (fun i j => raw40885 (permutation577 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40885step0 raw40885; decide +kernel
      have hl : raw40885step0Labels = raw40885Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40885 raw40885Labels permutation577 permutation6
    _ = mixedMoment B node944 node944Labels := by rfl

def raw40886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40886Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40886step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40886 raw40886Labels = mixedMoment B node580 node580Labels := by
  calc
    mixedMoment B raw40886 raw40886Labels = mixedMoment B raw40886step0 raw40886step0Labels := by
      have ha : raw40886step0 = (fun i j => raw40886 (permutation674 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40886step0 raw40886; decide +kernel
      have hl : raw40886step0Labels = raw40886Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40886 raw40886Labels permutation674 permutation6
    _ = mixedMoment B node580 node580Labels := by rfl

def raw40887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw40887Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![3, -2, -1]]
def raw40887step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40887step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![3, -2, -1]]
def raw40887step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40887step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40887 raw40887Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw40887 raw40887Labels = mixedMoment B raw40887step0 raw40887step0Labels := by
      have hz : ∀ j, raw40887 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40887step0 = (fun i j => raw40887 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40887step0 raw40887; decide +kernel
      have hl : raw40887step0Labels = raw40887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40887 raw40887Labels permutation520 hz
    mixedMoment B raw40887step0 raw40887step0Labels = mixedMoment B raw40887step1 raw40887step1Labels := by
      have hz : ∀ j, raw40887step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40887step1 = (fun i j => raw40887step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40887step1 raw40887step0; decide +kernel
      have hl : raw40887step1Labels = raw40887step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40887step0 raw40887step0Labels permutation104 hz
    mixedMoment B raw40887step1 raw40887step1Labels = mixedMoment B raw40887step2 raw40887step2Labels := by
      have ha : raw40887step2 = (fun i j => raw40887step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40887step2 raw40887step1; decide +kernel
      have hl : raw40887step2Labels = raw40887step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40887step1 raw40887step1Labels permutation24 permutation6
    _ = mixedMoment B node2138 node2138Labels := by rfl

def raw40888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw40888Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![3, -1, -2]]
def raw40888step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40888 raw40888Labels = mixedMoment B node1829 node1829Labels := by
  calc
    mixedMoment B raw40888 raw40888Labels = mixedMoment B raw40888step0 raw40888step0Labels := by
      have hz : ∀ j, raw40888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40888step0 = (fun i j => raw40888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40888step0 raw40888; decide +kernel
      have hl : raw40888step0Labels = raw40888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40888 raw40888Labels permutation434 hz
    mixedMoment B raw40888step0 raw40888step0Labels = mixedMoment B raw40888step1 raw40888step1Labels := by
      have ha : raw40888step1 = (fun i j => raw40888step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40888step1 raw40888step0; decide +kernel
      have hl : raw40888step1Labels = raw40888step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40888step0 raw40888step0Labels permutation102 permutation6
    _ = mixedMoment B node1829 node1829Labels := by rfl

def raw40889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw40889Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw40889step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40889 raw40889Labels = mixedMoment B node2039 node2039Labels := by
  calc
    mixedMoment B raw40889 raw40889Labels = mixedMoment B raw40889step0 raw40889step0Labels := by
      have hz : ∀ j, raw40889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40889step0 = (fun i j => raw40889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40889step0 raw40889; decide +kernel
      have hl : raw40889step0Labels = raw40889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40889 raw40889Labels permutation434 hz
    mixedMoment B raw40889step0 raw40889step0Labels = mixedMoment B raw40889step1 raw40889step1Labels := by
      have ha : raw40889step1 = (fun i j => raw40889step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40889step1 raw40889step0; decide +kernel
      have hl : raw40889step1Labels = raw40889step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40889step0 raw40889step0Labels permutation96 permutation6
    _ = mixedMoment B node2039 node2039Labels := by rfl

def raw40890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw40890Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw40890step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40890 raw40890Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw40890 raw40890Labels = mixedMoment B raw40890step0 raw40890step0Labels := by
      have hz : ∀ j, raw40890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40890step0 = (fun i j => raw40890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40890step0 raw40890; decide +kernel
      have hl : raw40890step0Labels = raw40890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40890 raw40890Labels permutation434 hz
    mixedMoment B raw40890step0 raw40890step0Labels = mixedMoment B raw40890step1 raw40890step1Labels := by
      have ha : raw40890step1 = (fun i j => raw40890step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40890step1 raw40890step0; decide +kernel
      have hl : raw40890step1Labels = raw40890step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40890step0 raw40890step0Labels permutation102 permutation6
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw40891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw40891Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![1, -2, 1], ![2, 0, -2]]
def raw40891step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40891 raw40891Labels = mixedMoment B node1816 node1816Labels := by
  calc
    mixedMoment B raw40891 raw40891Labels = mixedMoment B raw40891step0 raw40891step0Labels := by
      have hz : ∀ j, raw40891 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40891step0 = (fun i j => raw40891 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40891step0 raw40891; decide +kernel
      have hl : raw40891step0Labels = raw40891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40891 raw40891Labels permutation434 hz
    mixedMoment B raw40891step0 raw40891step0Labels = mixedMoment B raw40891step1 raw40891step1Labels := by
      have ha : raw40891step1 = (fun i j => raw40891step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40891step1 raw40891step0; decide +kernel
      have hl : raw40891step1Labels = raw40891step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40891step0 raw40891step0Labels permutation102 permutation6
    _ = mixedMoment B node1816 node1816Labels := by rfl

def raw40892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw40892Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40892 raw40892Labels = mixedMoment B node1977 node1977Labels := by
  calc
    mixedMoment B raw40892 raw40892Labels = mixedMoment B raw40892step0 raw40892step0Labels := by
      have ha : raw40892step0 = (fun i j => raw40892 (permutation413 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40892step0 raw40892; decide +kernel
      have hl : raw40892step0Labels = raw40892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40892 raw40892Labels permutation413 permutation6
    _ = mixedMoment B node1977 node1977Labels := by rfl

def raw40893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw40893Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40893 raw40893Labels = mixedMoment B node1794 node1794Labels := by
  calc
    mixedMoment B raw40893 raw40893Labels = mixedMoment B raw40893step0 raw40893step0Labels := by
      have ha : raw40893step0 = (fun i j => raw40893 (permutation432 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40893step0 raw40893; decide +kernel
      have hl : raw40893step0Labels = raw40893Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40893 raw40893Labels permutation432 permutation6
    _ = mixedMoment B node1794 node1794Labels := by rfl

def raw40894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw40894Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![3, -2, -1]]
def raw40894step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw40894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw40894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40894 raw40894Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw40894 raw40894Labels = mixedMoment B raw40894step0 raw40894step0Labels := by
      have hz : ∀ j, raw40894 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40894step0 = (fun i j => raw40894 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40894step0 raw40894; decide +kernel
      have hl : raw40894step0Labels = raw40894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40894 raw40894Labels permutation520 hz
    mixedMoment B raw40894step0 raw40894step0Labels = mixedMoment B raw40894step1 raw40894step1Labels := by
      have ha : raw40894step1 = (fun i j => raw40894step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40894step1 raw40894step0; decide +kernel
      have hl : raw40894step1Labels = raw40894step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40894step0 raw40894step0Labels permutation151 permutation3
    mixedMoment B raw40894step1 raw40894step1Labels = mixedMoment B raw40894step2 raw40894step2Labels := by
      have ha : raw40894step2 = -raw40894step1 := by apply Matrix.ext; change ∀ i j, raw40894step2 i j = -(raw40894step1 i j); unfold raw40894step2 raw40894step1; decide +kernel
      have hl : raw40894step2Labels = raw40894step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2758 node2758Labels := by rfl

def raw40895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw40895Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw40895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw40895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40895 raw40895Labels = mixedMoment B node3083 node3083Labels := by
  calc
    mixedMoment B raw40895 raw40895Labels = mixedMoment B raw40895step0 raw40895step0Labels := by
      have ha : raw40895step0 = (fun i j => raw40895 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40895step0 raw40895; decide +kernel
      have hl : raw40895step0Labels = raw40895Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40895 raw40895Labels permutation688 permutation3
    mixedMoment B raw40895step0 raw40895step0Labels = mixedMoment B raw40895step1 raw40895step1Labels := by
      have ha : raw40895step1 = -raw40895step0 := by apply Matrix.ext; change ∀ i j, raw40895step1 i j = -(raw40895step0 i j); unfold raw40895step1 raw40895step0; decide +kernel
      have hl : raw40895step1Labels = raw40895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3083 node3083Labels := by rfl

def raw40896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40896Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40896 raw40896Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw40896 raw40896Labels = mixedMoment B raw40896step0 raw40896step0Labels := by
      have ha : raw40896step0 = (fun i j => raw40896 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40896step0 raw40896; decide +kernel
      have hl : raw40896step0Labels = raw40896Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40896 raw40896Labels permutation393 permutation6
    _ = mixedMoment B node3780 node3780Labels := by rfl

def raw40897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw40897Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40897 raw40897Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw40897 raw40897Labels = mixedMoment B raw40897step0 raw40897step0Labels := by
      have ha : raw40897step0 = (fun i j => raw40897 (permutation398 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40897step0 raw40897; decide +kernel
      have hl : raw40897step0Labels = raw40897Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40897 raw40897Labels permutation398 permutation6
    _ = mixedMoment B node3783 node3783Labels := by rfl

def raw40898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw40898Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40898 raw40898Labels = mixedMoment B node3710 node3710Labels := by
  calc
    mixedMoment B raw40898 raw40898Labels = mixedMoment B raw40898step0 raw40898step0Labels := by
      have ha : raw40898step0 = (fun i j => raw40898 (permutation426 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40898step0 raw40898; decide +kernel
      have hl : raw40898step0Labels = raw40898Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40898 raw40898Labels permutation426 permutation6
    _ = mixedMoment B node3710 node3710Labels := by rfl

def raw40899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw40899Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw40899step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40899 raw40899Labels = mixedMoment B node3699 node3699Labels := by
  calc
    mixedMoment B raw40899 raw40899Labels = mixedMoment B raw40899step0 raw40899step0Labels := by
      have hz : ∀ j, raw40899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40899step0 = (fun i j => raw40899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40899step0 raw40899; decide +kernel
      have hl : raw40899step0Labels = raw40899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40899 raw40899Labels permutation434 hz
    mixedMoment B raw40899step0 raw40899step0Labels = mixedMoment B raw40899step1 raw40899step1Labels := by
      have ha : raw40899step1 = (fun i j => raw40899step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40899step1 raw40899step0; decide +kernel
      have hl : raw40899step1Labels = raw40899step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40899step0 raw40899step0Labels permutation96 permutation6
    _ = mixedMoment B node3699 node3699Labels := by rfl

def raw40900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw40900Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw40900step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40900 raw40900Labels = mixedMoment B node2819 node2819Labels := by
  calc
    mixedMoment B raw40900 raw40900Labels = mixedMoment B raw40900step0 raw40900step0Labels := by
      have hz : ∀ j, raw40900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40900step0 = (fun i j => raw40900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40900step0 raw40900; decide +kernel
      have hl : raw40900step0Labels = raw40900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40900 raw40900Labels permutation434 hz
    mixedMoment B raw40900step0 raw40900step0Labels = mixedMoment B raw40900step1 raw40900step1Labels := by
      have ha : raw40900step1 = (fun i j => raw40900step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40900step1 raw40900step0; decide +kernel
      have hl : raw40900step1Labels = raw40900step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40900step0 raw40900step0Labels permutation144 permutation6
    _ = mixedMoment B node2819 node2819Labels := by rfl

def raw40901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw40901Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40901step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40901 raw40901Labels = mixedMoment B node3676 node3676Labels := by
  calc
    mixedMoment B raw40901 raw40901Labels = mixedMoment B raw40901step0 raw40901step0Labels := by
      have ha : raw40901step0 = (fun i j => raw40901 (permutation413 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40901step0 raw40901; decide +kernel
      have hl : raw40901step0Labels = raw40901Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40901 raw40901Labels permutation413 permutation6
    _ = mixedMoment B node3676 node3676Labels := by rfl

def raw40902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw40902Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40902 raw40902Labels = mixedMoment B node2801 node2801Labels := by
  calc
    mixedMoment B raw40902 raw40902Labels = mixedMoment B raw40902step0 raw40902step0Labels := by
      have ha : raw40902step0 = (fun i j => raw40902 (permutation645 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40902step0 raw40902; decide +kernel
      have hl : raw40902step0Labels = raw40902Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40902 raw40902Labels permutation645 permutation6
    _ = mixedMoment B node2801 node2801Labels := by rfl

def raw40903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw40903Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40903 raw40903Labels = mixedMoment B node3673 node3673Labels := by
  calc
    mixedMoment B raw40903 raw40903Labels = mixedMoment B raw40903step0 raw40903step0Labels := by
      have ha : raw40903step0 = (fun i j => raw40903 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40903step0 raw40903; decide +kernel
      have hl : raw40903step0Labels = raw40903Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40903 raw40903Labels permutation393 permutation6
    _ = mixedMoment B node3673 node3673Labels := by rfl

def raw40904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw40904Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40904 raw40904Labels = mixedMoment B node3685 node3685Labels := by
  calc
    mixedMoment B raw40904 raw40904Labels = mixedMoment B raw40904step0 raw40904step0Labels := by
      have ha : raw40904step0 = (fun i j => raw40904 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40904step0 raw40904; decide +kernel
      have hl : raw40904step0Labels = raw40904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40904 raw40904Labels permutation393 permutation6
    _ = mixedMoment B node3685 node3685Labels := by rfl

def raw40905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw40905Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw40905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw40905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40905 raw40905Labels = mixedMoment B node2745 node2745Labels := by
  calc
    mixedMoment B raw40905 raw40905Labels = mixedMoment B raw40905step0 raw40905step0Labels := by
      have ha : raw40905step0 = (fun i j => raw40905 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40905step0 raw40905; decide +kernel
      have hl : raw40905step0Labels = raw40905Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40905 raw40905Labels permutation640 permutation3
    mixedMoment B raw40905step0 raw40905step0Labels = mixedMoment B raw40905step1 raw40905step1Labels := by
      have ha : raw40905step1 = -raw40905step0 := by apply Matrix.ext; change ∀ i j, raw40905step1 i j = -(raw40905step0 i j); unfold raw40905step1 raw40905step0; decide +kernel
      have hl : raw40905step1Labels = raw40905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2745 node2745Labels := by rfl

def raw40906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw40906Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40906 raw40906Labels = mixedMoment B node2898 node2898Labels := by
  calc
    mixedMoment B raw40906 raw40906Labels = mixedMoment B raw40906step0 raw40906step0Labels := by
      have ha : raw40906step0 = (fun i j => raw40906 (permutation639 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40906step0 raw40906; decide +kernel
      have hl : raw40906step0Labels = raw40906Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40906 raw40906Labels permutation639 permutation6
    _ = mixedMoment B node2898 node2898Labels := by rfl

def raw40907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw40907Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw40907step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40907 raw40907Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw40907 raw40907Labels = mixedMoment B raw40907step0 raw40907step0Labels := by
      have hz : ∀ j, raw40907 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40907step0 = (fun i j => raw40907 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40907step0 raw40907; decide +kernel
      have hl : raw40907step0Labels = raw40907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40907 raw40907Labels permutation434 hz
    mixedMoment B raw40907step0 raw40907step0Labels = mixedMoment B raw40907step1 raw40907step1Labels := by
      have ha : raw40907step1 = (fun i j => raw40907step0 (permutation120 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40907step1 raw40907step0; decide +kernel
      have hl : raw40907step1Labels = raw40907step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40907step0 raw40907step0Labels permutation120 permutation6
    _ = mixedMoment B node2499 node2499Labels := by rfl

def raw40908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw40908Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 2, -4]]
def raw40908step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40908 raw40908Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw40908 raw40908Labels = mixedMoment B raw40908step0 raw40908step0Labels := by
      have hz : ∀ j, raw40908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40908step0 = (fun i j => raw40908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40908step0 raw40908; decide +kernel
      have hl : raw40908step0Labels = raw40908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40908 raw40908Labels permutation434 hz
    mixedMoment B raw40908step0 raw40908step0Labels = mixedMoment B raw40908step1 raw40908step1Labels := by
      have ha : raw40908step1 = (fun i j => raw40908step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40908step1 raw40908step0; decide +kernel
      have hl : raw40908step1Labels = raw40908step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40908step0 raw40908step0Labels permutation144 permutation6
    _ = mixedMoment B node1141 node1141Labels := by rfl

def raw40909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw40909Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40909 raw40909Labels = mixedMoment B node2441 node2441Labels := by
  calc
    mixedMoment B raw40909 raw40909Labels = mixedMoment B raw40909step0 raw40909step0Labels := by
      have ha : raw40909step0 = (fun i j => raw40909 (permutation551 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40909step0 raw40909; decide +kernel
      have hl : raw40909step0Labels = raw40909Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40909 raw40909Labels permutation551 permutation6
    _ = mixedMoment B node2441 node2441Labels := by rfl

def raw40910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw40910Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40910 raw40910Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw40910 raw40910Labels = mixedMoment B raw40910step0 raw40910step0Labels := by
      have ha : raw40910step0 = (fun i j => raw40910 (permutation645 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40910step0 raw40910; decide +kernel
      have hl : raw40910step0Labels = raw40910Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40910 raw40910Labels permutation645 permutation6
    _ = mixedMoment B node1117 node1117Labels := by rfl

def raw40911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw40911Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40911 raw40911Labels = mixedMoment B node2433 node2433Labels := by
  calc
    mixedMoment B raw40911 raw40911Labels = mixedMoment B raw40911step0 raw40911step0Labels := by
      have ha : raw40911step0 = (fun i j => raw40911 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40911step0 raw40911; decide +kernel
      have hl : raw40911step0Labels = raw40911Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40911 raw40911Labels permutation479 permutation6
    _ = mixedMoment B node2433 node2433Labels := by rfl

def raw40912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw40912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40912 raw40912Labels = mixedMoment B node2473 node2473Labels := by
  calc
    mixedMoment B raw40912 raw40912Labels = mixedMoment B raw40912step0 raw40912step0Labels := by
      have ha : raw40912step0 = (fun i j => raw40912 (permutation479 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40912step0 raw40912; decide +kernel
      have hl : raw40912step0Labels = raw40912Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40912 raw40912Labels permutation479 permutation6
    _ = mixedMoment B node2473 node2473Labels := by rfl

def raw40913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw40913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 3, -4], ![2, -2, 0]]
def raw40913step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 3, -4], ![2, -2, 0]]
def raw40913step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40913 raw40913Labels = mixedMoment B node1063 node1063Labels := by
  calc
    mixedMoment B raw40913 raw40913Labels = mixedMoment B raw40913step0 raw40913step0Labels := by
      have hz : ∀ j, raw40913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40913step0 = (fun i j => raw40913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40913step0 raw40913; decide +kernel
      have hl : raw40913step0Labels = raw40913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40913 raw40913Labels permutation434 hz
    mixedMoment B raw40913step0 raw40913step0Labels = mixedMoment B raw40913step1 raw40913step1Labels := by
      have hz : ∀ j, raw40913step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40913step1 = (fun i j => raw40913step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40913step1 raw40913step0; decide +kernel
      have hl : raw40913step1Labels = raw40913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40913step0 raw40913step0Labels permutation80 hz
    mixedMoment B raw40913step1 raw40913step1Labels = mixedMoment B raw40913step2 raw40913step2Labels := by
      have ha : raw40913step2 = (fun i j => raw40913step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40913step2 raw40913step1; decide +kernel
      have hl : raw40913step2Labels = raw40913step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40913step1 raw40913step1Labels permutation24 permutation6
    _ = mixedMoment B node1063 node1063Labels := by rfl

def raw40914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 3, -5]]
def raw40914step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -2, 1], ![2, 3, -5]]
def raw40914step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40914step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw40914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40914 raw40914Labels = mixedMoment B node616 node616Labels := by
  calc
    mixedMoment B raw40914 raw40914Labels = mixedMoment B raw40914step0 raw40914step0Labels := by
      have hz : ∀ j, raw40914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40914step0 = (fun i j => raw40914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40914step0 raw40914; decide +kernel
      have hl : raw40914step0Labels = raw40914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40914 raw40914Labels permutation434 hz
    mixedMoment B raw40914step0 raw40914step0Labels = mixedMoment B raw40914step1 raw40914step1Labels := by
      have hz : ∀ j, raw40914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40914step1 = (fun i j => raw40914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40914step1 raw40914step0; decide +kernel
      have hl : raw40914step1Labels = raw40914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40914step0 raw40914step0Labels permutation80 hz
    mixedMoment B raw40914step1 raw40914step1Labels = mixedMoment B raw40914step2 raw40914step2Labels := by
      have ha : raw40914step2 = (fun i j => raw40914step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40914step2 raw40914step1; decide +kernel
      have hl : raw40914step2Labels = raw40914step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40914step1 raw40914step1Labels permutation30 permutation6
    _ = mixedMoment B node616 node616Labels := by rfl

def raw40915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 3, -4], ![2, -1, -1]]
def raw40915step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40915 raw40915Labels = mixedMoment B node950 node950Labels := by
  calc
    mixedMoment B raw40915 raw40915Labels = mixedMoment B raw40915step0 raw40915step0Labels := by
      have hz : ∀ j, raw40915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40915step0 = (fun i j => raw40915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40915step0 raw40915; decide +kernel
      have hl : raw40915step0Labels = raw40915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40915 raw40915Labels permutation346 hz
    mixedMoment B raw40915step0 raw40915step0Labels = mixedMoment B raw40915step1 raw40915step1Labels := by
      have ha : raw40915step1 = (fun i j => raw40915step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40915step1 raw40915step0; decide +kernel
      have hl : raw40915step1Labels = raw40915step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40915step0 raw40915step0Labels permutation126 permutation6
    _ = mixedMoment B node950 node950Labels := by rfl

def raw40916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 3, -5]]
def raw40916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw40916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40916 raw40916Labels = mixedMoment B node586 node586Labels := by
  calc
    mixedMoment B raw40916 raw40916Labels = mixedMoment B raw40916step0 raw40916step0Labels := by
      have hz : ∀ j, raw40916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40916step0 = (fun i j => raw40916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40916step0 raw40916; decide +kernel
      have hl : raw40916step0Labels = raw40916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40916 raw40916Labels permutation346 hz
    mixedMoment B raw40916step0 raw40916step0Labels = mixedMoment B raw40916step1 raw40916step1Labels := by
      have ha : raw40916step1 = (fun i j => raw40916step0 (permutation150 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40916step1 raw40916step0; decide +kernel
      have hl : raw40916step1Labels = raw40916step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40916step0 raw40916step0Labels permutation150 permutation6
    _ = mixedMoment B node586 node586Labels := by rfl

def raw40917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw40917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![3, -1, -2]]
def raw40917step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![3, -1, -2]]
def raw40917step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40917 raw40917Labels = mixedMoment B node1830 node1830Labels := by
  calc
    mixedMoment B raw40917 raw40917Labels = mixedMoment B raw40917step0 raw40917step0Labels := by
      have hz : ∀ j, raw40917 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40917step0 = (fun i j => raw40917 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40917step0 raw40917; decide +kernel
      have hl : raw40917step0Labels = raw40917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40917 raw40917Labels permutation520 hz
    mixedMoment B raw40917step0 raw40917step0Labels = mixedMoment B raw40917step1 raw40917step1Labels := by
      have hz : ∀ j, raw40917step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40917step1 = (fun i j => raw40917step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40917step1 raw40917step0; decide +kernel
      have hl : raw40917step1Labels = raw40917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40917step0 raw40917step0Labels permutation104 hz
    mixedMoment B raw40917step1 raw40917step1Labels = mixedMoment B raw40917step2 raw40917step2Labels := by
      have ha : raw40917step2 = (fun i j => raw40917step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40917step2 raw40917step1; decide +kernel
      have hl : raw40917step2Labels = raw40917step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40917step1 raw40917step1Labels permutation24 permutation6
    _ = mixedMoment B node1830 node1830Labels := by rfl

def raw40918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw40918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw40918step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40918 raw40918Labels = mixedMoment B node1978 node1978Labels := by
  calc
    mixedMoment B raw40918 raw40918Labels = mixedMoment B raw40918step0 raw40918step0Labels := by
      have hz : ∀ j, raw40918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40918step0 = (fun i j => raw40918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40918step0 raw40918; decide +kernel
      have hl : raw40918step0Labels = raw40918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40918 raw40918Labels permutation434 hz
    mixedMoment B raw40918step0 raw40918step0Labels = mixedMoment B raw40918step1 raw40918step1Labels := by
      have ha : raw40918step1 = (fun i j => raw40918step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40918step1 raw40918step0; decide +kernel
      have hl : raw40918step1Labels = raw40918step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40918step0 raw40918step0Labels permutation96 permutation6
    _ = mixedMoment B node1978 node1978Labels := by rfl

def raw40919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw40919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 3, -3], ![1, -1, 0], ![2, 0, -2]]
def raw40919step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40919step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40919 raw40919Labels = mixedMoment B node1795 node1795Labels := by
  calc
    mixedMoment B raw40919 raw40919Labels = mixedMoment B raw40919step0 raw40919step0Labels := by
      have hz : ∀ j, raw40919 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40919step0 = (fun i j => raw40919 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40919step0 raw40919; decide +kernel
      have hl : raw40919step0Labels = raw40919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40919 raw40919Labels permutation434 hz
    mixedMoment B raw40919step0 raw40919step0Labels = mixedMoment B raw40919step1 raw40919step1Labels := by
      have ha : raw40919step1 = (fun i j => raw40919step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40919step1 raw40919step0; decide +kernel
      have hl : raw40919step1Labels = raw40919step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40919step0 raw40919step0Labels permutation102 permutation6
    _ = mixedMoment B node1795 node1795Labels := by rfl

def raw40920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw40920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![3, -1, -2]]
def raw40920step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 3, -1], ![-2, 0, 2]]
def raw40920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw40920step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40920 raw40920Labels = mixedMoment B node2362 node2362Labels := by
  calc
    mixedMoment B raw40920 raw40920Labels = mixedMoment B raw40920step0 raw40920step0Labels := by
      have hz : ∀ j, raw40920 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40920step0 = (fun i j => raw40920 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40920step0 raw40920; decide +kernel
      have hl : raw40920step0Labels = raw40920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40920 raw40920Labels permutation520 hz
    mixedMoment B raw40920step0 raw40920step0Labels = mixedMoment B raw40920step1 raw40920step1Labels := by
      have ha : raw40920step1 = (fun i j => raw40920step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40920step1 raw40920step0; decide +kernel
      have hl : raw40920step1Labels = raw40920step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40920step0 raw40920step0Labels permutation59 permutation6
    mixedMoment B raw40920step1 raw40920step1Labels = mixedMoment B raw40920step2 raw40920step2Labels := by
      have ha : raw40920step2 = -raw40920step1 := by apply Matrix.ext; change ∀ i j, raw40920step2 i j = -(raw40920step1 i j); unfold raw40920step2 raw40920step1; decide +kernel
      have hl : raw40920step2Labels = raw40920step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2362 node2362Labels := by rfl

def raw40921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw40921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40921step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40921 raw40921Labels = mixedMoment B node2353 node2353Labels := by
  calc
    mixedMoment B raw40921 raw40921Labels = mixedMoment B raw40921step0 raw40921step0Labels := by
      have ha : raw40921step0 = (fun i j => raw40921 (permutation288 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40921step0 raw40921; decide +kernel
      have hl : raw40921step0Labels = raw40921Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40921 raw40921Labels permutation288 permutation6
    mixedMoment B raw40921step0 raw40921step0Labels = mixedMoment B raw40921step1 raw40921step1Labels := by
      have ha : raw40921step1 = -raw40921step0 := by apply Matrix.ext; change ∀ i j, raw40921step1 i j = -(raw40921step0 i j); unfold raw40921step1 raw40921step0; decide +kernel
      have hl : raw40921step1Labels = raw40921step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2353 node2353Labels := by rfl

def raw40922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw40922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40922step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40922 raw40922Labels = mixedMoment B node2350 node2350Labels := by
  calc
    mixedMoment B raw40922 raw40922Labels = mixedMoment B raw40922step0 raw40922step0Labels := by
      have ha : raw40922step0 = (fun i j => raw40922 (permutation280 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40922step0 raw40922; decide +kernel
      have hl : raw40922step0Labels = raw40922Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40922 raw40922Labels permutation280 permutation6
    mixedMoment B raw40922step0 raw40922step0Labels = mixedMoment B raw40922step1 raw40922step1Labels := by
      have ha : raw40922step1 = -raw40922step0 := by apply Matrix.ext; change ∀ i j, raw40922step1 i j = -(raw40922step0 i j); unfold raw40922step1 raw40922step0; decide +kernel
      have hl : raw40922step1Labels = raw40922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2350 node2350Labels := by rfl

def raw40923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw40923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw40923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw40923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw40923step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40923 raw40923Labels = mixedMoment B node2356 node2356Labels := by
  calc
    mixedMoment B raw40923 raw40923Labels = mixedMoment B raw40923step0 raw40923step0Labels := by
      have hz : ∀ j, raw40923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40923step0 = (fun i j => raw40923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40923step0 raw40923; decide +kernel
      have hl : raw40923step0Labels = raw40923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40923 raw40923Labels permutation434 hz
    mixedMoment B raw40923step0 raw40923step0Labels = mixedMoment B raw40923step1 raw40923step1Labels := by
      have ha : raw40923step1 = (fun i j => raw40923step0 (permutation61 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40923step1 raw40923step0; decide +kernel
      have hl : raw40923step1Labels = raw40923step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40923step0 raw40923step0Labels permutation61 permutation6
    mixedMoment B raw40923step1 raw40923step1Labels = mixedMoment B raw40923step2 raw40923step2Labels := by
      have ha : raw40923step2 = -raw40923step1 := by apply Matrix.ext; change ∀ i j, raw40923step2 i j = -(raw40923step1 i j); unfold raw40923step2 raw40923step1; decide +kernel
      have hl : raw40923step2Labels = raw40923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2356 node2356Labels := by rfl

def raw40924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw40924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw40924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 2, 1]]
def raw40924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw40924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40924 raw40924Labels = mixedMoment B node2352 node2352Labels := by
  calc
    mixedMoment B raw40924 raw40924Labels = mixedMoment B raw40924step0 raw40924step0Labels := by
      have hz : ∀ j, raw40924 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40924step0 = (fun i j => raw40924 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40924step0 raw40924; decide +kernel
      have hl : raw40924step0Labels = raw40924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40924 raw40924Labels permutation434 hz
    mixedMoment B raw40924step0 raw40924step0Labels = mixedMoment B raw40924step1 raw40924step1Labels := by
      have ha : raw40924step1 = (fun i j => raw40924step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40924step1 raw40924step0; decide +kernel
      have hl : raw40924step1Labels = raw40924step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40924step0 raw40924step0Labels permutation58 permutation6
    mixedMoment B raw40924step1 raw40924step1Labels = mixedMoment B raw40924step2 raw40924step2Labels := by
      have ha : raw40924step2 = -raw40924step1 := by apply Matrix.ext; change ∀ i j, raw40924step2 i j = -(raw40924step1 i j); unfold raw40924step2 raw40924step1; decide +kernel
      have hl : raw40924step2Labels = raw40924step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2352 node2352Labels := by rfl

def raw40925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 2, -2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw40925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40925 raw40925Labels = mixedMoment B node2348 node2348Labels := by
  calc
    mixedMoment B raw40925 raw40925Labels = mixedMoment B raw40925step0 raw40925step0Labels := by
      have ha : raw40925step0 = (fun i j => raw40925 (permutation288 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40925step0 raw40925; decide +kernel
      have hl : raw40925step0Labels = raw40925Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40925 raw40925Labels permutation288 permutation6
    mixedMoment B raw40925step0 raw40925step0Labels = mixedMoment B raw40925step1 raw40925step1Labels := by
      have ha : raw40925step1 = -raw40925step0 := by apply Matrix.ext; change ∀ i j, raw40925step1 i j = -(raw40925step0 i j); unfold raw40925step1 raw40925step0; decide +kernel
      have hl : raw40925step1Labels = raw40925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2348 node2348Labels := by rfl

def raw40926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw40926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw40926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40926step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw40926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40926 raw40926Labels = mixedMoment B node2361 node2361Labels := by
  calc
    mixedMoment B raw40926 raw40926Labels = mixedMoment B raw40926step0 raw40926step0Labels := by
      have ha : raw40926step0 = (fun i j => raw40926 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40926step0 raw40926; decide +kernel
      have hl : raw40926step0Labels = raw40926Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40926 raw40926Labels permutation265 permutation6
    mixedMoment B raw40926step0 raw40926step0Labels = mixedMoment B raw40926step1 raw40926step1Labels := by
      have ha : raw40926step1 = -raw40926step0 := by apply Matrix.ext; change ∀ i j, raw40926step1 i j = -(raw40926step0 i j); unfold raw40926step1 raw40926step0; decide +kernel
      have hl : raw40926step1Labels = raw40926step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2361 node2361Labels := by rfl

def raw40927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw40927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw40927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40927step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw40927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40927 raw40927Labels = mixedMoment B node2349 node2349Labels := by
  calc
    mixedMoment B raw40927 raw40927Labels = mixedMoment B raw40927step0 raw40927step0Labels := by
      have ha : raw40927step0 = (fun i j => raw40927 (permutation277 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40927step0 raw40927; decide +kernel
      have hl : raw40927step0Labels = raw40927Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40927 raw40927Labels permutation277 permutation6
    mixedMoment B raw40927step0 raw40927step0Labels = mixedMoment B raw40927step1 raw40927step1Labels := by
      have ha : raw40927step1 = -raw40927step0 := by apply Matrix.ext; change ∀ i j, raw40927step1 i j = -(raw40927step0 i j); unfold raw40927step1 raw40927step0; decide +kernel
      have hl : raw40927step1Labels = raw40927step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2349 node2349Labels := by rfl

def raw40928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 2, -3], ![2, -1, -1]]
def raw40928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw40928step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw40928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40928step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw40928step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40928 raw40928Labels = mixedMoment B node2355 node2355Labels := by
  calc
    mixedMoment B raw40928 raw40928Labels = mixedMoment B raw40928step0 raw40928step0Labels := by
      have hz : ∀ j, raw40928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40928step0 = (fun i j => raw40928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40928step0 raw40928; decide +kernel
      have hl : raw40928step0Labels = raw40928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40928 raw40928Labels permutation434 hz
    mixedMoment B raw40928step0 raw40928step0Labels = mixedMoment B raw40928step1 raw40928step1Labels := by
      have ha : raw40928step1 = (fun i j => raw40928step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40928step1 raw40928step0; decide +kernel
      have hl : raw40928step1Labels = raw40928step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40928step0 raw40928step0Labels permutation60 permutation6
    mixedMoment B raw40928step1 raw40928step1Labels = mixedMoment B raw40928step2 raw40928step2Labels := by
      have ha : raw40928step2 = -raw40928step1 := by apply Matrix.ext; change ∀ i j, raw40928step2 i j = -(raw40928step1 i j); unfold raw40928step2 raw40928step1; decide +kernel
      have hl : raw40928step2Labels = raw40928step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2355 node2355Labels := by rfl

def raw40929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw40929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 2, -4]]
def raw40929step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40929 raw40929Labels = mixedMoment B node1119 node1119Labels := by
  calc
    mixedMoment B raw40929 raw40929Labels = mixedMoment B raw40929step0 raw40929step0Labels := by
      have hz : ∀ j, raw40929 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40929step0 = (fun i j => raw40929 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40929step0 raw40929; decide +kernel
      have hl : raw40929step0Labels = raw40929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40929 raw40929Labels permutation434 hz
    mixedMoment B raw40929step0 raw40929step0Labels = mixedMoment B raw40929step1 raw40929step1Labels := by
      have ha : raw40929step1 = (fun i j => raw40929step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40929step1 raw40929step0; decide +kernel
      have hl : raw40929step1Labels = raw40929step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40929step0 raw40929step0Labels permutation144 permutation6
    _ = mixedMoment B node1119 node1119Labels := by rfl

def raw40930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 1, -1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw40930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw40930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40930step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw40930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40930 raw40930Labels = mixedMoment B node2347 node2347Labels := by
  calc
    mixedMoment B raw40930 raw40930Labels = mixedMoment B raw40930step0 raw40930step0Labels := by
      have ha : raw40930step0 = (fun i j => raw40930 (permutation287 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40930step0 raw40930; decide +kernel
      have hl : raw40930step0Labels = raw40930Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40930 raw40930Labels permutation287 permutation6
    mixedMoment B raw40930step0 raw40930step0Labels = mixedMoment B raw40930step1 raw40930step1Labels := by
      have ha : raw40930step1 = -raw40930step0 := by apply Matrix.ext; change ∀ i j, raw40930step1 i j = -(raw40930step0 i j); unfold raw40930step1 raw40930step0; decide +kernel
      have hl : raw40930step1Labels = raw40930step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2347 node2347Labels := by rfl

def raw40931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw40931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, 3, -4], ![2, -1, -1]]
def raw40931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, 3, -4], ![2, -1, -1]]
def raw40931step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40931step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40931 raw40931Labels = mixedMoment B node952 node952Labels := by
  calc
    mixedMoment B raw40931 raw40931Labels = mixedMoment B raw40931step0 raw40931step0Labels := by
      have hz : ∀ j, raw40931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40931step0 = (fun i j => raw40931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40931step0 raw40931; decide +kernel
      have hl : raw40931step0Labels = raw40931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40931 raw40931Labels permutation434 hz
    mixedMoment B raw40931step0 raw40931step0Labels = mixedMoment B raw40931step1 raw40931step1Labels := by
      have hz : ∀ j, raw40931step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40931step1 = (fun i j => raw40931step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40931step1 raw40931step0; decide +kernel
      have hl : raw40931step1Labels = raw40931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40931step0 raw40931step0Labels permutation80 hz
    mixedMoment B raw40931step1 raw40931step1Labels = mixedMoment B raw40931step2 raw40931step2Labels := by
      have ha : raw40931step2 = (fun i j => raw40931step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40931step2 raw40931step1; decide +kernel
      have hl : raw40931step2Labels = raw40931step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40931step1 raw40931step1Labels permutation24 permutation6
    _ = mixedMoment B node952 node952Labels := by rfl

def raw40932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 3, -5]]
def raw40932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40932step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -2, 3], ![1, -1, 0], ![2, 3, -5]]
def raw40932step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40932step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw40932step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40932 raw40932Labels = mixedMoment B node588 node588Labels := by
  calc
    mixedMoment B raw40932 raw40932Labels = mixedMoment B raw40932step0 raw40932step0Labels := by
      have hz : ∀ j, raw40932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40932step0 = (fun i j => raw40932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40932step0 raw40932; decide +kernel
      have hl : raw40932step0Labels = raw40932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40932 raw40932Labels permutation434 hz
    mixedMoment B raw40932step0 raw40932step0Labels = mixedMoment B raw40932step1 raw40932step1Labels := by
      have hz : ∀ j, raw40932step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40932step1 = (fun i j => raw40932step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40932step1 raw40932step0; decide +kernel
      have hl : raw40932step1Labels = raw40932step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40932step0 raw40932step0Labels permutation80 hz
    mixedMoment B raw40932step1 raw40932step1Labels = mixedMoment B raw40932step2 raw40932step2Labels := by
      have ha : raw40932step2 = (fun i j => raw40932step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40932step2 raw40932step1; decide +kernel
      have hl : raw40932step2Labels = raw40932step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40932step1 raw40932step1Labels permutation30 permutation6
    _ = mixedMoment B node588 node588Labels := by rfl

def raw40933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![2, -3, 1]]
def raw40933step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40933step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![2, -3, 1]]
def raw40933step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40933step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![2, -2, 0]]
def raw40933step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40933 raw40933Labels = mixedMoment B node2294 node2294Labels := by
  calc
    mixedMoment B raw40933 raw40933Labels = mixedMoment B raw40933step0 raw40933step0Labels := by
      have hz : ∀ j, raw40933 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40933step0 = (fun i j => raw40933 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40933step0 raw40933; decide +kernel
      have hl : raw40933step0Labels = raw40933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40933 raw40933Labels permutation520 hz
    mixedMoment B raw40933step0 raw40933step0Labels = mixedMoment B raw40933step1 raw40933step1Labels := by
      have hz : ∀ j, raw40933step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40933step1 = (fun i j => raw40933step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40933step1 raw40933step0; decide +kernel
      have hl : raw40933step1Labels = raw40933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40933step0 raw40933step0Labels permutation104 hz
    mixedMoment B raw40933step1 raw40933step1Labels = mixedMoment B raw40933step2 raw40933step2Labels := by
      have hz : ∀ j, raw40933step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw40933step2 = (fun i j => raw40933step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw40933step2 raw40933step1; decide +kernel
      have hl : raw40933step2Labels = raw40933step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40933step1 raw40933step1Labels permutation20 hz
    mixedMoment B raw40933step2 raw40933step2Labels = mixedMoment B raw40933step3 raw40933step3Labels := by
      have ha : raw40933step3 = (fun i j => raw40933step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40933step3 raw40933step2; decide +kernel
      have hl : raw40933step3Labels = raw40933step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40933step2 raw40933step2Labels permutation5 permutation6
    _ = mixedMoment B node2294 node2294Labels := by rfl

def raw40934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![2, -2, 0]]
def raw40934step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40934 raw40934Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw40934 raw40934Labels = mixedMoment B raw40934step0 raw40934step0Labels := by
      have hz : ∀ j, raw40934 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40934step0 = (fun i j => raw40934 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40934step0 raw40934; decide +kernel
      have hl : raw40934step0Labels = raw40934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40934 raw40934Labels permutation434 hz
    mixedMoment B raw40934step0 raw40934step0Labels = mixedMoment B raw40934step1 raw40934step1Labels := by
      have hz : ∀ j, raw40934step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40934step1 = (fun i j => raw40934step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40934step1 raw40934step0; decide +kernel
      have hl : raw40934step1Labels = raw40934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40934step0 raw40934step0Labels permutation80 hz
    mixedMoment B raw40934step1 raw40934step1Labels = mixedMoment B raw40934step2 raw40934step2Labels := by
      have ha : raw40934step2 = (fun i j => raw40934step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40934step2 raw40934step1; decide +kernel
      have hl : raw40934step2Labels = raw40934step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40934step1 raw40934step1Labels permutation19 permutation6
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw40935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40935step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![2, -1, -1]]
def raw40935step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40935step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40935step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40935 raw40935Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw40935 raw40935Labels = mixedMoment B raw40935step0 raw40935step0Labels := by
      have hz : ∀ j, raw40935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40935step0 = (fun i j => raw40935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40935step0 raw40935; decide +kernel
      have hl : raw40935step0Labels = raw40935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40935 raw40935Labels permutation434 hz
    mixedMoment B raw40935step0 raw40935step0Labels = mixedMoment B raw40935step1 raw40935step1Labels := by
      have hz : ∀ j, raw40935step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40935step1 = (fun i j => raw40935step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40935step1 raw40935step0; decide +kernel
      have hl : raw40935step1Labels = raw40935step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40935step0 raw40935step0Labels permutation80 hz
    mixedMoment B raw40935step1 raw40935step1Labels = mixedMoment B raw40935step2 raw40935step2Labels := by
      have ha : raw40935step2 = (fun i j => raw40935step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40935step2 raw40935step1; decide +kernel
      have hl : raw40935step2Labels = raw40935step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40935step1 raw40935step1Labels permutation18 permutation6
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw40936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -3, 3], ![2, 0, -2]]
def raw40936step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw40936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40936 raw40936Labels = mixedMoment B node1817 node1817Labels := by
  calc
    mixedMoment B raw40936 raw40936Labels = mixedMoment B raw40936step0 raw40936step0Labels := by
      have hz : ∀ j, raw40936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40936step0 = (fun i j => raw40936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40936step0 raw40936; decide +kernel
      have hl : raw40936step0Labels = raw40936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40936 raw40936Labels permutation434 hz
    mixedMoment B raw40936step0 raw40936step0Labels = mixedMoment B raw40936step1 raw40936step1Labels := by
      have hz : ∀ j, raw40936step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40936step1 = (fun i j => raw40936step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40936step1 raw40936step0; decide +kernel
      have hl : raw40936step1Labels = raw40936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40936step0 raw40936step0Labels permutation80 hz
    mixedMoment B raw40936step1 raw40936step1Labels = mixedMoment B raw40936step2 raw40936step2Labels := by
      have ha : raw40936step2 = (fun i j => raw40936step1 (permutation18 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40936step2 raw40936step1; decide +kernel
      have hl : raw40936step2Labels = raw40936step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40936step1 raw40936step1Labels permutation18 permutation6
    _ = mixedMoment B node1817 node1817Labels := by rfl

def raw40937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![1, -1, 0], ![1, -2, 1]]
def raw40937step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40937step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40937 raw40937Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw40937 raw40937Labels = mixedMoment B raw40937step0 raw40937step0Labels := by
      have hz : ∀ j, raw40937 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40937step0 = (fun i j => raw40937 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40937step0 raw40937; decide +kernel
      have hl : raw40937step0Labels = raw40937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40937 raw40937Labels permutation434 hz
    mixedMoment B raw40937step0 raw40937step0Labels = mixedMoment B raw40937step1 raw40937step1Labels := by
      have hz : ∀ j, raw40937step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40937step1 = (fun i j => raw40937step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40937step1 raw40937step0; decide +kernel
      have hl : raw40937step1Labels = raw40937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40937step0 raw40937step0Labels permutation80 hz
    mixedMoment B raw40937step1 raw40937step1Labels = mixedMoment B raw40937step2 raw40937step2Labels := by
      have ha : raw40937step2 = (fun i j => raw40937step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40937step2 raw40937step1; decide +kernel
      have hl : raw40937step2Labels = raw40937step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40937step1 raw40937step1Labels permutation17 permutation6
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw40938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40938 raw40938Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw40938 raw40938Labels = mixedMoment B raw40938step0 raw40938step0Labels := by
      have hz : ∀ j, raw40938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40938step0 = (fun i j => raw40938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40938step0 raw40938; decide +kernel
      have hl : raw40938step0Labels = raw40938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40938 raw40938Labels permutation346 hz
    mixedMoment B raw40938step0 raw40938step0Labels = mixedMoment B raw40938step1 raw40938step1Labels := by
      have ha : raw40938step1 = (fun i j => raw40938step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40938step1 raw40938step0; decide +kernel
      have hl : raw40938step1Labels = raw40938step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40938step0 raw40938step0Labels permutation77 permutation6
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw40939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40939Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40939step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40939step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40939step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40939 raw40939Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw40939 raw40939Labels = mixedMoment B raw40939step0 raw40939step0Labels := by
      have hz : ∀ j, raw40939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40939step0 = (fun i j => raw40939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40939step0 raw40939; decide +kernel
      have hl : raw40939step0Labels = raw40939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40939 raw40939Labels permutation346 hz
    mixedMoment B raw40939step0 raw40939step0Labels = mixedMoment B raw40939step1 raw40939step1Labels := by
      have ha : raw40939step1 = (fun i j => raw40939step0 (permutation76 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40939step1 raw40939step0; decide +kernel
      have hl : raw40939step1Labels = raw40939step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40939step0 raw40939step0Labels permutation76 permutation6
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw40940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40940Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40940step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40940 raw40940Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw40940 raw40940Labels = mixedMoment B raw40940step0 raw40940step0Labels := by
      have hz : ∀ j, raw40940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40940step0 = (fun i j => raw40940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40940step0 raw40940; decide +kernel
      have hl : raw40940step0Labels = raw40940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40940 raw40940Labels permutation346 hz
    mixedMoment B raw40940step0 raw40940step0Labels = mixedMoment B raw40940step1 raw40940step1Labels := by
      have ha : raw40940step1 = (fun i j => raw40940step0 (permutation71 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40940step1 raw40940step0; decide +kernel
      have hl : raw40940step1Labels = raw40940step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40940step0 raw40940step0Labels permutation71 permutation6
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw40941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40941Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40941step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40941 raw40941Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw40941 raw40941Labels = mixedMoment B raw40941step0 raw40941step0Labels := by
      have hz : ∀ j, raw40941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40941step0 = (fun i j => raw40941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40941step0 raw40941; decide +kernel
      have hl : raw40941step0Labels = raw40941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40941 raw40941Labels permutation346 hz
    mixedMoment B raw40941step0 raw40941step0Labels = mixedMoment B raw40941step1 raw40941step1Labels := by
      have ha : raw40941step1 = (fun i j => raw40941step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40941step1 raw40941step0; decide +kernel
      have hl : raw40941step1Labels = raw40941step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40941step0 raw40941step0Labels permutation73 permutation6
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw40942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40942Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40942step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40942step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40942step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40942 raw40942Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw40942 raw40942Labels = mixedMoment B raw40942step0 raw40942step0Labels := by
      have hz : ∀ j, raw40942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40942step0 = (fun i j => raw40942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40942step0 raw40942; decide +kernel
      have hl : raw40942step0Labels = raw40942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40942 raw40942Labels permutation346 hz
    mixedMoment B raw40942step0 raw40942step0Labels = mixedMoment B raw40942step1 raw40942step1Labels := by
      have ha : raw40942step1 = (fun i j => raw40942step0 (permutation72 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40942step1 raw40942step0; decide +kernel
      have hl : raw40942step1Labels = raw40942step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40942step0 raw40942step0Labels permutation72 permutation6
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw40943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, 0, 0], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw40943step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw40943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40943 raw40943Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw40943 raw40943Labels = mixedMoment B raw40943step0 raw40943step0Labels := by
      have hz : ∀ j, raw40943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw40943step0 = (fun i j => raw40943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw40943step0 raw40943; decide +kernel
      have hl : raw40943step0Labels = raw40943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40943 raw40943Labels permutation346 hz
    mixedMoment B raw40943step0 raw40943step0Labels = mixedMoment B raw40943step1 raw40943step1Labels := by
      have ha : raw40943step1 = (fun i j => raw40943step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40943step1 raw40943step0; decide +kernel
      have hl : raw40943step1Labels = raw40943step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40943step0 raw40943step0Labels permutation83 permutation6
    mixedMoment B raw40943step1 raw40943step1Labels = mixedMoment B raw40943step2 raw40943step2Labels := by
      have ha : raw40943step2 = -raw40943step1 := by apply Matrix.ext; change ∀ i j, raw40943step2 i j = -(raw40943step1 i j); unfold raw40943step2 raw40943step1; decide +kernel
      have hl : raw40943step2Labels = raw40943step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1804 node1804Labels := by rfl

def raw40944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw40944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40944step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40944 raw40944Labels = mixedMoment B node1811 node1811Labels := by
  calc
    mixedMoment B raw40944 raw40944Labels = mixedMoment B raw40944step0 raw40944step0Labels := by
      have ha : raw40944step0 = (fun i j => raw40944 (permutation340 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40944step0 raw40944; decide +kernel
      have hl : raw40944step0Labels = raw40944Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40944 raw40944Labels permutation340 permutation6
    _ = mixedMoment B node1811 node1811Labels := by rfl

def raw40945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0]]
def raw40945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40945step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40945 raw40945Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw40945 raw40945Labels = mixedMoment B raw40945step0 raw40945step0Labels := by
      have ha : raw40945step0 = (fun i j => raw40945 (permutation332 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40945step0 raw40945; decide +kernel
      have hl : raw40945step0Labels = raw40945Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40945 raw40945Labels permutation332 permutation6
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw40946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 3, -3], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw40946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40946step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40946 raw40946Labels = mixedMoment B node1966 node1966Labels := by
  calc
    mixedMoment B raw40946 raw40946Labels = mixedMoment B raw40946step0 raw40946step0Labels := by
      have ha : raw40946step0 = (fun i j => raw40946 (permutation331 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40946step0 raw40946; decide +kernel
      have hl : raw40946step0Labels = raw40946Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40946 raw40946Labels permutation331 permutation6
    _ = mixedMoment B node1966 node1966Labels := by rfl

def raw40947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1]]
def raw40947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1]]
def raw40947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![2, -3, 1]]
def raw40947step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw40947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40947step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw40947step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40947 raw40947Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw40947 raw40947Labels = mixedMoment B raw40947step0 raw40947step0Labels := by
      have hz : ∀ j, raw40947 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw40947step0 = (fun i j => raw40947 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw40947step0 raw40947; decide +kernel
      have hl : raw40947step0Labels = raw40947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40947 raw40947Labels permutation520 hz
    mixedMoment B raw40947step0 raw40947step0Labels = mixedMoment B raw40947step1 raw40947step1Labels := by
      have hz : ∀ j, raw40947step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw40947step1 = (fun i j => raw40947step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw40947step1 raw40947step0; decide +kernel
      have hl : raw40947step1Labels = raw40947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40947step0 raw40947step0Labels permutation104 hz
    mixedMoment B raw40947step1 raw40947step1Labels = mixedMoment B raw40947step2 raw40947step2Labels := by
      have ha : raw40947step2 = (fun i j => raw40947step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw40947step2 raw40947step1; decide +kernel
      have hl : raw40947step2Labels = raw40947step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40947step1 raw40947step1Labels permutation31 permutation3
    mixedMoment B raw40947step2 raw40947step2Labels = mixedMoment B raw40947step3 raw40947step3Labels := by
      have ha : raw40947step3 = -raw40947step2 := by apply Matrix.ext; change ∀ i j, raw40947step3 i j = -(raw40947step2 i j); unfold raw40947step3 raw40947step2; decide +kernel
      have hl : raw40947step3Labels = raw40947step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw40948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0]]
def raw40948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0]]
def raw40948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw40948step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40948 raw40948Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw40948 raw40948Labels = mixedMoment B raw40948step0 raw40948step0Labels := by
      have hz : ∀ j, raw40948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40948step0 = (fun i j => raw40948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40948step0 raw40948; decide +kernel
      have hl : raw40948step0Labels = raw40948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40948 raw40948Labels permutation434 hz
    mixedMoment B raw40948step0 raw40948step0Labels = mixedMoment B raw40948step1 raw40948step1Labels := by
      have ha : raw40948step1 = (fun i j => raw40948step0 (permutation67 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40948step1 raw40948step0; decide +kernel
      have hl : raw40948step1Labels = raw40948step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40948step0 raw40948step0Labels permutation67 permutation6
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw40949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1]]
def raw40949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1]]
def raw40949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw40949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw40949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40949 raw40949Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw40949 raw40949Labels = mixedMoment B raw40949step0 raw40949step0Labels := by
      have hz : ∀ j, raw40949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40949step0 = (fun i j => raw40949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40949step0 raw40949; decide +kernel
      have hl : raw40949step0Labels = raw40949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40949 raw40949Labels permutation434 hz
    mixedMoment B raw40949step0 raw40949step0Labels = mixedMoment B raw40949step1 raw40949step1Labels := by
      have ha : raw40949step1 = (fun i j => raw40949step0 (permutation109 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40949step1 raw40949step0; decide +kernel
      have hl : raw40949step1Labels = raw40949step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40949step0 raw40949step0Labels permutation109 permutation6
    mixedMoment B raw40949step1 raw40949step1Labels = mixedMoment B raw40949step2 raw40949step2Labels := by
      have ha : raw40949step2 = -raw40949step1 := by apply Matrix.ext; change ∀ i j, raw40949step2 i j = -(raw40949step1 i j); unfold raw40949step2 raw40949step1; decide +kernel
      have hl : raw40949step2Labels = raw40949step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw40950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2]]
def raw40950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -3, 3], ![2, 0, -2]]
def raw40950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw40950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40950 raw40950Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw40950 raw40950Labels = mixedMoment B raw40950step0 raw40950step0Labels := by
      have hz : ∀ j, raw40950 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40950step0 = (fun i j => raw40950 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40950step0 raw40950; decide +kernel
      have hl : raw40950step0Labels = raw40950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40950 raw40950Labels permutation434 hz
    mixedMoment B raw40950step0 raw40950step0Labels = mixedMoment B raw40950step1 raw40950step1Labels := by
      have ha : raw40950step1 = (fun i j => raw40950step0 (permutation107 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40950step1 raw40950step0; decide +kernel
      have hl : raw40950step1Labels = raw40950step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40950step0 raw40950step0Labels permutation107 permutation6
    mixedMoment B raw40950step1 raw40950step1Labels = mixedMoment B raw40950step2 raw40950step2Labels := by
      have ha : raw40950step2 = -raw40950step1 := by apply Matrix.ext; change ∀ i j, raw40950step2 i j = -(raw40950step1 i j); unfold raw40950step2 raw40950step1; decide +kernel
      have hl : raw40950step2Labels = raw40950step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw40951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1]]
def raw40951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw40951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40951step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40951 raw40951Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw40951 raw40951Labels = mixedMoment B raw40951step0 raw40951step0Labels := by
      have hz : ∀ j, raw40951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40951step0 = (fun i j => raw40951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40951step0 raw40951; decide +kernel
      have hl : raw40951step0Labels = raw40951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40951 raw40951Labels permutation434 hz
    mixedMoment B raw40951step0 raw40951step0Labels = mixedMoment B raw40951step1 raw40951step1Labels := by
      have ha : raw40951step1 = (fun i j => raw40951step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40951step1 raw40951step0; decide +kernel
      have hl : raw40951step1Labels = raw40951step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40951step0 raw40951step0Labels permutation65 permutation6
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw40952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1]]
def raw40952Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40952step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40952 raw40952Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw40952 raw40952Labels = mixedMoment B raw40952step0 raw40952step0Labels := by
      have ha : raw40952step0 = (fun i j => raw40952 (permutation304 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40952step0 raw40952; decide +kernel
      have hl : raw40952step0Labels = raw40952Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40952 raw40952Labels permutation304 permutation6
    _ = mixedMoment B node3789 node3789Labels := by rfl

def raw40953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2]]
def raw40953Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw40953step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40953 raw40953Labels = mixedMoment B node3708 node3708Labels := by
  calc
    mixedMoment B raw40953 raw40953Labels = mixedMoment B raw40953step0 raw40953step0Labels := by
      have ha : raw40953step0 = (fun i j => raw40953 (permutation339 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40953step0 raw40953; decide +kernel
      have hl : raw40953step0Labels = raw40953Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40953 raw40953Labels permutation339 permutation6
    _ = mixedMoment B node3708 node3708Labels := by rfl

def raw40954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, -2, 1]]
def raw40954Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw40954step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40954 raw40954Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw40954 raw40954Labels = mixedMoment B raw40954step0 raw40954step0Labels := by
      have ha : raw40954step0 = (fun i j => raw40954 (permutation301 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40954step0 raw40954; decide +kernel
      have hl : raw40954step0Labels = raw40954Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40954 raw40954Labels permutation301 permutation6
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw40955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0]]
def raw40955Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw40955step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40955 raw40955Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw40955 raw40955Labels = mixedMoment B raw40955step0 raw40955step0Labels := by
      have ha : raw40955step0 = (fun i j => raw40955 (permutation302 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40955step0 raw40955; decide +kernel
      have hl : raw40955step0Labels = raw40955Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40955 raw40955Labels permutation302 permutation6
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw40956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, -1, 0]]
def raw40956Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40956step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40956step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40956 raw40956Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw40956 raw40956Labels = mixedMoment B raw40956step0 raw40956step0Labels := by
      have ha : raw40956step0 = (fun i j => raw40956 (permutation450 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40956step0 raw40956; decide +kernel
      have hl : raw40956step0Labels = raw40956Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40956 raw40956Labels permutation450 permutation6
    mixedMoment B raw40956step0 raw40956step0Labels = mixedMoment B raw40956step1 raw40956step1Labels := by
      have ha : raw40956step1 = -raw40956step0 := by apply Matrix.ext; change ∀ i j, raw40956step1 i j = -(raw40956step0 i j); unfold raw40956step1 raw40956step0; decide +kernel
      have hl : raw40956step1Labels = raw40956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw40957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 1, -1], ![0, -3, 3], ![1, 0, -1], ![1, 0, -1]]
def raw40957Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw40957step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw40957step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40957 raw40957Labels = mixedMoment B node1802 node1802Labels := by
  calc
    mixedMoment B raw40957 raw40957Labels = mixedMoment B raw40957step0 raw40957step0Labels := by
      have ha : raw40957step0 = (fun i j => raw40957 (permutation447 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40957step0 raw40957; decide +kernel
      have hl : raw40957step0Labels = raw40957Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40957 raw40957Labels permutation447 permutation6
    mixedMoment B raw40957step0 raw40957step0Labels = mixedMoment B raw40957step1 raw40957step1Labels := by
      have ha : raw40957step1 = -raw40957step0 := by apply Matrix.ext; change ∀ i j, raw40957step1 i j = -(raw40957step0 i j); unfold raw40957step1 raw40957step0; decide +kernel
      have hl : raw40957step1Labels = raw40957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1802 node1802Labels := by rfl

def raw40958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40958Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, -3, 3], ![2, 1, -3]]
def raw40958step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40958step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, -3, 3], ![2, 1, -3]]
def raw40958step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40958step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, 0, 2], ![-3, 2, 1]]
def raw40958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40958step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw40958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40958 raw40958Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw40958 raw40958Labels = mixedMoment B raw40958step0 raw40958step0Labels := by
      have hz : ∀ j, raw40958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40958step0 = (fun i j => raw40958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40958step0 raw40958; decide +kernel
      have hl : raw40958step0Labels = raw40958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40958 raw40958Labels permutation434 hz
    mixedMoment B raw40958step0 raw40958step0Labels = mixedMoment B raw40958step1 raw40958step1Labels := by
      have hz : ∀ j, raw40958step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40958step1 = (fun i j => raw40958step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40958step1 raw40958step0; decide +kernel
      have hl : raw40958step1Labels = raw40958step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40958step0 raw40958step0Labels permutation80 hz
    mixedMoment B raw40958step1 raw40958step1Labels = mixedMoment B raw40958step2 raw40958step2Labels := by
      have ha : raw40958step2 = (fun i j => raw40958step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40958step2 raw40958step1; decide +kernel
      have hl : raw40958step2Labels = raw40958step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40958step1 raw40958step1Labels permutation20 permutation6
    mixedMoment B raw40958step2 raw40958step2Labels = mixedMoment B raw40958step3 raw40958step3Labels := by
      have ha : raw40958step3 = -raw40958step2 := by apply Matrix.ext; change ∀ i j, raw40958step3 i j = -(raw40958step2 i j); unfold raw40958step3 raw40958step2; decide +kernel
      have hl : raw40958step3Labels = raw40958step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1819 node1819Labels := by rfl

def raw40959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40959Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![1, -3, 2]]
def raw40959step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40959step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 2, -2], ![1, 1, -2], ![1, -3, 2]]
def raw40959step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw40959step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw40959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw40959step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw40959step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical40959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw40959 raw40959Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw40959 raw40959Labels = mixedMoment B raw40959step0 raw40959step0Labels := by
      have hz : ∀ j, raw40959 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw40959step0 = (fun i j => raw40959 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw40959step0 raw40959; decide +kernel
      have hl : raw40959step0Labels = raw40959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40959 raw40959Labels permutation434 hz
    mixedMoment B raw40959step0 raw40959step0Labels = mixedMoment B raw40959step1 raw40959step1Labels := by
      have hz : ∀ j, raw40959step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw40959step1 = (fun i j => raw40959step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw40959step1 raw40959step0; decide +kernel
      have hl : raw40959step1Labels = raw40959step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw40959step0 raw40959step0Labels permutation80 hz
    mixedMoment B raw40959step1 raw40959step1Labels = mixedMoment B raw40959step2 raw40959step2Labels := by
      have ha : raw40959step2 = (fun i j => raw40959step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw40959step2 raw40959step1; decide +kernel
      have hl : raw40959step2Labels = raw40959step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw40959step1 raw40959step1Labels permutation27 permutation6
    mixedMoment B raw40959step2 raw40959step2Labels = mixedMoment B raw40959step3 raw40959step3Labels := by
      have ha : raw40959step3 = -raw40959step2 := by apply Matrix.ext; change ∀ i j, raw40959step3 i j = -(raw40959step2 i j); unfold raw40959step3 raw40959step2; decide +kernel
      have hl : raw40959step3Labels = raw40959step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3397 node3397Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
