import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6912 raw6912Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw6912 raw6912Labels = mixedMoment B raw6912step0 raw6912step0Labels := by
      have hz : ∀ j, raw6912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6912step0 = (fun i j => raw6912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6912step0 raw6912; decide +kernel
      have hl : raw6912step0Labels = raw6912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6912 raw6912Labels permutation346 hz
    mixedMoment B raw6912step0 raw6912step0Labels = mixedMoment B raw6912step1 raw6912step1Labels := by
      have ha : raw6912step1 = (fun i j => raw6912step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6912step1 raw6912step0; decide +kernel
      have hl : raw6912step1Labels = raw6912step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6912step0 raw6912step0Labels permutation34 permutation2
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw6913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6913 raw6913Labels = mixedMoment B node1226 node1226Labels := by
  calc
    mixedMoment B raw6913 raw6913Labels = mixedMoment B raw6913step0 raw6913step0Labels := by
      have hz : ∀ j, raw6913 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6913step0 = (fun i j => raw6913 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6913step0 raw6913; decide +kernel
      have hl : raw6913step0Labels = raw6913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6913 raw6913Labels permutation346 hz
    mixedMoment B raw6913step0 raw6913step0Labels = mixedMoment B raw6913step1 raw6913step1Labels := by
      have ha : raw6913step1 = (fun i j => raw6913step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6913step1 raw6913step0; decide +kernel
      have hl : raw6913step1Labels = raw6913step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6913step0 raw6913step0Labels permutation33 permutation2
    _ = mixedMoment B node1226 node1226Labels := by rfl

def raw6914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6914 raw6914Labels = mixedMoment B node1225 node1225Labels := by
  calc
    mixedMoment B raw6914 raw6914Labels = mixedMoment B raw6914step0 raw6914step0Labels := by
      have hz : ∀ j, raw6914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6914step0 = (fun i j => raw6914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6914step0 raw6914; decide +kernel
      have hl : raw6914step0Labels = raw6914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6914 raw6914Labels permutation346 hz
    _ = mixedMoment B node1225 node1225Labels := by rfl

def raw6915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw6915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6915 raw6915Labels = mixedMoment B node2578 node2578Labels := by
  calc
    mixedMoment B raw6915 raw6915Labels = mixedMoment B raw6915step0 raw6915step0Labels := by
      have ha : raw6915step0 = (fun i j => raw6915 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6915step0 raw6915; decide +kernel
      have hl : raw6915step0Labels = raw6915Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6915 raw6915Labels permutation182 permutation2
    _ = mixedMoment B node2578 node2578Labels := by rfl

def raw6916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![0, 1, -1], ![-2, 2, 0], ![-2, 1, 1]]
def raw6916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw6916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6916 raw6916Labels = mixedMoment B node2649 node2649Labels := by
  calc
    mixedMoment B raw6916 raw6916Labels = mixedMoment B raw6916step0 raw6916step0Labels := by
      have hz : ∀ j, raw6916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6916step0 = (fun i j => raw6916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6916step0 raw6916; decide +kernel
      have hl : raw6916step0Labels = raw6916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6916 raw6916Labels permutation346 hz
    mixedMoment B raw6916step0 raw6916step0Labels = mixedMoment B raw6916step1 raw6916step1Labels := by
      have ha : raw6916step1 = (fun i j => raw6916step0 (permutation83 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6916step1 raw6916step0; decide +kernel
      have hl : raw6916step1Labels = raw6916step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6916step0 raw6916step0Labels permutation83 permutation4
    mixedMoment B raw6916step1 raw6916step1Labels = mixedMoment B raw6916step2 raw6916step2Labels := by
      have ha : raw6916step2 = -raw6916step1 := by apply Matrix.ext; change ∀ i j, raw6916step2 i j = -(raw6916step1 i j); unfold raw6916step2 raw6916step1; decide +kernel
      have hl : raw6916step2Labels = raw6916step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2649 node2649Labels := by rfl

def raw6917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw6917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6917 raw6917Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw6917 raw6917Labels = mixedMoment B raw6917step0 raw6917step0Labels := by
      have hz : ∀ j, raw6917 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6917step0 = (fun i j => raw6917 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6917step0 raw6917; decide +kernel
      have hl : raw6917step0Labels = raw6917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6917 raw6917Labels permutation346 hz
    mixedMoment B raw6917step0 raw6917step0Labels = mixedMoment B raw6917step1 raw6917step1Labels := by
      have ha : raw6917step1 = (fun i j => raw6917step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6917step1 raw6917step0; decide +kernel
      have hl : raw6917step1Labels = raw6917step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6917step0 raw6917step0Labels permutation46 permutation2
    _ = mixedMoment B node2758 node2758Labels := by rfl

def raw6918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6918Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6918step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6918 raw6918Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw6918 raw6918Labels = mixedMoment B raw6918step0 raw6918step0Labels := by
      have hz : ∀ j, raw6918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6918step0 = (fun i j => raw6918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6918step0 raw6918; decide +kernel
      have hl : raw6918step0Labels = raw6918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6918 raw6918Labels permutation346 hz
    mixedMoment B raw6918step0 raw6918step0Labels = mixedMoment B raw6918step1 raw6918step1Labels := by
      have ha : raw6918step1 = (fun i j => raw6918step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6918step1 raw6918step0; decide +kernel
      have hl : raw6918step1Labels = raw6918step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6918step0 raw6918step0Labels permutation39 permutation2
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw6919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6919Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6919 raw6919Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw6919 raw6919Labels = mixedMoment B raw6919step0 raw6919step0Labels := by
      have ha : raw6919step0 = (fun i j => raw6919 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6919step0 raw6919; decide +kernel
      have hl : raw6919step0Labels = raw6919Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6919 raw6919Labels permutation158 permutation2
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw6920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6920Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6920step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6920 raw6920Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw6920 raw6920Labels = mixedMoment B raw6920step0 raw6920step0Labels := by
      have hz : ∀ j, raw6920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6920step0 = (fun i j => raw6920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6920step0 raw6920; decide +kernel
      have hl : raw6920step0Labels = raw6920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6920 raw6920Labels permutation346 hz
    mixedMoment B raw6920step0 raw6920step0Labels = mixedMoment B raw6920step1 raw6920step1Labels := by
      have ha : raw6920step1 = (fun i j => raw6920step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6920step1 raw6920step0; decide +kernel
      have hl : raw6920step1Labels = raw6920step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6920step0 raw6920step0Labels permutation34 permutation2
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw6921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6921Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6921step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6921 raw6921Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw6921 raw6921Labels = mixedMoment B raw6921step0 raw6921step0Labels := by
      have hz : ∀ j, raw6921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6921step0 = (fun i j => raw6921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6921step0 raw6921; decide +kernel
      have hl : raw6921step0Labels = raw6921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6921 raw6921Labels permutation346 hz
    mixedMoment B raw6921step0 raw6921step0Labels = mixedMoment B raw6921step1 raw6921step1Labels := by
      have ha : raw6921step1 = (fun i j => raw6921step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6921step1 raw6921step0; decide +kernel
      have hl : raw6921step1Labels = raw6921step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6921step0 raw6921step0Labels permutation33 permutation2
    _ = mixedMoment B node2499 node2499Labels := by rfl

def raw6922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6922Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6922 raw6922Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw6922 raw6922Labels = mixedMoment B raw6922step0 raw6922step0Labels := by
      have hz : ∀ j, raw6922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6922step0 = (fun i j => raw6922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6922step0 raw6922; decide +kernel
      have hl : raw6922step0Labels = raw6922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6922 raw6922Labels permutation346 hz
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw6923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6923Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6923 raw6923Labels = mixedMoment B node2646 node2646Labels := by
  calc
    mixedMoment B raw6923 raw6923Labels = mixedMoment B raw6923step0 raw6923step0Labels := by
      have ha : raw6923step0 = (fun i j => raw6923 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6923step0 raw6923; decide +kernel
      have hl : raw6923step0Labels = raw6923Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6923 raw6923Labels permutation200 permutation2
    _ = mixedMoment B node2646 node2646Labels := by rfl

def raw6924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6924Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6924 raw6924Labels = mixedMoment B node2714 node2714Labels := by
  calc
    mixedMoment B raw6924 raw6924Labels = mixedMoment B raw6924step0 raw6924step0Labels := by
      have ha : raw6924step0 = (fun i j => raw6924 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6924step0 raw6924; decide +kernel
      have hl : raw6924step0Labels = raw6924Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6924 raw6924Labels permutation166 permutation2
    _ = mixedMoment B node2714 node2714Labels := by rfl

def raw6925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6925Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6925 raw6925Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw6925 raw6925Labels = mixedMoment B raw6925step0 raw6925step0Labels := by
      have ha : raw6925step0 = (fun i j => raw6925 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6925step0 raw6925; decide +kernel
      have hl : raw6925step0Labels = raw6925Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6925 raw6925Labels permutation159 permutation2
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw6926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6926Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6926step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6926 raw6926Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw6926 raw6926Labels = mixedMoment B raw6926step0 raw6926step0Labels := by
      have ha : raw6926step0 = (fun i j => raw6926 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6926step0 raw6926; decide +kernel
      have hl : raw6926step0Labels = raw6926Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6926 raw6926Labels permutation178 permutation2
    _ = mixedMoment B node2557 node2557Labels := by rfl

def raw6927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6927Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6927 raw6927Labels = mixedMoment B node2549 node2549Labels := by
  calc
    mixedMoment B raw6927 raw6927Labels = mixedMoment B raw6927step0 raw6927step0Labels := by
      have ha : raw6927step0 = (fun i j => raw6927 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6927step0 raw6927; decide +kernel
      have hl : raw6927step0Labels = raw6927Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6927 raw6927Labels permutation177 permutation2
    _ = mixedMoment B node2549 node2549Labels := by rfl

def raw6928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6928Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6928 raw6928Labels = mixedMoment B node2548 node2548Labels := by
  calc
    mixedMoment B raw6928 raw6928Labels = mixedMoment B raw6928step0 raw6928step0Labels := by
      have ha : raw6928step0 = (fun i j => raw6928 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6928step0 raw6928; decide +kernel
      have hl : raw6928step0Labels = raw6928Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6928 raw6928Labels permutation176 permutation2
    _ = mixedMoment B node2548 node2548Labels := by rfl

def raw6929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6929Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw6929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6929 raw6929Labels = mixedMoment B node2649 node2649Labels := by
  calc
    mixedMoment B raw6929 raw6929Labels = mixedMoment B raw6929step0 raw6929step0Labels := by
      have hz : ∀ j, raw6929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6929step0 = (fun i j => raw6929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6929step0 raw6929; decide +kernel
      have hl : raw6929step0Labels = raw6929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6929 raw6929Labels permutation346 hz
    mixedMoment B raw6929step0 raw6929step0Labels = mixedMoment B raw6929step1 raw6929step1Labels := by
      have ha : raw6929step1 = (fun i j => raw6929step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6929step1 raw6929step0; decide +kernel
      have hl : raw6929step1Labels = raw6929step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6929step0 raw6929step0Labels permutation39 permutation2
    _ = mixedMoment B node2649 node2649Labels := by rfl

def raw6930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6930Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -3, 0]]
def raw6930step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6930 raw6930Labels = mixedMoment B node2648 node2648Labels := by
  calc
    mixedMoment B raw6930 raw6930Labels = mixedMoment B raw6930step0 raw6930step0Labels := by
      have hz : ∀ j, raw6930 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6930step0 = (fun i j => raw6930 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6930step0 raw6930; decide +kernel
      have hl : raw6930step0Labels = raw6930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6930 raw6930Labels permutation346 hz
    mixedMoment B raw6930step0 raw6930step0Labels = mixedMoment B raw6930step1 raw6930step1Labels := by
      have ha : raw6930step1 = (fun i j => raw6930step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6930step1 raw6930step0; decide +kernel
      have hl : raw6930step1Labels = raw6930step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6930step0 raw6930step0Labels permutation38 permutation2
    _ = mixedMoment B node2648 node2648Labels := by rfl

def raw6931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw6931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6931step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6931step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6931 raw6931Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw6931 raw6931Labels = mixedMoment B raw6931step0 raw6931step0Labels := by
      have hz : ∀ j, raw6931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6931step0 = (fun i j => raw6931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6931step0 raw6931; decide +kernel
      have hl : raw6931step0Labels = raw6931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6931 raw6931Labels permutation346 hz
    mixedMoment B raw6931step0 raw6931step0Labels = mixedMoment B raw6931step1 raw6931step1Labels := by
      have ha : raw6931step1 = (fun i j => raw6931step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6931step1 raw6931step0; decide +kernel
      have hl : raw6931step1Labels = raw6931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6931step0 raw6931step0Labels permutation151 permutation2
    mixedMoment B raw6931step1 raw6931step1Labels = mixedMoment B raw6931step2 raw6931step2Labels := by
      have ha : raw6931step2 = -raw6931step1 := by apply Matrix.ext; change ∀ i j, raw6931step2 i j = -(raw6931step1 i j); unfold raw6931step2 raw6931step1; decide +kernel
      have hl : raw6931step2Labels = raw6931step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw6932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6932step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6932 raw6932Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw6932 raw6932Labels = mixedMoment B raw6932step0 raw6932step0Labels := by
      have ha : raw6932step0 = (fun i j => raw6932 (permutation619 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6932step0 raw6932; decide +kernel
      have hl : raw6932step0Labels = raw6932Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6932 raw6932Labels permutation619 permutation7
    mixedMoment B raw6932step0 raw6932step0Labels = mixedMoment B raw6932step1 raw6932step1Labels := by
      have ha : raw6932step1 = raw6932step0 := by apply Matrix.ext; unfold raw6932step1 raw6932step0; decide +kernel
      have hl : raw6932step0Labels = labelEmbedding10 ∘ raw6932step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6932step0 raw6932step0Labels raw6932step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw6933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw6933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6933step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6933step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6933 raw6933Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw6933 raw6933Labels = mixedMoment B raw6933step0 raw6933step0Labels := by
      have hz : ∀ j, raw6933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6933step0 = (fun i j => raw6933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6933step0 raw6933; decide +kernel
      have hl : raw6933step0Labels = raw6933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6933 raw6933Labels permutation346 hz
    mixedMoment B raw6933step0 raw6933step0Labels = mixedMoment B raw6933step1 raw6933step1Labels := by
      have ha : raw6933step1 = (fun i j => raw6933step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6933step1 raw6933step0; decide +kernel
      have hl : raw6933step1Labels = raw6933step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6933step0 raw6933step0Labels permutation149 permutation2
    mixedMoment B raw6933step1 raw6933step1Labels = mixedMoment B raw6933step2 raw6933step2Labels := by
      have ha : raw6933step2 = -raw6933step1 := by apply Matrix.ext; change ∀ i j, raw6933step2 i j = -(raw6933step1 i j); unfold raw6933step2 raw6933step1; decide +kernel
      have hl : raw6933step2Labels = raw6933step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw6934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6934step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw6934step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6934step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6934step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6934step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6934step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6934 raw6934Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw6934 raw6934Labels = mixedMoment B raw6934step0 raw6934step0Labels := by
      have hz : ∀ j, raw6934 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6934step0 = (fun i j => raw6934 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6934step0 raw6934; decide +kernel
      have hl : raw6934step0Labels = raw6934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6934 raw6934Labels permutation520 hz
    mixedMoment B raw6934step0 raw6934step0Labels = mixedMoment B raw6934step1 raw6934step1Labels := by
      have hz : ∀ j, raw6934step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6934step1 = (fun i j => raw6934step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6934step1 raw6934step0; decide +kernel
      have hl : raw6934step1Labels = raw6934step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6934step0 raw6934step0Labels permutation80 hz
    mixedMoment B raw6934step1 raw6934step1Labels = mixedMoment B raw6934step2 raw6934step2Labels := by
      have ha : raw6934step2 = (fun i j => raw6934step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6934step2 raw6934step1; decide +kernel
      have hl : raw6934step2Labels = raw6934step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6934step1 raw6934step1Labels permutation28 permutation7
    mixedMoment B raw6934step2 raw6934step2Labels = mixedMoment B raw6934step3 raw6934step3Labels := by
      have ha : raw6934step3 = raw6934step2 := by apply Matrix.ext; unfold raw6934step3 raw6934step2; decide +kernel
      have hl : raw6934step2Labels = labelEmbedding10 ∘ raw6934step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6934step2 raw6934step2Labels raw6934step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw6935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6935step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6935step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6935step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6935 raw6935Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw6935 raw6935Labels = mixedMoment B raw6935step0 raw6935step0Labels := by
      have hz : ∀ j, raw6935 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6935step0 = (fun i j => raw6935 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6935step0 raw6935; decide +kernel
      have hl : raw6935step0Labels = raw6935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6935 raw6935Labels permutation346 hz
    mixedMoment B raw6935step0 raw6935step0Labels = mixedMoment B raw6935step1 raw6935step1Labels := by
      have ha : raw6935step1 = (fun i j => raw6935step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6935step1 raw6935step0; decide +kernel
      have hl : raw6935step1Labels = raw6935step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6935step0 raw6935step0Labels permutation92 permutation4
    mixedMoment B raw6935step1 raw6935step1Labels = mixedMoment B raw6935step2 raw6935step2Labels := by
      have ha : raw6935step2 = raw6935step1 := by apply Matrix.ext; unfold raw6935step2 raw6935step1; decide +kernel
      have hl : raw6935step1Labels = labelEmbedding7 ∘ raw6935step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6935step1 raw6935step1Labels raw6935step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw6936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6936step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6936 raw6936Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw6936 raw6936Labels = mixedMoment B raw6936step0 raw6936step0Labels := by
      have hz : ∀ j, raw6936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6936step0 = (fun i j => raw6936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6936step0 raw6936; decide +kernel
      have hl : raw6936step0Labels = raw6936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6936 raw6936Labels permutation346 hz
    mixedMoment B raw6936step0 raw6936step0Labels = mixedMoment B raw6936step1 raw6936step1Labels := by
      have ha : raw6936step1 = (fun i j => raw6936step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6936step1 raw6936step0; decide +kernel
      have hl : raw6936step1Labels = raw6936step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6936step0 raw6936step0Labels permutation38 permutation3
    mixedMoment B raw6936step1 raw6936step1Labels = mixedMoment B raw6936step2 raw6936step2Labels := by
      have ha : raw6936step2 = raw6936step1 := by apply Matrix.ext; unfold raw6936step2 raw6936step1; decide +kernel
      have hl : raw6936step1Labels = labelEmbedding6 ∘ raw6936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6936step1 raw6936step1Labels raw6936step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw6937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6937step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6937step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6937 raw6937Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw6937 raw6937Labels = mixedMoment B raw6937step0 raw6937step0Labels := by
      have ha : raw6937step0 = (fun i j => raw6937 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6937step0 raw6937; decide +kernel
      have hl : raw6937step0Labels = raw6937Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6937 raw6937Labels permutation182 permutation3
    mixedMoment B raw6937step0 raw6937step0Labels = mixedMoment B raw6937step1 raw6937step1Labels := by
      have ha : raw6937step1 = raw6937step0 := by apply Matrix.ext; unfold raw6937step1 raw6937step0; decide +kernel
      have hl : raw6937step0Labels = labelEmbedding6 ∘ raw6937step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6937step0 raw6937step0Labels raw6937step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw6938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6938step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6938step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6938 raw6938Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw6938 raw6938Labels = mixedMoment B raw6938step0 raw6938step0Labels := by
      have hz : ∀ j, raw6938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6938step0 = (fun i j => raw6938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6938step0 raw6938; decide +kernel
      have hl : raw6938step0Labels = raw6938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6938 raw6938Labels permutation346 hz
    mixedMoment B raw6938step0 raw6938step0Labels = mixedMoment B raw6938step1 raw6938step1Labels := by
      have ha : raw6938step1 = (fun i j => raw6938step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6938step1 raw6938step0; decide +kernel
      have hl : raw6938step1Labels = raw6938step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6938step0 raw6938step0Labels permutation38 permutation3
    mixedMoment B raw6938step1 raw6938step1Labels = mixedMoment B raw6938step2 raw6938step2Labels := by
      have ha : raw6938step2 = raw6938step1 := by apply Matrix.ext; unfold raw6938step2 raw6938step1; decide +kernel
      have hl : raw6938step1Labels = labelEmbedding6 ∘ raw6938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6938step1 raw6938step1Labels raw6938step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw6939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6939step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw6939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6939step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6939step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6939step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6939step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6939 raw6939Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw6939 raw6939Labels = mixedMoment B raw6939step0 raw6939step0Labels := by
      have hz : ∀ j, raw6939 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6939step0 = (fun i j => raw6939 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6939step0 raw6939; decide +kernel
      have hl : raw6939step0Labels = raw6939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6939 raw6939Labels permutation520 hz
    mixedMoment B raw6939step0 raw6939step0Labels = mixedMoment B raw6939step1 raw6939step1Labels := by
      have hz : ∀ j, raw6939step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6939step1 = (fun i j => raw6939step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6939step1 raw6939step0; decide +kernel
      have hl : raw6939step1Labels = raw6939step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6939step0 raw6939step0Labels permutation80 hz
    mixedMoment B raw6939step1 raw6939step1Labels = mixedMoment B raw6939step2 raw6939step2Labels := by
      have ha : raw6939step2 = (fun i j => raw6939step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6939step2 raw6939step1; decide +kernel
      have hl : raw6939step2Labels = raw6939step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6939step1 raw6939step1Labels permutation10 permutation3
    mixedMoment B raw6939step2 raw6939step2Labels = mixedMoment B raw6939step3 raw6939step3Labels := by
      have ha : raw6939step3 = raw6939step2 := by apply Matrix.ext; unfold raw6939step3 raw6939step2; decide +kernel
      have hl : raw6939step2Labels = labelEmbedding6 ∘ raw6939step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6939step2 raw6939step2Labels raw6939step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw6940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6940step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6940step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6940 raw6940Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw6940 raw6940Labels = mixedMoment B raw6940step0 raw6940step0Labels := by
      have hz : ∀ j, raw6940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6940step0 = (fun i j => raw6940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6940step0 raw6940; decide +kernel
      have hl : raw6940step0Labels = raw6940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6940 raw6940Labels permutation346 hz
    mixedMoment B raw6940step0 raw6940step0Labels = mixedMoment B raw6940step1 raw6940step1Labels := by
      have ha : raw6940step1 = (fun i j => raw6940step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6940step1 raw6940step0; decide +kernel
      have hl : raw6940step1Labels = raw6940step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6940step0 raw6940step0Labels permutation42 permutation3
    mixedMoment B raw6940step1 raw6940step1Labels = mixedMoment B raw6940step2 raw6940step2Labels := by
      have ha : raw6940step2 = raw6940step1 := by apply Matrix.ext; unfold raw6940step2 raw6940step1; decide +kernel
      have hl : raw6940step1Labels = labelEmbedding6 ∘ raw6940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6940step1 raw6940step1Labels raw6940step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw6941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6941step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6941 raw6941Labels = mixedMoment B node4409 node4409Labels := by
  calc
    mixedMoment B raw6941 raw6941Labels = mixedMoment B raw6941step0 raw6941step0Labels := by
      have ha : raw6941step0 = (fun i j => raw6941 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6941step0 raw6941; decide +kernel
      have hl : raw6941step0Labels = raw6941Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6941 raw6941Labels permutation158 permutation3
    mixedMoment B raw6941step0 raw6941step0Labels = mixedMoment B raw6941step1 raw6941step1Labels := by
      have ha : raw6941step1 = raw6941step0 := by apply Matrix.ext; unfold raw6941step1 raw6941step0; decide +kernel
      have hl : raw6941step0Labels = labelEmbedding6 ∘ raw6941step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6941step0 raw6941step0Labels raw6941step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4409 node4409Labels := by rfl

def raw6942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6942step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6942 raw6942Labels = mixedMoment B node5007 node5007Labels := by
  calc
    mixedMoment B raw6942 raw6942Labels = mixedMoment B raw6942step0 raw6942step0Labels := by
      have ha : raw6942step0 = (fun i j => raw6942 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6942step0 raw6942; decide +kernel
      have hl : raw6942step0Labels = raw6942Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6942 raw6942Labels permutation158 permutation3
    mixedMoment B raw6942step0 raw6942step0Labels = mixedMoment B raw6942step1 raw6942step1Labels := by
      have ha : raw6942step1 = raw6942step0 := by apply Matrix.ext; unfold raw6942step1 raw6942step0; decide +kernel
      have hl : raw6942step0Labels = labelEmbedding6 ∘ raw6942step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6942step0 raw6942step0Labels raw6942step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5007 node5007Labels := by rfl

def raw6943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6943step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6943 raw6943Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw6943 raw6943Labels = mixedMoment B raw6943step0 raw6943step0Labels := by
      have ha : raw6943step0 = (fun i j => raw6943 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6943step0 raw6943; decide +kernel
      have hl : raw6943step0Labels = raw6943Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6943 raw6943Labels permutation200 permutation3
    mixedMoment B raw6943step0 raw6943step0Labels = mixedMoment B raw6943step1 raw6943step1Labels := by
      have ha : raw6943step1 = raw6943step0 := by apply Matrix.ext; unfold raw6943step1 raw6943step0; decide +kernel
      have hl : raw6943step0Labels = labelEmbedding6 ∘ raw6943step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6943step0 raw6943step0Labels raw6943step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw6944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6944step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6944step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6944 raw6944Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw6944 raw6944Labels = mixedMoment B raw6944step0 raw6944step0Labels := by
      have hz : ∀ j, raw6944 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6944step0 = (fun i j => raw6944 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6944step0 raw6944; decide +kernel
      have hl : raw6944step0Labels = raw6944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6944 raw6944Labels permutation520 hz
    mixedMoment B raw6944step0 raw6944step0Labels = mixedMoment B raw6944step1 raw6944step1Labels := by
      have ha : raw6944step1 = (fun i j => raw6944step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6944step1 raw6944step0; decide +kernel
      have hl : raw6944step1Labels = raw6944step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6944step0 raw6944step0Labels permutation34 permutation3
    mixedMoment B raw6944step1 raw6944step1Labels = mixedMoment B raw6944step2 raw6944step2Labels := by
      have ha : raw6944step2 = raw6944step1 := by apply Matrix.ext; unfold raw6944step2 raw6944step1; decide +kernel
      have hl : raw6944step1Labels = labelEmbedding6 ∘ raw6944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6944step1 raw6944step1Labels raw6944step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw6945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6945step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6945 raw6945Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw6945 raw6945Labels = mixedMoment B raw6945step0 raw6945step0Labels := by
      have ha : raw6945step0 = (fun i j => raw6945 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6945step0 raw6945; decide +kernel
      have hl : raw6945step0Labels = raw6945Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6945 raw6945Labels permutation162 permutation3
    mixedMoment B raw6945step0 raw6945step0Labels = mixedMoment B raw6945step1 raw6945step1Labels := by
      have ha : raw6945step1 = raw6945step0 := by apply Matrix.ext; unfold raw6945step1 raw6945step0; decide +kernel
      have hl : raw6945step0Labels = labelEmbedding6 ∘ raw6945step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6945step0 raw6945step0Labels raw6945step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw6946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6946step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6946step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6946 raw6946Labels = mixedMoment B node4425 node4425Labels := by
  calc
    mixedMoment B raw6946 raw6946Labels = mixedMoment B raw6946step0 raw6946step0Labels := by
      have hz : ∀ j, raw6946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6946step0 = (fun i j => raw6946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6946step0 raw6946; decide +kernel
      have hl : raw6946step0Labels = raw6946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6946 raw6946Labels permutation346 hz
    mixedMoment B raw6946step0 raw6946step0Labels = mixedMoment B raw6946step1 raw6946step1Labels := by
      have ha : raw6946step1 = (fun i j => raw6946step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6946step1 raw6946step0; decide +kernel
      have hl : raw6946step1Labels = raw6946step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6946step0 raw6946step0Labels permutation34 permutation3
    mixedMoment B raw6946step1 raw6946step1Labels = mixedMoment B raw6946step2 raw6946step2Labels := by
      have ha : raw6946step2 = raw6946step1 := by apply Matrix.ext; unfold raw6946step2 raw6946step1; decide +kernel
      have hl : raw6946step1Labels = labelEmbedding6 ∘ raw6946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6946step1 raw6946step1Labels raw6946step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4425 node4425Labels := by rfl

def raw6947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6947step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6947step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6947 raw6947Labels = mixedMoment B node5019 node5019Labels := by
  calc
    mixedMoment B raw6947 raw6947Labels = mixedMoment B raw6947step0 raw6947step0Labels := by
      have hz : ∀ j, raw6947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6947step0 = (fun i j => raw6947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6947step0 raw6947; decide +kernel
      have hl : raw6947step0Labels = raw6947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6947 raw6947Labels permutation346 hz
    mixedMoment B raw6947step0 raw6947step0Labels = mixedMoment B raw6947step1 raw6947step1Labels := by
      have ha : raw6947step1 = (fun i j => raw6947step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6947step1 raw6947step0; decide +kernel
      have hl : raw6947step1Labels = raw6947step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6947step0 raw6947step0Labels permutation34 permutation3
    mixedMoment B raw6947step1 raw6947step1Labels = mixedMoment B raw6947step2 raw6947step2Labels := by
      have ha : raw6947step2 = raw6947step1 := by apply Matrix.ext; unfold raw6947step2 raw6947step1; decide +kernel
      have hl : raw6947step1Labels = labelEmbedding6 ∘ raw6947step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6947step1 raw6947step1Labels raw6947step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5019 node5019Labels := by rfl

def raw6948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6948step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6948 raw6948Labels = mixedMoment B node5060 node5060Labels := by
  calc
    mixedMoment B raw6948 raw6948Labels = mixedMoment B raw6948step0 raw6948step0Labels := by
      have ha : raw6948step0 = (fun i j => raw6948 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6948step0 raw6948; decide +kernel
      have hl : raw6948step0Labels = raw6948Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6948 raw6948Labels permutation178 permutation3
    mixedMoment B raw6948step0 raw6948step0Labels = mixedMoment B raw6948step1 raw6948step1Labels := by
      have ha : raw6948step1 = raw6948step0 := by apply Matrix.ext; unfold raw6948step1 raw6948step0; decide +kernel
      have hl : raw6948step0Labels = labelEmbedding6 ∘ raw6948step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6948step0 raw6948step0Labels raw6948step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5060 node5060Labels := by rfl

def raw6949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw6949step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6949step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6949step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6949step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6949step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6949step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6949step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6949 raw6949Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw6949 raw6949Labels = mixedMoment B raw6949step0 raw6949step0Labels := by
      have hz : ∀ j, raw6949 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6949step0 = (fun i j => raw6949 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6949step0 raw6949; decide +kernel
      have hl : raw6949step0Labels = raw6949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6949 raw6949Labels permutation520 hz
    mixedMoment B raw6949step0 raw6949step0Labels = mixedMoment B raw6949step1 raw6949step1Labels := by
      have hz : ∀ j, raw6949step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6949step1 = (fun i j => raw6949step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6949step1 raw6949step0; decide +kernel
      have hl : raw6949step1Labels = raw6949step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6949step0 raw6949step0Labels permutation80 hz
    mixedMoment B raw6949step1 raw6949step1Labels = mixedMoment B raw6949step2 raw6949step2Labels := by
      have ha : raw6949step2 = (fun i j => raw6949step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6949step2 raw6949step1; decide +kernel
      have hl : raw6949step2Labels = raw6949step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6949step1 raw6949step1Labels permutation8 permutation3
    mixedMoment B raw6949step2 raw6949step2Labels = mixedMoment B raw6949step3 raw6949step3Labels := by
      have ha : raw6949step3 = raw6949step2 := by apply Matrix.ext; unfold raw6949step3 raw6949step2; decide +kernel
      have hl : raw6949step2Labels = labelEmbedding6 ∘ raw6949step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6949step2 raw6949step2Labels raw6949step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw6950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6950step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6950step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6950step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6950step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6950 raw6950Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw6950 raw6950Labels = mixedMoment B raw6950step0 raw6950step0Labels := by
      have hz : ∀ j, raw6950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6950step0 = (fun i j => raw6950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6950step0 raw6950; decide +kernel
      have hl : raw6950step0Labels = raw6950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6950 raw6950Labels permutation346 hz
    mixedMoment B raw6950step0 raw6950step0Labels = mixedMoment B raw6950step1 raw6950step1Labels := by
      have ha : raw6950step1 = (fun i j => raw6950step0 (permutation95 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6950step1 raw6950step0; decide +kernel
      have hl : raw6950step1Labels = raw6950step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6950step0 raw6950step0Labels permutation95 permutation4
    mixedMoment B raw6950step1 raw6950step1Labels = mixedMoment B raw6950step2 raw6950step2Labels := by
      have ha : raw6950step2 = raw6950step1 := by apply Matrix.ext; unfold raw6950step2 raw6950step1; decide +kernel
      have hl : raw6950step1Labels = labelEmbedding7 ∘ raw6950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6950step1 raw6950step1Labels raw6950step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw6951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6951step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6951step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6951 raw6951Labels = mixedMoment B node4411 node4411Labels := by
  calc
    mixedMoment B raw6951 raw6951Labels = mixedMoment B raw6951step0 raw6951step0Labels := by
      have hz : ∀ j, raw6951 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6951step0 = (fun i j => raw6951 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6951step0 raw6951; decide +kernel
      have hl : raw6951step0Labels = raw6951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6951 raw6951Labels permutation346 hz
    mixedMoment B raw6951step0 raw6951step0Labels = mixedMoment B raw6951step1 raw6951step1Labels := by
      have ha : raw6951step1 = (fun i j => raw6951step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6951step1 raw6951step0; decide +kernel
      have hl : raw6951step1Labels = raw6951step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6951step0 raw6951step0Labels permutation33 permutation3
    mixedMoment B raw6951step1 raw6951step1Labels = mixedMoment B raw6951step2 raw6951step2Labels := by
      have ha : raw6951step2 = raw6951step1 := by apply Matrix.ext; unfold raw6951step2 raw6951step1; decide +kernel
      have hl : raw6951step1Labels = labelEmbedding6 ∘ raw6951step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6951step1 raw6951step1Labels raw6951step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4411 node4411Labels := by rfl

def raw6952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6952step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6952step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6952step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6952step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6952step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6952 raw6952Labels = mixedMoment B node5009 node5009Labels := by
  calc
    mixedMoment B raw6952 raw6952Labels = mixedMoment B raw6952step0 raw6952step0Labels := by
      have hz : ∀ j, raw6952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6952step0 = (fun i j => raw6952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6952step0 raw6952; decide +kernel
      have hl : raw6952step0Labels = raw6952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6952 raw6952Labels permutation346 hz
    mixedMoment B raw6952step0 raw6952step0Labels = mixedMoment B raw6952step1 raw6952step1Labels := by
      have ha : raw6952step1 = (fun i j => raw6952step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6952step1 raw6952step0; decide +kernel
      have hl : raw6952step1Labels = raw6952step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6952step0 raw6952step0Labels permutation33 permutation3
    mixedMoment B raw6952step1 raw6952step1Labels = mixedMoment B raw6952step2 raw6952step2Labels := by
      have ha : raw6952step2 = raw6952step1 := by apply Matrix.ext; unfold raw6952step2 raw6952step1; decide +kernel
      have hl : raw6952step1Labels = labelEmbedding6 ∘ raw6952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6952step1 raw6952step1Labels raw6952step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5009 node5009Labels := by rfl

def raw6953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6953step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6953 raw6953Labels = mixedMoment B node5053 node5053Labels := by
  calc
    mixedMoment B raw6953 raw6953Labels = mixedMoment B raw6953step0 raw6953step0Labels := by
      have ha : raw6953step0 = (fun i j => raw6953 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6953step0 raw6953; decide +kernel
      have hl : raw6953step0Labels = raw6953Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6953 raw6953Labels permutation177 permutation3
    mixedMoment B raw6953step0 raw6953step0Labels = mixedMoment B raw6953step1 raw6953step1Labels := by
      have ha : raw6953step1 = raw6953step0 := by apply Matrix.ext; unfold raw6953step1 raw6953step0; decide +kernel
      have hl : raw6953step0Labels = labelEmbedding6 ∘ raw6953step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6953step0 raw6953step0Labels raw6953step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5053 node5053Labels := by rfl

def raw6954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6954step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6954step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6954step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6954 raw6954Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw6954 raw6954Labels = mixedMoment B raw6954step0 raw6954step0Labels := by
      have hz : ∀ j, raw6954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6954step0 = (fun i j => raw6954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6954step0 raw6954; decide +kernel
      have hl : raw6954step0Labels = raw6954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6954 raw6954Labels permutation346 hz
    mixedMoment B raw6954step0 raw6954step0Labels = mixedMoment B raw6954step1 raw6954step1Labels := by
      have ha : raw6954step1 = (fun i j => raw6954step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6954step1 raw6954step0; decide +kernel
      have hl : raw6954step1Labels = raw6954step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6954step0 raw6954step0Labels permutation39 permutation3
    mixedMoment B raw6954step1 raw6954step1Labels = mixedMoment B raw6954step2 raw6954step2Labels := by
      have ha : raw6954step2 = raw6954step1 := by apply Matrix.ext; unfold raw6954step2 raw6954step1; decide +kernel
      have hl : raw6954step1Labels = labelEmbedding6 ∘ raw6954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6954step1 raw6954step1Labels raw6954step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw6955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw6955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw6955step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6955step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6955step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6955 raw6955Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw6955 raw6955Labels = mixedMoment B raw6955step0 raw6955step0Labels := by
      have hz : ∀ j, raw6955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6955step0 = (fun i j => raw6955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6955step0 raw6955; decide +kernel
      have hl : raw6955step0Labels = raw6955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6955 raw6955Labels permutation346 hz
    mixedMoment B raw6955step0 raw6955step0Labels = mixedMoment B raw6955step1 raw6955step1Labels := by
      have ha : raw6955step1 = (fun i j => raw6955step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6955step1 raw6955step0; decide +kernel
      have hl : raw6955step1Labels = raw6955step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6955step0 raw6955step0Labels permutation33 permutation3
    mixedMoment B raw6955step1 raw6955step1Labels = mixedMoment B raw6955step2 raw6955step2Labels := by
      have ha : raw6955step2 = raw6955step1 := by apply Matrix.ext; unfold raw6955step2 raw6955step1; decide +kernel
      have hl : raw6955step1Labels = labelEmbedding6 ∘ raw6955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6955step1 raw6955step1Labels raw6955step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw6956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6956step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6956step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6956step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6956 raw6956Labels = mixedMoment B node4410 node4410Labels := by
  calc
    mixedMoment B raw6956 raw6956Labels = mixedMoment B raw6956step0 raw6956step0Labels := by
      have hz : ∀ j, raw6956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6956step0 = (fun i j => raw6956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6956step0 raw6956; decide +kernel
      have hl : raw6956step0Labels = raw6956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6956 raw6956Labels permutation346 hz
    mixedMoment B raw6956step0 raw6956step0Labels = mixedMoment B raw6956step1 raw6956step1Labels := by
      have ha : raw6956step1 = (fun i j => raw6956step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6956step1 raw6956step0; decide +kernel
      have hl : raw6956step1Labels = raw6956step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6956step0 raw6956step0Labels permutation32 permutation3
    mixedMoment B raw6956step1 raw6956step1Labels = mixedMoment B raw6956step2 raw6956step2Labels := by
      have ha : raw6956step2 = raw6956step1 := by apply Matrix.ext; unfold raw6956step2 raw6956step1; decide +kernel
      have hl : raw6956step1Labels = labelEmbedding6 ∘ raw6956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6956step1 raw6956step1Labels raw6956step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4410 node4410Labels := by rfl

def raw6957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6957step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6957step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6957 raw6957Labels = mixedMoment B node5008 node5008Labels := by
  calc
    mixedMoment B raw6957 raw6957Labels = mixedMoment B raw6957step0 raw6957step0Labels := by
      have hz : ∀ j, raw6957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6957step0 = (fun i j => raw6957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6957step0 raw6957; decide +kernel
      have hl : raw6957step0Labels = raw6957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6957 raw6957Labels permutation346 hz
    mixedMoment B raw6957step0 raw6957step0Labels = mixedMoment B raw6957step1 raw6957step1Labels := by
      have ha : raw6957step1 = (fun i j => raw6957step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6957step1 raw6957step0; decide +kernel
      have hl : raw6957step1Labels = raw6957step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6957step0 raw6957step0Labels permutation32 permutation3
    mixedMoment B raw6957step1 raw6957step1Labels = mixedMoment B raw6957step2 raw6957step2Labels := by
      have ha : raw6957step2 = raw6957step1 := by apply Matrix.ext; unfold raw6957step2 raw6957step1; decide +kernel
      have hl : raw6957step1Labels = labelEmbedding6 ∘ raw6957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6957step1 raw6957step1Labels raw6957step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5008 node5008Labels := by rfl

def raw6958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6958step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6958step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6958 raw6958Labels = mixedMoment B node5052 node5052Labels := by
  calc
    mixedMoment B raw6958 raw6958Labels = mixedMoment B raw6958step0 raw6958step0Labels := by
      have ha : raw6958step0 = (fun i j => raw6958 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6958step0 raw6958; decide +kernel
      have hl : raw6958step0Labels = raw6958Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6958 raw6958Labels permutation176 permutation3
    mixedMoment B raw6958step0 raw6958step0Labels = mixedMoment B raw6958step1 raw6958step1Labels := by
      have ha : raw6958step1 = raw6958step0 := by apply Matrix.ext; unfold raw6958step1 raw6958step0; decide +kernel
      have hl : raw6958step0Labels = labelEmbedding6 ∘ raw6958step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6958step0 raw6958step0Labels raw6958step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5052 node5052Labels := by rfl

def raw6959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6959step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw6959step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw6959step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6959 raw6959Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw6959 raw6959Labels = mixedMoment B raw6959step0 raw6959step0Labels := by
      have hz : ∀ j, raw6959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6959step0 = (fun i j => raw6959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6959step0 raw6959; decide +kernel
      have hl : raw6959step0Labels = raw6959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6959 raw6959Labels permutation346 hz
    mixedMoment B raw6959step0 raw6959step0Labels = mixedMoment B raw6959step1 raw6959step1Labels := by
      have ha : raw6959step1 = (fun i j => raw6959step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6959step1 raw6959step0; decide +kernel
      have hl : raw6959step1Labels = raw6959step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6959step0 raw6959step0Labels permutation149 permutation2
    mixedMoment B raw6959step1 raw6959step1Labels = mixedMoment B raw6959step2 raw6959step2Labels := by
      have ha : raw6959step2 = -raw6959step1 := by apply Matrix.ext; change ∀ i j, raw6959step2 i j = -(raw6959step1 i j); unfold raw6959step2 raw6959step1; decide +kernel
      have hl : raw6959step2Labels = raw6959step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw6960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![3, -1, -2]]
def raw6960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw6960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw6960step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw6960step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6960step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw6960step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6960 raw6960Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw6960 raw6960Labels = mixedMoment B raw6960step0 raw6960step0Labels := by
      have hz : ∀ j, raw6960 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6960step0 = (fun i j => raw6960 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6960step0 raw6960; decide +kernel
      have hl : raw6960step0Labels = raw6960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6960 raw6960Labels permutation520 hz
    mixedMoment B raw6960step0 raw6960step0Labels = mixedMoment B raw6960step1 raw6960step1Labels := by
      have hz : ∀ j, raw6960step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6960step1 = (fun i j => raw6960step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6960step1 raw6960step0; decide +kernel
      have hl : raw6960step1Labels = raw6960step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6960step0 raw6960step0Labels permutation80 hz
    mixedMoment B raw6960step1 raw6960step1Labels = mixedMoment B raw6960step2 raw6960step2Labels := by
      have ha : raw6960step2 = (fun i j => raw6960step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6960step2 raw6960step1; decide +kernel
      have hl : raw6960step2Labels = raw6960step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6960step1 raw6960step1Labels permutation29 permutation2
    mixedMoment B raw6960step2 raw6960step2Labels = mixedMoment B raw6960step3 raw6960step3Labels := by
      have ha : raw6960step3 = -raw6960step2 := by apply Matrix.ext; change ∀ i j, raw6960step3 i j = -(raw6960step2 i j); unfold raw6960step3 raw6960step2; decide +kernel
      have hl : raw6960step3Labels = raw6960step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw6961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6961Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6961step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6961step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6961step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6961 raw6961Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw6961 raw6961Labels = mixedMoment B raw6961step0 raw6961step0Labels := by
      have hz : ∀ j, raw6961 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6961step0 = (fun i j => raw6961 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6961step0 raw6961; decide +kernel
      have hl : raw6961step0Labels = raw6961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6961 raw6961Labels permutation346 hz
    mixedMoment B raw6961step0 raw6961step0Labels = mixedMoment B raw6961step1 raw6961step1Labels := by
      have ha : raw6961step1 = (fun i j => raw6961step0 (permutation82 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6961step1 raw6961step0; decide +kernel
      have hl : raw6961step1Labels = raw6961step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6961step0 raw6961step0Labels permutation82 permutation6
    mixedMoment B raw6961step1 raw6961step1Labels = mixedMoment B raw6961step2 raw6961step2Labels := by
      have ha : raw6961step2 = -raw6961step1 := by apply Matrix.ext; change ∀ i j, raw6961step2 i j = -(raw6961step1 i j); unfold raw6961step2 raw6961step1; decide +kernel
      have hl : raw6961step2Labels = raw6961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw6962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6962Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6962step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6962step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6962 raw6962Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw6962 raw6962Labels = mixedMoment B raw6962step0 raw6962step0Labels := by
      have ha : raw6962step0 = (fun i j => raw6962 (permutation445 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6962step0 raw6962; decide +kernel
      have hl : raw6962step0Labels = raw6962Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6962 raw6962Labels permutation445 permutation6
    mixedMoment B raw6962step0 raw6962step0Labels = mixedMoment B raw6962step1 raw6962step1Labels := by
      have ha : raw6962step1 = -raw6962step0 := by apply Matrix.ext; change ∀ i j, raw6962step1 i j = -(raw6962step0 i j); unfold raw6962step1 raw6962step0; decide +kernel
      have hl : raw6962step1Labels = raw6962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw6963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6963Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6963step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw6963step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6963 raw6963Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw6963 raw6963Labels = mixedMoment B raw6963step0 raw6963step0Labels := by
      have hz : ∀ j, raw6963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6963step0 = (fun i j => raw6963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6963step0 raw6963; decide +kernel
      have hl : raw6963step0Labels = raw6963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6963 raw6963Labels permutation346 hz
    mixedMoment B raw6963step0 raw6963step0Labels = mixedMoment B raw6963step1 raw6963step1Labels := by
      have ha : raw6963step1 = (fun i j => raw6963step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6963step1 raw6963step0; decide +kernel
      have hl : raw6963step1Labels = raw6963step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6963step0 raw6963step0Labels permutation38 permutation3
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw6964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6964Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6964step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6964step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw6964step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6964step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6964step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6964step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6964 raw6964Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw6964 raw6964Labels = mixedMoment B raw6964step0 raw6964step0Labels := by
      have hz : ∀ j, raw6964 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6964step0 = (fun i j => raw6964 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6964step0 raw6964; decide +kernel
      have hl : raw6964step0Labels = raw6964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6964 raw6964Labels permutation520 hz
    mixedMoment B raw6964step0 raw6964step0Labels = mixedMoment B raw6964step1 raw6964step1Labels := by
      have hz : ∀ j, raw6964step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6964step1 = (fun i j => raw6964step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6964step1 raw6964step0; decide +kernel
      have hl : raw6964step1Labels = raw6964step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6964step0 raw6964step0Labels permutation80 hz
    mixedMoment B raw6964step1 raw6964step1Labels = mixedMoment B raw6964step2 raw6964step2Labels := by
      have ha : raw6964step2 = (fun i j => raw6964step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6964step2 raw6964step1; decide +kernel
      have hl : raw6964step2Labels = raw6964step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6964step1 raw6964step1Labels permutation20 permutation6
    mixedMoment B raw6964step2 raw6964step2Labels = mixedMoment B raw6964step3 raw6964step3Labels := by
      have ha : raw6964step3 = -raw6964step2 := by apply Matrix.ext; change ∀ i j, raw6964step3 i j = -(raw6964step2 i j); unfold raw6964step3 raw6964step2; decide +kernel
      have hl : raw6964step3Labels = raw6964step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw6965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6965Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6965step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6965step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6965 raw6965Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw6965 raw6965Labels = mixedMoment B raw6965step0 raw6965step0Labels := by
      have hz : ∀ j, raw6965 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6965step0 = (fun i j => raw6965 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6965step0 raw6965; decide +kernel
      have hl : raw6965step0Labels = raw6965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6965 raw6965Labels permutation346 hz
    mixedMoment B raw6965step0 raw6965step0Labels = mixedMoment B raw6965step1 raw6965step1Labels := by
      have ha : raw6965step1 = (fun i j => raw6965step0 (permutation82 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6965step1 raw6965step0; decide +kernel
      have hl : raw6965step1Labels = raw6965step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6965step0 raw6965step0Labels permutation82 permutation6
    mixedMoment B raw6965step1 raw6965step1Labels = mixedMoment B raw6965step2 raw6965step2Labels := by
      have ha : raw6965step2 = -raw6965step1 := by apply Matrix.ext; change ∀ i j, raw6965step2 i j = -(raw6965step1 i j); unfold raw6965step2 raw6965step1; decide +kernel
      have hl : raw6965step2Labels = raw6965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw6966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6966Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6966step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6966step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6966 raw6966Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw6966 raw6966Labels = mixedMoment B raw6966step0 raw6966step0Labels := by
      have hz : ∀ j, raw6966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6966step0 = (fun i j => raw6966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6966step0 raw6966; decide +kernel
      have hl : raw6966step0Labels = raw6966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6966 raw6966Labels permutation346 hz
    mixedMoment B raw6966step0 raw6966step0Labels = mixedMoment B raw6966step1 raw6966step1Labels := by
      have ha : raw6966step1 = (fun i j => raw6966step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6966step1 raw6966step0; decide +kernel
      have hl : raw6966step1Labels = raw6966step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6966step0 raw6966step0Labels permutation38 permutation3
    _ = mixedMoment B node1058 node1058Labels := by rfl

def raw6967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6967Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6967 raw6967Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw6967 raw6967Labels = mixedMoment B raw6967step0 raw6967step0Labels := by
      have ha : raw6967step0 = (fun i j => raw6967 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6967step0 raw6967; decide +kernel
      have hl : raw6967step0Labels = raw6967Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6967 raw6967Labels permutation182 permutation3
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw6968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6968Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6968step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6968step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6968 raw6968Labels = mixedMoment B node2638 node2638Labels := by
  calc
    mixedMoment B raw6968 raw6968Labels = mixedMoment B raw6968step0 raw6968step0Labels := by
      have hz : ∀ j, raw6968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6968step0 = (fun i j => raw6968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6968step0 raw6968; decide +kernel
      have hl : raw6968step0Labels = raw6968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6968 raw6968Labels permutation346 hz
    mixedMoment B raw6968step0 raw6968step0Labels = mixedMoment B raw6968step1 raw6968step1Labels := by
      have ha : raw6968step1 = (fun i j => raw6968step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6968step1 raw6968step0; decide +kernel
      have hl : raw6968step1Labels = raw6968step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6968step0 raw6968step0Labels permutation38 permutation3
    _ = mixedMoment B node2638 node2638Labels := by rfl

def raw6969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6969Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6969step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6969step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw6969step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6969step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6969 raw6969Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw6969 raw6969Labels = mixedMoment B raw6969step0 raw6969step0Labels := by
      have hz : ∀ j, raw6969 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6969step0 = (fun i j => raw6969 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6969step0 raw6969; decide +kernel
      have hl : raw6969step0Labels = raw6969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6969 raw6969Labels permutation520 hz
    mixedMoment B raw6969step0 raw6969step0Labels = mixedMoment B raw6969step1 raw6969step1Labels := by
      have hz : ∀ j, raw6969step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6969step1 = (fun i j => raw6969step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6969step1 raw6969step0; decide +kernel
      have hl : raw6969step1Labels = raw6969step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6969step0 raw6969step0Labels permutation80 hz
    mixedMoment B raw6969step1 raw6969step1Labels = mixedMoment B raw6969step2 raw6969step2Labels := by
      have ha : raw6969step2 = (fun i j => raw6969step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6969step2 raw6969step1; decide +kernel
      have hl : raw6969step2Labels = raw6969step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6969step1 raw6969step1Labels permutation10 permutation3
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw6970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6970Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6970step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6970step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6970 raw6970Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw6970 raw6970Labels = mixedMoment B raw6970step0 raw6970step0Labels := by
      have hz : ∀ j, raw6970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6970step0 = (fun i j => raw6970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6970step0 raw6970; decide +kernel
      have hl : raw6970step0Labels = raw6970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6970 raw6970Labels permutation346 hz
    mixedMoment B raw6970step0 raw6970step0Labels = mixedMoment B raw6970step1 raw6970step1Labels := by
      have ha : raw6970step1 = (fun i j => raw6970step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6970step1 raw6970step0; decide +kernel
      have hl : raw6970step1Labels = raw6970step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6970step0 raw6970step0Labels permutation42 permutation3
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw6971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6971Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6971 raw6971Labels = mixedMoment B node990 node990Labels := by
  calc
    mixedMoment B raw6971 raw6971Labels = mixedMoment B raw6971step0 raw6971step0Labels := by
      have ha : raw6971step0 = (fun i j => raw6971 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6971step0 raw6971; decide +kernel
      have hl : raw6971step0Labels = raw6971Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6971 raw6971Labels permutation158 permutation3
    _ = mixedMoment B node990 node990Labels := by rfl

def raw6972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6972Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6972 raw6972Labels = mixedMoment B node2392 node2392Labels := by
  calc
    mixedMoment B raw6972 raw6972Labels = mixedMoment B raw6972step0 raw6972step0Labels := by
      have ha : raw6972step0 = (fun i j => raw6972 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6972step0 raw6972; decide +kernel
      have hl : raw6972step0Labels = raw6972Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6972 raw6972Labels permutation158 permutation3
    _ = mixedMoment B node2392 node2392Labels := by rfl

def raw6973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6973Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6973 raw6973Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw6973 raw6973Labels = mixedMoment B raw6973step0 raw6973step0Labels := by
      have ha : raw6973step0 = (fun i j => raw6973 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6973step0 raw6973; decide +kernel
      have hl : raw6973step0Labels = raw6973Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6973 raw6973Labels permutation200 permutation3
    _ = mixedMoment B node2617 node2617Labels := by rfl

def raw6974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6974Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6974step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6974step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6974 raw6974Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw6974 raw6974Labels = mixedMoment B raw6974step0 raw6974step0Labels := by
      have hz : ∀ j, raw6974 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6974step0 = (fun i j => raw6974 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6974step0 raw6974; decide +kernel
      have hl : raw6974step0Labels = raw6974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6974 raw6974Labels permutation520 hz
    mixedMoment B raw6974step0 raw6974step0Labels = mixedMoment B raw6974step1 raw6974step1Labels := by
      have ha : raw6974step1 = (fun i j => raw6974step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6974step1 raw6974step0; decide +kernel
      have hl : raw6974step1Labels = raw6974step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6974step0 raw6974step0Labels permutation34 permutation3
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw6975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6975Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6975 raw6975Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw6975 raw6975Labels = mixedMoment B raw6975step0 raw6975step0Labels := by
      have ha : raw6975step0 = (fun i j => raw6975 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6975step0 raw6975; decide +kernel
      have hl : raw6975step0Labels = raw6975Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6975 raw6975Labels permutation162 permutation3
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw6976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6976step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6976step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6976 raw6976Labels = mixedMoment B node1006 node1006Labels := by
  calc
    mixedMoment B raw6976 raw6976Labels = mixedMoment B raw6976step0 raw6976step0Labels := by
      have hz : ∀ j, raw6976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6976step0 = (fun i j => raw6976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6976step0 raw6976; decide +kernel
      have hl : raw6976step0Labels = raw6976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6976 raw6976Labels permutation346 hz
    mixedMoment B raw6976step0 raw6976step0Labels = mixedMoment B raw6976step1 raw6976step1Labels := by
      have ha : raw6976step1 = (fun i j => raw6976step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6976step1 raw6976step0; decide +kernel
      have hl : raw6976step1Labels = raw6976step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6976step0 raw6976step0Labels permutation34 permutation3
    _ = mixedMoment B node1006 node1006Labels := by rfl

def raw6977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6977 raw6977Labels = mixedMoment B node2405 node2405Labels := by
  calc
    mixedMoment B raw6977 raw6977Labels = mixedMoment B raw6977step0 raw6977step0Labels := by
      have hz : ∀ j, raw6977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6977step0 = (fun i j => raw6977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6977step0 raw6977; decide +kernel
      have hl : raw6977step0Labels = raw6977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6977 raw6977Labels permutation346 hz
    mixedMoment B raw6977step0 raw6977step0Labels = mixedMoment B raw6977step1 raw6977step1Labels := by
      have ha : raw6977step1 = (fun i j => raw6977step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6977step1 raw6977step0; decide +kernel
      have hl : raw6977step1Labels = raw6977step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6977step0 raw6977step0Labels permutation34 permutation3
    _ = mixedMoment B node2405 node2405Labels := by rfl

def raw6978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6978 raw6978Labels = mixedMoment B node2463 node2463Labels := by
  calc
    mixedMoment B raw6978 raw6978Labels = mixedMoment B raw6978step0 raw6978step0Labels := by
      have ha : raw6978step0 = (fun i j => raw6978 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6978step0 raw6978; decide +kernel
      have hl : raw6978step0Labels = raw6978Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6978 raw6978Labels permutation178 permutation3
    _ = mixedMoment B node2463 node2463Labels := by rfl

def raw6979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw6979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6979step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6979 raw6979Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw6979 raw6979Labels = mixedMoment B raw6979step0 raw6979step0Labels := by
      have hz : ∀ j, raw6979 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6979step0 = (fun i j => raw6979 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6979step0 raw6979; decide +kernel
      have hl : raw6979step0Labels = raw6979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6979 raw6979Labels permutation520 hz
    mixedMoment B raw6979step0 raw6979step0Labels = mixedMoment B raw6979step1 raw6979step1Labels := by
      have hz : ∀ j, raw6979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6979step1 = (fun i j => raw6979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6979step1 raw6979step0; decide +kernel
      have hl : raw6979step1Labels = raw6979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6979step0 raw6979step0Labels permutation80 hz
    mixedMoment B raw6979step1 raw6979step1Labels = mixedMoment B raw6979step2 raw6979step2Labels := by
      have ha : raw6979step2 = (fun i j => raw6979step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6979step2 raw6979step1; decide +kernel
      have hl : raw6979step2Labels = raw6979step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6979step1 raw6979step1Labels permutation8 permutation3
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw6980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6980Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6980step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw6980step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6980 raw6980Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw6980 raw6980Labels = mixedMoment B raw6980step0 raw6980step0Labels := by
      have hz : ∀ j, raw6980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6980step0 = (fun i j => raw6980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6980step0 raw6980; decide +kernel
      have hl : raw6980step0Labels = raw6980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6980 raw6980Labels permutation346 hz
    mixedMoment B raw6980step0 raw6980step0Labels = mixedMoment B raw6980step1 raw6980step1Labels := by
      have ha : raw6980step1 = (fun i j => raw6980step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6980step1 raw6980step0; decide +kernel
      have hl : raw6980step1Labels = raw6980step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6980step0 raw6980step0Labels permutation37 permutation3
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw6981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6981Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6981step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6981step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6981 raw6981Labels = mixedMoment B node992 node992Labels := by
  calc
    mixedMoment B raw6981 raw6981Labels = mixedMoment B raw6981step0 raw6981step0Labels := by
      have hz : ∀ j, raw6981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6981step0 = (fun i j => raw6981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6981step0 raw6981; decide +kernel
      have hl : raw6981step0Labels = raw6981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6981 raw6981Labels permutation346 hz
    mixedMoment B raw6981step0 raw6981step0Labels = mixedMoment B raw6981step1 raw6981step1Labels := by
      have ha : raw6981step1 = (fun i j => raw6981step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6981step1 raw6981step0; decide +kernel
      have hl : raw6981step1Labels = raw6981step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6981step0 raw6981step0Labels permutation33 permutation3
    _ = mixedMoment B node992 node992Labels := by rfl

def raw6982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6982Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6982step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6982 raw6982Labels = mixedMoment B node2394 node2394Labels := by
  calc
    mixedMoment B raw6982 raw6982Labels = mixedMoment B raw6982step0 raw6982step0Labels := by
      have hz : ∀ j, raw6982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6982step0 = (fun i j => raw6982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6982step0 raw6982; decide +kernel
      have hl : raw6982step0Labels = raw6982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6982 raw6982Labels permutation346 hz
    mixedMoment B raw6982step0 raw6982step0Labels = mixedMoment B raw6982step1 raw6982step1Labels := by
      have ha : raw6982step1 = (fun i j => raw6982step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6982step1 raw6982step0; decide +kernel
      have hl : raw6982step1Labels = raw6982step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6982step0 raw6982step0Labels permutation33 permutation3
    _ = mixedMoment B node2394 node2394Labels := by rfl

def raw6983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6983Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw6983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6983 raw6983Labels = mixedMoment B node2455 node2455Labels := by
  calc
    mixedMoment B raw6983 raw6983Labels = mixedMoment B raw6983step0 raw6983step0Labels := by
      have ha : raw6983step0 = (fun i j => raw6983 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6983step0 raw6983; decide +kernel
      have hl : raw6983step0Labels = raw6983Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6983 raw6983Labels permutation177 permutation3
    _ = mixedMoment B node2455 node2455Labels := by rfl

def raw6984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6984Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw6984step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6984 raw6984Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw6984 raw6984Labels = mixedMoment B raw6984step0 raw6984step0Labels := by
      have hz : ∀ j, raw6984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6984step0 = (fun i j => raw6984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6984step0 raw6984; decide +kernel
      have hl : raw6984step0Labels = raw6984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6984 raw6984Labels permutation346 hz
    mixedMoment B raw6984step0 raw6984step0Labels = mixedMoment B raw6984step1 raw6984step1Labels := by
      have ha : raw6984step1 = (fun i j => raw6984step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6984step1 raw6984step0; decide +kernel
      have hl : raw6984step1Labels = raw6984step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6984step0 raw6984step0Labels permutation39 permutation3
    _ = mixedMoment B node2620 node2620Labels := by rfl

def raw6985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw6985Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw6985step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6985 raw6985Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw6985 raw6985Labels = mixedMoment B raw6985step0 raw6985step0Labels := by
      have hz : ∀ j, raw6985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6985step0 = (fun i j => raw6985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6985step0 raw6985; decide +kernel
      have hl : raw6985step0Labels = raw6985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6985 raw6985Labels permutation346 hz
    mixedMoment B raw6985step0 raw6985step0Labels = mixedMoment B raw6985step1 raw6985step1Labels := by
      have ha : raw6985step1 = (fun i j => raw6985step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6985step1 raw6985step0; decide +kernel
      have hl : raw6985step1Labels = raw6985step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6985step0 raw6985step0Labels permutation33 permutation3
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw6986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6986Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6986step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6986 raw6986Labels = mixedMoment B node991 node991Labels := by
  calc
    mixedMoment B raw6986 raw6986Labels = mixedMoment B raw6986step0 raw6986step0Labels := by
      have hz : ∀ j, raw6986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6986step0 = (fun i j => raw6986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6986step0 raw6986; decide +kernel
      have hl : raw6986step0Labels = raw6986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6986 raw6986Labels permutation346 hz
    mixedMoment B raw6986step0 raw6986step0Labels = mixedMoment B raw6986step1 raw6986step1Labels := by
      have ha : raw6986step1 = (fun i j => raw6986step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6986step1 raw6986step0; decide +kernel
      have hl : raw6986step1Labels = raw6986step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6986step0 raw6986step0Labels permutation32 permutation3
    _ = mixedMoment B node991 node991Labels := by rfl

def raw6987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6987Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6987step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6987 raw6987Labels = mixedMoment B node2393 node2393Labels := by
  calc
    mixedMoment B raw6987 raw6987Labels = mixedMoment B raw6987step0 raw6987step0Labels := by
      have hz : ∀ j, raw6987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6987step0 = (fun i j => raw6987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6987step0 raw6987; decide +kernel
      have hl : raw6987step0Labels = raw6987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6987 raw6987Labels permutation346 hz
    mixedMoment B raw6987step0 raw6987step0Labels = mixedMoment B raw6987step1 raw6987step1Labels := by
      have ha : raw6987step1 = (fun i j => raw6987step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6987step1 raw6987step0; decide +kernel
      have hl : raw6987step1Labels = raw6987step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6987step0 raw6987step0Labels permutation32 permutation3
    _ = mixedMoment B node2393 node2393Labels := by rfl

def raw6988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6988Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6988 raw6988Labels = mixedMoment B node2454 node2454Labels := by
  calc
    mixedMoment B raw6988 raw6988Labels = mixedMoment B raw6988step0 raw6988step0Labels := by
      have ha : raw6988step0 = (fun i j => raw6988 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6988step0 raw6988; decide +kernel
      have hl : raw6988step0Labels = raw6988Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6988 raw6988Labels permutation176 permutation3
    _ = mixedMoment B node2454 node2454Labels := by rfl

def raw6989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6989Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw6989step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw6989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6989 raw6989Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw6989 raw6989Labels = mixedMoment B raw6989step0 raw6989step0Labels := by
      have hz : ∀ j, raw6989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6989step0 = (fun i j => raw6989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6989step0 raw6989; decide +kernel
      have hl : raw6989step0Labels = raw6989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6989 raw6989Labels permutation346 hz
    mixedMoment B raw6989step0 raw6989step0Labels = mixedMoment B raw6989step1 raw6989step1Labels := by
      have ha : raw6989step1 = (fun i j => raw6989step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6989step1 raw6989step0; decide +kernel
      have hl : raw6989step1Labels = raw6989step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6989step0 raw6989step0Labels permutation38 permutation3
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw6990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![3, -1, -2]]
def raw6990Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw6990step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6990step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw6990step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6990step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw6990step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6990 raw6990Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw6990 raw6990Labels = mixedMoment B raw6990step0 raw6990step0Labels := by
      have hz : ∀ j, raw6990 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6990step0 = (fun i j => raw6990 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6990step0 raw6990; decide +kernel
      have hl : raw6990step0Labels = raw6990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6990 raw6990Labels permutation520 hz
    mixedMoment B raw6990step0 raw6990step0Labels = mixedMoment B raw6990step1 raw6990step1Labels := by
      have hz : ∀ j, raw6990step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6990step1 = (fun i j => raw6990step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6990step1 raw6990step0; decide +kernel
      have hl : raw6990step1Labels = raw6990step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6990step0 raw6990step0Labels permutation80 hz
    mixedMoment B raw6990step1 raw6990step1Labels = mixedMoment B raw6990step2 raw6990step2Labels := by
      have ha : raw6990step2 = (fun i j => raw6990step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6990step2 raw6990step1; decide +kernel
      have hl : raw6990step2Labels = raw6990step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6990step1 raw6990step1Labels permutation8 permutation3
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw6991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6991step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6991 raw6991Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw6991 raw6991Labels = mixedMoment B raw6991step0 raw6991step0Labels := by
      have hz : ∀ j, raw6991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6991step0 = (fun i j => raw6991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6991step0 raw6991; decide +kernel
      have hl : raw6991step0Labels = raw6991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6991 raw6991Labels permutation346 hz
    mixedMoment B raw6991step0 raw6991step0Labels = mixedMoment B raw6991step1 raw6991step1Labels := by
      have ha : raw6991step1 = (fun i j => raw6991step0 (permutation138 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6991step1 raw6991step0; decide +kernel
      have hl : raw6991step1Labels = raw6991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6991step0 raw6991step0Labels permutation138 permutation7
    mixedMoment B raw6991step1 raw6991step1Labels = mixedMoment B raw6991step2 raw6991step2Labels := by
      have ha : raw6991step2 = raw6991step1 := by apply Matrix.ext; unfold raw6991step2 raw6991step1; decide +kernel
      have hl : raw6991step1Labels = labelEmbedding1 ∘ raw6991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6991step1 raw6991step1Labels raw6991step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw6992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6992step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6992step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6992 raw6992Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw6992 raw6992Labels = mixedMoment B raw6992step0 raw6992step0Labels := by
      have ha : raw6992step0 = (fun i j => raw6992 (permutation619 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6992step0 raw6992; decide +kernel
      have hl : raw6992step0Labels = raw6992Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6992 raw6992Labels permutation619 permutation7
    mixedMoment B raw6992step0 raw6992step0Labels = mixedMoment B raw6992step1 raw6992step1Labels := by
      have ha : raw6992step1 = raw6992step0 := by apply Matrix.ext; unfold raw6992step1 raw6992step0; decide +kernel
      have hl : raw6992step0Labels = labelEmbedding1 ∘ raw6992step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6992step0 raw6992step0Labels raw6992step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw6993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6993step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6993 raw6993Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw6993 raw6993Labels = mixedMoment B raw6993step0 raw6993step0Labels := by
      have hz : ∀ j, raw6993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6993step0 = (fun i j => raw6993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6993step0 raw6993; decide +kernel
      have hl : raw6993step0Labels = raw6993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6993 raw6993Labels permutation346 hz
    mixedMoment B raw6993step0 raw6993step0Labels = mixedMoment B raw6993step1 raw6993step1Labels := by
      have ha : raw6993step1 = (fun i j => raw6993step0 (permutation138 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6993step1 raw6993step0; decide +kernel
      have hl : raw6993step1Labels = raw6993step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6993step0 raw6993step0Labels permutation138 permutation7
    mixedMoment B raw6993step1 raw6993step1Labels = mixedMoment B raw6993step2 raw6993step2Labels := by
      have ha : raw6993step2 = raw6993step1 := by apply Matrix.ext; unfold raw6993step2 raw6993step1; decide +kernel
      have hl : raw6993step1Labels = labelEmbedding1 ∘ raw6993step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6993step1 raw6993step1Labels raw6993step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw6994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw6994step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6994 raw6994Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw6994 raw6994Labels = mixedMoment B raw6994step0 raw6994step0Labels := by
      have hz : ∀ j, raw6994 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6994step0 = (fun i j => raw6994 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6994step0 raw6994; decide +kernel
      have hl : raw6994step0Labels = raw6994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6994 raw6994Labels permutation520 hz
    mixedMoment B raw6994step0 raw6994step0Labels = mixedMoment B raw6994step1 raw6994step1Labels := by
      have hz : ∀ j, raw6994step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6994step1 = (fun i j => raw6994step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6994step1 raw6994step0; decide +kernel
      have hl : raw6994step1Labels = raw6994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6994step0 raw6994step0Labels permutation80 hz
    mixedMoment B raw6994step1 raw6994step1Labels = mixedMoment B raw6994step2 raw6994step2Labels := by
      have ha : raw6994step2 = (fun i j => raw6994step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6994step2 raw6994step1; decide +kernel
      have hl : raw6994step2Labels = raw6994step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6994step1 raw6994step1Labels permutation28 permutation7
    mixedMoment B raw6994step2 raw6994step2Labels = mixedMoment B raw6994step3 raw6994step3Labels := by
      have ha : raw6994step3 = raw6994step2 := by apply Matrix.ext; unfold raw6994step3 raw6994step2; decide +kernel
      have hl : raw6994step2Labels = labelEmbedding1 ∘ raw6994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6994step2 raw6994step2Labels raw6994step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw6995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw6995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6995step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6995 raw6995Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw6995 raw6995Labels = mixedMoment B raw6995step0 raw6995step0Labels := by
      have hz : ∀ j, raw6995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6995step0 = (fun i j => raw6995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6995step0 raw6995; decide +kernel
      have hl : raw6995step0Labels = raw6995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6995 raw6995Labels permutation346 hz
    mixedMoment B raw6995step0 raw6995step0Labels = mixedMoment B raw6995step1 raw6995step1Labels := by
      have ha : raw6995step1 = (fun i j => raw6995step0 (permutation138 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6995step1 raw6995step0; decide +kernel
      have hl : raw6995step1Labels = raw6995step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6995step0 raw6995step0Labels permutation138 permutation7
    mixedMoment B raw6995step1 raw6995step1Labels = mixedMoment B raw6995step2 raw6995step2Labels := by
      have ha : raw6995step2 = raw6995step1 := by apply Matrix.ext; unfold raw6995step2 raw6995step1; decide +kernel
      have hl : raw6995step1Labels = labelEmbedding1 ∘ raw6995step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6995step1 raw6995step1Labels raw6995step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw6996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6996step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6996 raw6996Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw6996 raw6996Labels = mixedMoment B raw6996step0 raw6996step0Labels := by
      have hz : ∀ j, raw6996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6996step0 = (fun i j => raw6996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6996step0 raw6996; decide +kernel
      have hl : raw6996step0Labels = raw6996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6996 raw6996Labels permutation346 hz
    mixedMoment B raw6996step0 raw6996step0Labels = mixedMoment B raw6996step1 raw6996step1Labels := by
      have ha : raw6996step1 = (fun i j => raw6996step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6996step1 raw6996step0; decide +kernel
      have hl : raw6996step1Labels = raw6996step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6996step0 raw6996step0Labels permutation37 permutation5
    mixedMoment B raw6996step1 raw6996step1Labels = mixedMoment B raw6996step2 raw6996step2Labels := by
      have ha : raw6996step2 = -raw6996step1 := by apply Matrix.ext; change ∀ i j, raw6996step2 i j = -(raw6996step1 i j); unfold raw6996step2 raw6996step1; decide +kernel
      have hl : raw6996step2Labels = raw6996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6996step2 raw6996step2Labels = mixedMoment B raw6996step3 raw6996step3Labels := by
      have ha : raw6996step3 = raw6996step2 := by apply Matrix.ext; unfold raw6996step3 raw6996step2; decide +kernel
      have hl : raw6996step2Labels = labelEmbedding1 ∘ raw6996step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6996step2 raw6996step2Labels raw6996step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw6997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6997step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6997step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6997step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6997step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6997 raw6997Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw6997 raw6997Labels = mixedMoment B raw6997step0 raw6997step0Labels := by
      have ha : raw6997step0 = (fun i j => raw6997 (permutation181 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6997step0 raw6997; decide +kernel
      have hl : raw6997step0Labels = raw6997Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6997 raw6997Labels permutation181 permutation5
    mixedMoment B raw6997step0 raw6997step0Labels = mixedMoment B raw6997step1 raw6997step1Labels := by
      have ha : raw6997step1 = -raw6997step0 := by apply Matrix.ext; change ∀ i j, raw6997step1 i j = -(raw6997step0 i j); unfold raw6997step1 raw6997step0; decide +kernel
      have hl : raw6997step1Labels = raw6997step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6997step1 raw6997step1Labels = mixedMoment B raw6997step2 raw6997step2Labels := by
      have ha : raw6997step2 = raw6997step1 := by apply Matrix.ext; unfold raw6997step2 raw6997step1; decide +kernel
      have hl : raw6997step1Labels = labelEmbedding1 ∘ raw6997step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6997step1 raw6997step1Labels raw6997step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw6998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw6998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw6998step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw6998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6998step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw6998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6998 raw6998Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw6998 raw6998Labels = mixedMoment B raw6998step0 raw6998step0Labels := by
      have hz : ∀ j, raw6998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6998step0 = (fun i j => raw6998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6998step0 raw6998; decide +kernel
      have hl : raw6998step0Labels = raw6998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6998 raw6998Labels permutation346 hz
    mixedMoment B raw6998step0 raw6998step0Labels = mixedMoment B raw6998step1 raw6998step1Labels := by
      have ha : raw6998step1 = (fun i j => raw6998step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6998step1 raw6998step0; decide +kernel
      have hl : raw6998step1Labels = raw6998step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6998step0 raw6998step0Labels permutation36 permutation5
    mixedMoment B raw6998step1 raw6998step1Labels = mixedMoment B raw6998step2 raw6998step2Labels := by
      have ha : raw6998step2 = -raw6998step1 := by apply Matrix.ext; change ∀ i j, raw6998step2 i j = -(raw6998step1 i j); unfold raw6998step2 raw6998step1; decide +kernel
      have hl : raw6998step2Labels = raw6998step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6998step2 raw6998step2Labels = mixedMoment B raw6998step3 raw6998step3Labels := by
      have ha : raw6998step3 = raw6998step2 := by apply Matrix.ext; unfold raw6998step3 raw6998step2; decide +kernel
      have hl : raw6998step2Labels = labelEmbedding1 ∘ raw6998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6998step2 raw6998step2Labels raw6998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw6999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw6999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw6999step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw6999step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6999step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6999step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6999step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6999step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6999 raw6999Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw6999 raw6999Labels = mixedMoment B raw6999step0 raw6999step0Labels := by
      have hz : ∀ j, raw6999 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6999step0 = (fun i j => raw6999 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6999step0 raw6999; decide +kernel
      have hl : raw6999step0Labels = raw6999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6999 raw6999Labels permutation520 hz
    mixedMoment B raw6999step0 raw6999step0Labels = mixedMoment B raw6999step1 raw6999step1Labels := by
      have hz : ∀ j, raw6999step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6999step1 = (fun i j => raw6999step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6999step1 raw6999step0; decide +kernel
      have hl : raw6999step1Labels = raw6999step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6999step0 raw6999step0Labels permutation80 hz
    mixedMoment B raw6999step1 raw6999step1Labels = mixedMoment B raw6999step2 raw6999step2Labels := by
      have ha : raw6999step2 = (fun i j => raw6999step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6999step2 raw6999step1; decide +kernel
      have hl : raw6999step2Labels = raw6999step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6999step1 raw6999step1Labels permutation9 permutation5
    mixedMoment B raw6999step2 raw6999step2Labels = mixedMoment B raw6999step3 raw6999step3Labels := by
      have ha : raw6999step3 = -raw6999step2 := by apply Matrix.ext; change ∀ i j, raw6999step3 i j = -(raw6999step2 i j); unfold raw6999step3 raw6999step2; decide +kernel
      have hl : raw6999step3Labels = raw6999step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6999step3 raw6999step3Labels = mixedMoment B raw6999step4 raw6999step4Labels := by
      have ha : raw6999step4 = raw6999step3 := by apply Matrix.ext; unfold raw6999step4 raw6999step3; decide +kernel
      have hl : raw6999step3Labels = labelEmbedding1 ∘ raw6999step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6999step3 raw6999step3Labels raw6999step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw7000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7000step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7000step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7000 raw7000Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw7000 raw7000Labels = mixedMoment B raw7000step0 raw7000step0Labels := by
      have hz : ∀ j, raw7000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7000step0 = (fun i j => raw7000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7000step0 raw7000; decide +kernel
      have hl : raw7000step0Labels = raw7000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7000 raw7000Labels permutation346 hz
    mixedMoment B raw7000step0 raw7000step0Labels = mixedMoment B raw7000step1 raw7000step1Labels := by
      have ha : raw7000step1 = (fun i j => raw7000step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7000step1 raw7000step0; decide +kernel
      have hl : raw7000step1Labels = raw7000step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7000step0 raw7000step0Labels permutation51 permutation5
    mixedMoment B raw7000step1 raw7000step1Labels = mixedMoment B raw7000step2 raw7000step2Labels := by
      have ha : raw7000step2 = -raw7000step1 := by apply Matrix.ext; change ∀ i j, raw7000step2 i j = -(raw7000step1 i j); unfold raw7000step2 raw7000step1; decide +kernel
      have hl : raw7000step2Labels = raw7000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7000step2 raw7000step2Labels = mixedMoment B raw7000step3 raw7000step3Labels := by
      have ha : raw7000step3 = raw7000step2 := by apply Matrix.ext; unfold raw7000step3 raw7000step2; decide +kernel
      have hl : raw7000step2Labels = labelEmbedding1 ∘ raw7000step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7000step2 raw7000step2Labels raw7000step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw7001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7001step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7001step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7001step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7001 raw7001Labels = mixedMoment B node1609 node1609Labels := by
  calc
    mixedMoment B raw7001 raw7001Labels = mixedMoment B raw7001step0 raw7001step0Labels := by
      have ha : raw7001step0 = (fun i j => raw7001 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7001step0 raw7001; decide +kernel
      have hl : raw7001step0Labels = raw7001Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7001 raw7001Labels permutation171 permutation5
    mixedMoment B raw7001step0 raw7001step0Labels = mixedMoment B raw7001step1 raw7001step1Labels := by
      have ha : raw7001step1 = -raw7001step0 := by apply Matrix.ext; change ∀ i j, raw7001step1 i j = -(raw7001step0 i j); unfold raw7001step1 raw7001step0; decide +kernel
      have hl : raw7001step1Labels = raw7001step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7001step1 raw7001step1Labels = mixedMoment B raw7001step2 raw7001step2Labels := by
      have ha : raw7001step2 = raw7001step1 := by apply Matrix.ext; unfold raw7001step2 raw7001step1; decide +kernel
      have hl : raw7001step1Labels = labelEmbedding1 ∘ raw7001step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7001step1 raw7001step1Labels raw7001step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1609 node1609Labels := by rfl

def raw7002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7002Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7002step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7002step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7002step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7002step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7002 raw7002Labels = mixedMoment B node3347 node3347Labels := by
  calc
    mixedMoment B raw7002 raw7002Labels = mixedMoment B raw7002step0 raw7002step0Labels := by
      have ha : raw7002step0 = (fun i j => raw7002 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7002step0 raw7002; decide +kernel
      have hl : raw7002step0Labels = raw7002Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7002 raw7002Labels permutation171 permutation5
    mixedMoment B raw7002step0 raw7002step0Labels = mixedMoment B raw7002step1 raw7002step1Labels := by
      have ha : raw7002step1 = -raw7002step0 := by apply Matrix.ext; change ∀ i j, raw7002step1 i j = -(raw7002step0 i j); unfold raw7002step1 raw7002step0; decide +kernel
      have hl : raw7002step1Labels = raw7002step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7002step1 raw7002step1Labels = mixedMoment B raw7002step2 raw7002step2Labels := by
      have ha : raw7002step2 = raw7002step1 := by apply Matrix.ext; unfold raw7002step2 raw7002step1; decide +kernel
      have hl : raw7002step1Labels = labelEmbedding1 ∘ raw7002step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7002step1 raw7002step1Labels raw7002step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3347 node3347Labels := by rfl

def raw7003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7003Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7003step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw7003step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7003step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7003step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7003step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7003 raw7003Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw7003 raw7003Labels = mixedMoment B raw7003step0 raw7003step0Labels := by
      have ha : raw7003step0 = (fun i j => raw7003 (permutation172 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7003step0 raw7003; decide +kernel
      have hl : raw7003step0Labels = raw7003Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7003 raw7003Labels permutation172 permutation5
    mixedMoment B raw7003step0 raw7003step0Labels = mixedMoment B raw7003step1 raw7003step1Labels := by
      have ha : raw7003step1 = -raw7003step0 := by apply Matrix.ext; change ∀ i j, raw7003step1 i j = -(raw7003step0 i j); unfold raw7003step1 raw7003step0; decide +kernel
      have hl : raw7003step1Labels = raw7003step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7003step1 raw7003step1Labels = mixedMoment B raw7003step2 raw7003step2Labels := by
      have ha : raw7003step2 = raw7003step1 := by apply Matrix.ext; unfold raw7003step2 raw7003step1; decide +kernel
      have hl : raw7003step1Labels = labelEmbedding1 ∘ raw7003step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7003step1 raw7003step1Labels raw7003step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw7004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw7004Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw7004step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw7004step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7004step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7004step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7004step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7004 raw7004Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw7004 raw7004Labels = mixedMoment B raw7004step0 raw7004step0Labels := by
      have hz : ∀ j, raw7004 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7004step0 = (fun i j => raw7004 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7004step0 raw7004; decide +kernel
      have hl : raw7004step0Labels = raw7004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7004 raw7004Labels permutation520 hz
    mixedMoment B raw7004step0 raw7004step0Labels = mixedMoment B raw7004step1 raw7004step1Labels := by
      have ha : raw7004step1 = (fun i j => raw7004step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7004step1 raw7004step0; decide +kernel
      have hl : raw7004step1Labels = raw7004step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7004step0 raw7004step0Labels permutation36 permutation5
    mixedMoment B raw7004step1 raw7004step1Labels = mixedMoment B raw7004step2 raw7004step2Labels := by
      have ha : raw7004step2 = -raw7004step1 := by apply Matrix.ext; change ∀ i j, raw7004step2 i j = -(raw7004step1 i j); unfold raw7004step2 raw7004step1; decide +kernel
      have hl : raw7004step2Labels = raw7004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7004step2 raw7004step2Labels = mixedMoment B raw7004step3 raw7004step3Labels := by
      have ha : raw7004step3 = raw7004step2 := by apply Matrix.ext; unfold raw7004step3 raw7004step2; decide +kernel
      have hl : raw7004step2Labels = labelEmbedding1 ∘ raw7004step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7004step2 raw7004step2Labels raw7004step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw7005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7005Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7005step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7005step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7005step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7005step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7005 raw7005Labels = mixedMoment B node3505 node3505Labels := by
  calc
    mixedMoment B raw7005 raw7005Labels = mixedMoment B raw7005step0 raw7005step0Labels := by
      have ha : raw7005step0 = (fun i j => raw7005 (permutation171 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7005step0 raw7005; decide +kernel
      have hl : raw7005step0Labels = raw7005Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7005 raw7005Labels permutation171 permutation5
    mixedMoment B raw7005step0 raw7005step0Labels = mixedMoment B raw7005step1 raw7005step1Labels := by
      have ha : raw7005step1 = -raw7005step0 := by apply Matrix.ext; change ∀ i j, raw7005step1 i j = -(raw7005step0 i j); unfold raw7005step1 raw7005step0; decide +kernel
      have hl : raw7005step1Labels = raw7005step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7005step1 raw7005step1Labels = mixedMoment B raw7005step2 raw7005step2Labels := by
      have ha : raw7005step2 = raw7005step1 := by apply Matrix.ext; unfold raw7005step2 raw7005step1; decide +kernel
      have hl : raw7005step1Labels = labelEmbedding1 ∘ raw7005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7005step1 raw7005step1Labels raw7005step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3505 node3505Labels := by rfl

def raw7006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7006Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7006step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw7006step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7006step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw7006step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7006step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw7006step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7006 raw7006Labels = mixedMoment B node1610 node1610Labels := by
  calc
    mixedMoment B raw7006 raw7006Labels = mixedMoment B raw7006step0 raw7006step0Labels := by
      have hz : ∀ j, raw7006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7006step0 = (fun i j => raw7006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7006step0 raw7006; decide +kernel
      have hl : raw7006step0Labels = raw7006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7006 raw7006Labels permutation346 hz
    mixedMoment B raw7006step0 raw7006step0Labels = mixedMoment B raw7006step1 raw7006step1Labels := by
      have ha : raw7006step1 = (fun i j => raw7006step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7006step1 raw7006step0; decide +kernel
      have hl : raw7006step1Labels = raw7006step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7006step0 raw7006step0Labels permutation37 permutation5
    mixedMoment B raw7006step1 raw7006step1Labels = mixedMoment B raw7006step2 raw7006step2Labels := by
      have ha : raw7006step2 = -raw7006step1 := by apply Matrix.ext; change ∀ i j, raw7006step2 i j = -(raw7006step1 i j); unfold raw7006step2 raw7006step1; decide +kernel
      have hl : raw7006step2Labels = raw7006step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7006step2 raw7006step2Labels = mixedMoment B raw7006step3 raw7006step3Labels := by
      have ha : raw7006step3 = raw7006step2 := by apply Matrix.ext; unfold raw7006step3 raw7006step2; decide +kernel
      have hl : raw7006step2Labels = labelEmbedding1 ∘ raw7006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7006step2 raw7006step2Labels raw7006step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1610 node1610Labels := by rfl

def raw7007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7007Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7007step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw7007step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw7007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7007 raw7007Labels = mixedMoment B node2910 node2910Labels := by
  calc
    mixedMoment B raw7007 raw7007Labels = mixedMoment B raw7007step0 raw7007step0Labels := by
      have hz : ∀ j, raw7007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7007step0 = (fun i j => raw7007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7007step0 raw7007; decide +kernel
      have hl : raw7007step0Labels = raw7007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7007 raw7007Labels permutation346 hz
    mixedMoment B raw7007step0 raw7007step0Labels = mixedMoment B raw7007step1 raw7007step1Labels := by
      have ha : raw7007step1 = (fun i j => raw7007step0 (permutation97 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7007step1 raw7007step0; decide +kernel
      have hl : raw7007step1Labels = raw7007step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7007step0 raw7007step0Labels permutation97 permutation5
    mixedMoment B raw7007step1 raw7007step1Labels = mixedMoment B raw7007step2 raw7007step2Labels := by
      have ha : raw7007step2 = raw7007step1 := by apply Matrix.ext; unfold raw7007step2 raw7007step1; decide +kernel
      have hl : raw7007step1Labels = labelEmbedding1 ∘ raw7007step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7007step1 raw7007step1Labels raw7007step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2910 node2910Labels := by rfl

def raw7008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7008Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw7008step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw7008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7008 raw7008Labels = mixedMoment B node2906 node2906Labels := by
  calc
    mixedMoment B raw7008 raw7008Labels = mixedMoment B raw7008step0 raw7008step0Labels := by
      have ha : raw7008step0 = (fun i j => raw7008 (permutation502 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7008step0 raw7008; decide +kernel
      have hl : raw7008step0Labels = raw7008Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7008 raw7008Labels permutation502 permutation5
    mixedMoment B raw7008step0 raw7008step0Labels = mixedMoment B raw7008step1 raw7008step1Labels := by
      have ha : raw7008step1 = raw7008step0 := by apply Matrix.ext; unfold raw7008step1 raw7008step0; decide +kernel
      have hl : raw7008step0Labels = labelEmbedding1 ∘ raw7008step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7008step0 raw7008step0Labels raw7008step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2906 node2906Labels := by rfl

def raw7009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![0, 0, 0], ![2, 0, -2]]
def raw7009Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw7009step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw7009step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw7009step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7009step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw7009step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7009 raw7009Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw7009 raw7009Labels = mixedMoment B raw7009step0 raw7009step0Labels := by
      have hz : ∀ j, raw7009 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7009step0 = (fun i j => raw7009 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7009step0 raw7009; decide +kernel
      have hl : raw7009step0Labels = raw7009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7009 raw7009Labels permutation520 hz
    mixedMoment B raw7009step0 raw7009step0Labels = mixedMoment B raw7009step1 raw7009step1Labels := by
      have hz : ∀ j, raw7009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7009step1 = (fun i j => raw7009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7009step1 raw7009step0; decide +kernel
      have hl : raw7009step1Labels = raw7009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7009step0 raw7009step0Labels permutation80 hz
    mixedMoment B raw7009step1 raw7009step1Labels = mixedMoment B raw7009step2 raw7009step2Labels := by
      have ha : raw7009step2 = (fun i j => raw7009step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7009step2 raw7009step1; decide +kernel
      have hl : raw7009step2Labels = raw7009step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7009step1 raw7009step1Labels permutation25 permutation5
    mixedMoment B raw7009step2 raw7009step2Labels = mixedMoment B raw7009step3 raw7009step3Labels := by
      have ha : raw7009step3 = raw7009step2 := by apply Matrix.ext; unfold raw7009step3 raw7009step2; decide +kernel
      have hl : raw7009step2Labels = labelEmbedding1 ∘ raw7009step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7009step2 raw7009step2Labels raw7009step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw7010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7010Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7010step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw7010step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw7010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7010 raw7010Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw7010 raw7010Labels = mixedMoment B raw7010step0 raw7010step0Labels := by
      have hz : ∀ j, raw7010 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7010step0 = (fun i j => raw7010 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7010step0 raw7010; decide +kernel
      have hl : raw7010step0Labels = raw7010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7010 raw7010Labels permutation346 hz
    mixedMoment B raw7010step0 raw7010step0Labels = mixedMoment B raw7010step1 raw7010step1Labels := by
      have ha : raw7010step1 = (fun i j => raw7010step0 (permutation97 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7010step1 raw7010step0; decide +kernel
      have hl : raw7010step1Labels = raw7010step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7010step0 raw7010step0Labels permutation97 permutation5
    mixedMoment B raw7010step1 raw7010step1Labels = mixedMoment B raw7010step2 raw7010step2Labels := by
      have ha : raw7010step2 = raw7010step1 := by apply Matrix.ext; unfold raw7010step2 raw7010step1; decide +kernel
      have hl : raw7010step1Labels = labelEmbedding1 ∘ raw7010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7010step1 raw7010step1Labels raw7010step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw7011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7011Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7011step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw7011step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7011step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7011step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7011step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7011 raw7011Labels = mixedMoment B node1611 node1611Labels := by
  calc
    mixedMoment B raw7011 raw7011Labels = mixedMoment B raw7011step0 raw7011step0Labels := by
      have hz : ∀ j, raw7011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7011step0 = (fun i j => raw7011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7011step0 raw7011; decide +kernel
      have hl : raw7011step0Labels = raw7011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7011 raw7011Labels permutation346 hz
    mixedMoment B raw7011step0 raw7011step0Labels = mixedMoment B raw7011step1 raw7011step1Labels := by
      have ha : raw7011step1 = (fun i j => raw7011step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7011step1 raw7011step0; decide +kernel
      have hl : raw7011step1Labels = raw7011step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7011step0 raw7011step0Labels permutation36 permutation5
    mixedMoment B raw7011step1 raw7011step1Labels = mixedMoment B raw7011step2 raw7011step2Labels := by
      have ha : raw7011step2 = -raw7011step1 := by apply Matrix.ext; change ∀ i j, raw7011step2 i j = -(raw7011step1 i j); unfold raw7011step2 raw7011step1; decide +kernel
      have hl : raw7011step2Labels = raw7011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7011step2 raw7011step2Labels = mixedMoment B raw7011step3 raw7011step3Labels := by
      have ha : raw7011step3 = raw7011step2 := by apply Matrix.ext; unfold raw7011step3 raw7011step2; decide +kernel
      have hl : raw7011step2Labels = labelEmbedding1 ∘ raw7011step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7011step2 raw7011step2Labels raw7011step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1611 node1611Labels := by rfl

def raw7012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7012Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7012step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw7012step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7012step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7012step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7012step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7012 raw7012Labels = mixedMoment B node3348 node3348Labels := by
  calc
    mixedMoment B raw7012 raw7012Labels = mixedMoment B raw7012step0 raw7012step0Labels := by
      have hz : ∀ j, raw7012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7012step0 = (fun i j => raw7012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7012step0 raw7012; decide +kernel
      have hl : raw7012step0Labels = raw7012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7012 raw7012Labels permutation346 hz
    mixedMoment B raw7012step0 raw7012step0Labels = mixedMoment B raw7012step1 raw7012step1Labels := by
      have ha : raw7012step1 = (fun i j => raw7012step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7012step1 raw7012step0; decide +kernel
      have hl : raw7012step1Labels = raw7012step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7012step0 raw7012step0Labels permutation36 permutation5
    mixedMoment B raw7012step1 raw7012step1Labels = mixedMoment B raw7012step2 raw7012step2Labels := by
      have ha : raw7012step2 = -raw7012step1 := by apply Matrix.ext; change ∀ i j, raw7012step2 i j = -(raw7012step1 i j); unfold raw7012step2 raw7012step1; decide +kernel
      have hl : raw7012step2Labels = raw7012step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7012step2 raw7012step2Labels = mixedMoment B raw7012step3 raw7012step3Labels := by
      have ha : raw7012step3 = raw7012step2 := by apply Matrix.ext; unfold raw7012step3 raw7012step2; decide +kernel
      have hl : raw7012step2Labels = labelEmbedding1 ∘ raw7012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7012step2 raw7012step2Labels raw7012step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3348 node3348Labels := by rfl

def raw7013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7013Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw7013step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7013step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7013step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw7013step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7013 raw7013Labels = mixedMoment B node3430 node3430Labels := by
  calc
    mixedMoment B raw7013 raw7013Labels = mixedMoment B raw7013step0 raw7013step0Labels := by
      have ha : raw7013step0 = (fun i j => raw7013 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7013step0 raw7013; decide +kernel
      have hl : raw7013step0Labels = raw7013Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7013 raw7013Labels permutation180 permutation5
    mixedMoment B raw7013step0 raw7013step0Labels = mixedMoment B raw7013step1 raw7013step1Labels := by
      have ha : raw7013step1 = -raw7013step0 := by apply Matrix.ext; change ∀ i j, raw7013step1 i j = -(raw7013step0 i j); unfold raw7013step1 raw7013step0; decide +kernel
      have hl : raw7013step1Labels = raw7013step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7013step1 raw7013step1Labels = mixedMoment B raw7013step2 raw7013step2Labels := by
      have ha : raw7013step2 = raw7013step1 := by apply Matrix.ext; unfold raw7013step2 raw7013step1; decide +kernel
      have hl : raw7013step1Labels = labelEmbedding1 ∘ raw7013step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7013step1 raw7013step1Labels raw7013step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3430 node3430Labels := by rfl

def raw7014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7014Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7014step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw7014step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw7014step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7014step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw7014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7014 raw7014Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw7014 raw7014Labels = mixedMoment B raw7014step0 raw7014step0Labels := by
      have hz : ∀ j, raw7014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7014step0 = (fun i j => raw7014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7014step0 raw7014; decide +kernel
      have hl : raw7014step0Labels = raw7014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7014 raw7014Labels permutation346 hz
    mixedMoment B raw7014step0 raw7014step0Labels = mixedMoment B raw7014step1 raw7014step1Labels := by
      have ha : raw7014step1 = (fun i j => raw7014step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7014step1 raw7014step0; decide +kernel
      have hl : raw7014step1Labels = raw7014step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7014step0 raw7014step0Labels permutation36 permutation5
    mixedMoment B raw7014step1 raw7014step1Labels = mixedMoment B raw7014step2 raw7014step2Labels := by
      have ha : raw7014step2 = -raw7014step1 := by apply Matrix.ext; change ∀ i j, raw7014step2 i j = -(raw7014step1 i j); unfold raw7014step2 raw7014step1; decide +kernel
      have hl : raw7014step2Labels = raw7014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7014step2 raw7014step2Labels = mixedMoment B raw7014step3 raw7014step3Labels := by
      have ha : raw7014step3 = raw7014step2 := by apply Matrix.ext; unfold raw7014step3 raw7014step2; decide +kernel
      have hl : raw7014step2Labels = labelEmbedding1 ∘ raw7014step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7014step2 raw7014step2Labels raw7014step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw7015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw7015Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw7015step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw7015step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7015step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7015step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7015step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7015 raw7015Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw7015 raw7015Labels = mixedMoment B raw7015step0 raw7015step0Labels := by
      have hz : ∀ j, raw7015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7015step0 = (fun i j => raw7015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7015step0 raw7015; decide +kernel
      have hl : raw7015step0Labels = raw7015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7015 raw7015Labels permutation346 hz
    mixedMoment B raw7015step0 raw7015step0Labels = mixedMoment B raw7015step1 raw7015step1Labels := by
      have ha : raw7015step1 = (fun i j => raw7015step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7015step1 raw7015step0; decide +kernel
      have hl : raw7015step1Labels = raw7015step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7015step0 raw7015step0Labels permutation36 permutation5
    mixedMoment B raw7015step1 raw7015step1Labels = mixedMoment B raw7015step2 raw7015step2Labels := by
      have ha : raw7015step2 = -raw7015step1 := by apply Matrix.ext; change ∀ i j, raw7015step2 i j = -(raw7015step1 i j); unfold raw7015step2 raw7015step1; decide +kernel
      have hl : raw7015step2Labels = raw7015step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7015step2 raw7015step2Labels = mixedMoment B raw7015step3 raw7015step3Labels := by
      have ha : raw7015step3 = raw7015step2 := by apply Matrix.ext; unfold raw7015step3 raw7015step2; decide +kernel
      have hl : raw7015step2Labels = labelEmbedding1 ∘ raw7015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7015step2 raw7015step2Labels raw7015step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3506 node3506Labels := by rfl

def raw7016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7016Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7016step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw7016step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7016step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7016step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7016step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7016 raw7016Labels = mixedMoment B node1624 node1624Labels := by
  calc
    mixedMoment B raw7016 raw7016Labels = mixedMoment B raw7016step0 raw7016step0Labels := by
      have hz : ∀ j, raw7016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7016step0 = (fun i j => raw7016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7016step0 raw7016; decide +kernel
      have hl : raw7016step0Labels = raw7016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7016 raw7016Labels permutation346 hz
    mixedMoment B raw7016step0 raw7016step0Labels = mixedMoment B raw7016step1 raw7016step1Labels := by
      have ha : raw7016step1 = (fun i j => raw7016step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7016step1 raw7016step0; decide +kernel
      have hl : raw7016step1Labels = raw7016step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7016step0 raw7016step0Labels permutation35 permutation5
    mixedMoment B raw7016step1 raw7016step1Labels = mixedMoment B raw7016step2 raw7016step2Labels := by
      have ha : raw7016step2 = -raw7016step1 := by apply Matrix.ext; change ∀ i j, raw7016step2 i j = -(raw7016step1 i j); unfold raw7016step2 raw7016step1; decide +kernel
      have hl : raw7016step2Labels = raw7016step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7016step2 raw7016step2Labels = mixedMoment B raw7016step3 raw7016step3Labels := by
      have ha : raw7016step3 = raw7016step2 := by apply Matrix.ext; unfold raw7016step3 raw7016step2; decide +kernel
      have hl : raw7016step2Labels = labelEmbedding1 ∘ raw7016step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7016step2 raw7016step2Labels raw7016step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1624 node1624Labels := by rfl

def raw7017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7017Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7017step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw7017step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7017step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7017step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7017step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7017 raw7017Labels = mixedMoment B node3358 node3358Labels := by
  calc
    mixedMoment B raw7017 raw7017Labels = mixedMoment B raw7017step0 raw7017step0Labels := by
      have hz : ∀ j, raw7017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7017step0 = (fun i j => raw7017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7017step0 raw7017; decide +kernel
      have hl : raw7017step0Labels = raw7017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7017 raw7017Labels permutation346 hz
    mixedMoment B raw7017step0 raw7017step0Labels = mixedMoment B raw7017step1 raw7017step1Labels := by
      have ha : raw7017step1 = (fun i j => raw7017step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7017step1 raw7017step0; decide +kernel
      have hl : raw7017step1Labels = raw7017step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7017step0 raw7017step0Labels permutation35 permutation5
    mixedMoment B raw7017step1 raw7017step1Labels = mixedMoment B raw7017step2 raw7017step2Labels := by
      have ha : raw7017step2 = -raw7017step1 := by apply Matrix.ext; change ∀ i j, raw7017step2 i j = -(raw7017step1 i j); unfold raw7017step2 raw7017step1; decide +kernel
      have hl : raw7017step2Labels = raw7017step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7017step2 raw7017step2Labels = mixedMoment B raw7017step3 raw7017step3Labels := by
      have ha : raw7017step3 = raw7017step2 := by apply Matrix.ext; unfold raw7017step3 raw7017step2; decide +kernel
      have hl : raw7017step2Labels = labelEmbedding1 ∘ raw7017step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7017step2 raw7017step2Labels raw7017step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3358 node3358Labels := by rfl

def raw7018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7018Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw7018step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7018step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7018step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw7018step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7018 raw7018Labels = mixedMoment B node3437 node3437Labels := by
  calc
    mixedMoment B raw7018 raw7018Labels = mixedMoment B raw7018step0 raw7018step0Labels := by
      have ha : raw7018step0 = (fun i j => raw7018 (permutation179 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7018step0 raw7018; decide +kernel
      have hl : raw7018step0Labels = raw7018Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7018 raw7018Labels permutation179 permutation5
    mixedMoment B raw7018step0 raw7018step0Labels = mixedMoment B raw7018step1 raw7018step1Labels := by
      have ha : raw7018step1 = -raw7018step0 := by apply Matrix.ext; change ∀ i j, raw7018step1 i j = -(raw7018step0 i j); unfold raw7018step1 raw7018step0; decide +kernel
      have hl : raw7018step1Labels = raw7018step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7018step1 raw7018step1Labels = mixedMoment B raw7018step2 raw7018step2Labels := by
      have ha : raw7018step2 = raw7018step1 := by apply Matrix.ext; unfold raw7018step2 raw7018step1; decide +kernel
      have hl : raw7018step1Labels = labelEmbedding1 ∘ raw7018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7018step1 raw7018step1Labels raw7018step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3437 node3437Labels := by rfl

def raw7019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7019Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7019step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw7019step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw7019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7019 raw7019Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw7019 raw7019Labels = mixedMoment B raw7019step0 raw7019step0Labels := by
      have hz : ∀ j, raw7019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7019step0 = (fun i j => raw7019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7019step0 raw7019; decide +kernel
      have hl : raw7019step0Labels = raw7019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7019 raw7019Labels permutation346 hz
    mixedMoment B raw7019step0 raw7019step0Labels = mixedMoment B raw7019step1 raw7019step1Labels := by
      have ha : raw7019step1 = (fun i j => raw7019step0 (permutation138 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7019step1 raw7019step0; decide +kernel
      have hl : raw7019step1Labels = raw7019step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7019step0 raw7019step0Labels permutation138 permutation7
    mixedMoment B raw7019step1 raw7019step1Labels = mixedMoment B raw7019step2 raw7019step2Labels := by
      have ha : raw7019step2 = raw7019step1 := by apply Matrix.ext; unfold raw7019step2 raw7019step1; decide +kernel
      have hl : raw7019step1Labels = labelEmbedding1 ∘ raw7019step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7019step1 raw7019step1Labels raw7019step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw7020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![3, -1, -2]]
def raw7020Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw7020step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw7020step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw7020step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw7020step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7020step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw7020step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7020 raw7020Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw7020 raw7020Labels = mixedMoment B raw7020step0 raw7020step0Labels := by
      have hz : ∀ j, raw7020 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7020step0 = (fun i j => raw7020 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7020step0 raw7020; decide +kernel
      have hl : raw7020step0Labels = raw7020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7020 raw7020Labels permutation520 hz
    mixedMoment B raw7020step0 raw7020step0Labels = mixedMoment B raw7020step1 raw7020step1Labels := by
      have hz : ∀ j, raw7020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7020step1 = (fun i j => raw7020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7020step1 raw7020step0; decide +kernel
      have hl : raw7020step1Labels = raw7020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7020step0 raw7020step0Labels permutation80 hz
    mixedMoment B raw7020step1 raw7020step1Labels = mixedMoment B raw7020step2 raw7020step2Labels := by
      have ha : raw7020step2 = (fun i j => raw7020step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7020step2 raw7020step1; decide +kernel
      have hl : raw7020step2Labels = raw7020step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7020step1 raw7020step1Labels permutation9 permutation5
    mixedMoment B raw7020step2 raw7020step2Labels = mixedMoment B raw7020step3 raw7020step3Labels := by
      have ha : raw7020step3 = -raw7020step2 := by apply Matrix.ext; change ∀ i j, raw7020step3 i j = -(raw7020step2 i j); unfold raw7020step3 raw7020step2; decide +kernel
      have hl : raw7020step3Labels = raw7020step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7020step3 raw7020step3Labels = mixedMoment B raw7020step4 raw7020step4Labels := by
      have ha : raw7020step4 = raw7020step3 := by apply Matrix.ext; unfold raw7020step4 raw7020step3; decide +kernel
      have hl : raw7020step3Labels = labelEmbedding1 ∘ raw7020step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7020step3 raw7020step3Labels raw7020step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw7021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7021 raw7021Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw7021 raw7021Labels = mixedMoment B raw7021step0 raw7021step0Labels := by
      have hz : ∀ j, raw7021 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7021step0 = (fun i j => raw7021 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7021step0 raw7021; decide +kernel
      have hl : raw7021step0Labels = raw7021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7021 raw7021Labels permutation346 hz
    mixedMoment B raw7021step0 raw7021step0Labels = mixedMoment B raw7021step1 raw7021step1Labels := by
      have ha : raw7021step1 = (fun i j => raw7021step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7021step1 raw7021step0; decide +kernel
      have hl : raw7021step1Labels = raw7021step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7021step0 raw7021step0Labels permutation38 permutation2
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw7022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw7022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw7022step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7022 raw7022Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw7022 raw7022Labels = mixedMoment B raw7022step0 raw7022step0Labels := by
      have hz : ∀ j, raw7022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7022step0 = (fun i j => raw7022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7022step0 raw7022; decide +kernel
      have hl : raw7022step0Labels = raw7022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7022 raw7022Labels permutation346 hz
    mixedMoment B raw7022step0 raw7022step0Labels = mixedMoment B raw7022step1 raw7022step1Labels := by
      have ha : raw7022step1 = (fun i j => raw7022step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7022step1 raw7022step0; decide +kernel
      have hl : raw7022step1Labels = raw7022step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7022step0 raw7022step0Labels permutation151 permutation2
    mixedMoment B raw7022step1 raw7022step1Labels = mixedMoment B raw7022step2 raw7022step2Labels := by
      have ha : raw7022step2 = -raw7022step1 := by apply Matrix.ext; change ∀ i j, raw7022step2 i j = -(raw7022step1 i j); unfold raw7022step2 raw7022step1; decide +kernel
      have hl : raw7022step2Labels = raw7022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw7023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw7023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7023 raw7023Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw7023 raw7023Labels = mixedMoment B raw7023step0 raw7023step0Labels := by
      have ha : raw7023step0 = (fun i j => raw7023 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7023step0 raw7023; decide +kernel
      have hl : raw7023step0Labels = raw7023Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7023 raw7023Labels permutation676 permutation2
    mixedMoment B raw7023step0 raw7023step0Labels = mixedMoment B raw7023step1 raw7023step1Labels := by
      have ha : raw7023step1 = -raw7023step0 := by apply Matrix.ext; change ∀ i j, raw7023step1 i j = -(raw7023step0 i j); unfold raw7023step1 raw7023step0; decide +kernel
      have hl : raw7023step1Labels = raw7023step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw7024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw7024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7024step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7024 raw7024Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw7024 raw7024Labels = mixedMoment B raw7024step0 raw7024step0Labels := by
      have hz : ∀ j, raw7024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7024step0 = (fun i j => raw7024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7024step0 raw7024; decide +kernel
      have hl : raw7024step0Labels = raw7024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7024 raw7024Labels permutation346 hz
    mixedMoment B raw7024step0 raw7024step0Labels = mixedMoment B raw7024step1 raw7024step1Labels := by
      have ha : raw7024step1 = (fun i j => raw7024step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7024step1 raw7024step0; decide +kernel
      have hl : raw7024step1Labels = raw7024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7024step0 raw7024step0Labels permutation149 permutation2
    mixedMoment B raw7024step1 raw7024step1Labels = mixedMoment B raw7024step2 raw7024step2Labels := by
      have ha : raw7024step2 = -raw7024step1 := by apply Matrix.ext; change ∀ i j, raw7024step2 i j = -(raw7024step1 i j); unfold raw7024step2 raw7024step1; decide +kernel
      have hl : raw7024step2Labels = raw7024step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw7025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw7025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw7025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw7025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7025step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw7025step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7025step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw7025step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7025 raw7025Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw7025 raw7025Labels = mixedMoment B raw7025step0 raw7025step0Labels := by
      have hz : ∀ j, raw7025 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7025step0 = (fun i j => raw7025 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7025step0 raw7025; decide +kernel
      have hl : raw7025step0Labels = raw7025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7025 raw7025Labels permutation520 hz
    mixedMoment B raw7025step0 raw7025step0Labels = mixedMoment B raw7025step1 raw7025step1Labels := by
      have hz : ∀ j, raw7025step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7025step1 = (fun i j => raw7025step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7025step1 raw7025step0; decide +kernel
      have hl : raw7025step1Labels = raw7025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7025step0 raw7025step0Labels permutation80 hz
    mixedMoment B raw7025step1 raw7025step1Labels = mixedMoment B raw7025step2 raw7025step2Labels := by
      have ha : raw7025step2 = (fun i j => raw7025step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7025step2 raw7025step1; decide +kernel
      have hl : raw7025step2Labels = raw7025step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7025step1 raw7025step1Labels permutation29 permutation2
    mixedMoment B raw7025step2 raw7025step2Labels = mixedMoment B raw7025step3 raw7025step3Labels := by
      have ha : raw7025step3 = -raw7025step2 := by apply Matrix.ext; change ∀ i j, raw7025step3 i j = -(raw7025step2 i j); unfold raw7025step3 raw7025step2; decide +kernel
      have hl : raw7025step3Labels = raw7025step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw7026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7026 raw7026Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw7026 raw7026Labels = mixedMoment B raw7026step0 raw7026step0Labels := by
      have hz : ∀ j, raw7026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7026step0 = (fun i j => raw7026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7026step0 raw7026; decide +kernel
      have hl : raw7026step0Labels = raw7026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7026 raw7026Labels permutation346 hz
    mixedMoment B raw7026step0 raw7026step0Labels = mixedMoment B raw7026step1 raw7026step1Labels := by
      have ha : raw7026step1 = (fun i j => raw7026step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7026step1 raw7026step0; decide +kernel
      have hl : raw7026step1Labels = raw7026step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7026step0 raw7026step0Labels permutation92 permutation4
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw7027 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-2, 2], ![0, 0], ![2, -2]]
def raw7027Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7027step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-2, 2], ![2, -2]]
def raw7027step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7027step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]
def raw7027step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7027step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw7027step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical7027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7027 raw7027Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw7027 raw7027Labels = mixedMoment B raw7027step0 raw7027step0Labels := by
      have hz : ∀ j, raw7027 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7027step0 = (fun i j => raw7027 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7027step0 raw7027; decide +kernel
      have hl : raw7027step0Labels = raw7027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7027 raw7027Labels permutation520 hz
    mixedMoment B raw7027step0 raw7027step0Labels = mixedMoment B raw7027step1 raw7027step1Labels := by
      have hz : ∀ j, raw7027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7027step1 = (fun i j => raw7027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7027step1 raw7027step0; decide +kernel
      have hl : raw7027step1Labels = raw7027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7027step0 raw7027step0Labels permutation80 hz
    mixedMoment B raw7027step1 raw7027step1Labels = mixedMoment B raw7027step2 raw7027step2Labels := by
      have ha : raw7027step2 = (fun i j => raw7027step1 (permutation20 i) (permutation0 j)) := by apply Matrix.ext; unfold raw7027step2 raw7027step1; decide +kernel
      have hl : raw7027step2Labels = raw7027step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7027step1 raw7027step1Labels permutation20 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw7028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7028 raw7028Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw7028 raw7028Labels = mixedMoment B raw7028step0 raw7028step0Labels := by
      have hz : ∀ j, raw7028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7028step0 = (fun i j => raw7028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7028step0 raw7028; decide +kernel
      have hl : raw7028step0Labels = raw7028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7028 raw7028Labels permutation346 hz
    mixedMoment B raw7028step0 raw7028step0Labels = mixedMoment B raw7028step1 raw7028step1Labels := by
      have ha : raw7028step1 = (fun i j => raw7028step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7028step1 raw7028step0; decide +kernel
      have hl : raw7028step1Labels = raw7028step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7028step0 raw7028step0Labels permutation40 permutation2
    _ = mixedMoment B node1367 node1367Labels := by rfl

def raw7029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7029 raw7029Labels = mixedMoment B node1357 node1357Labels := by
  calc
    mixedMoment B raw7029 raw7029Labels = mixedMoment B raw7029step0 raw7029step0Labels := by
      have ha : raw7029step0 = (fun i j => raw7029 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7029step0 raw7029; decide +kernel
      have hl : raw7029step0Labels = raw7029Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7029 raw7029Labels permutation200 permutation2
    _ = mixedMoment B node1357 node1357Labels := by rfl

def raw7030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7030 raw7030Labels = mixedMoment B node1422 node1422Labels := by
  calc
    mixedMoment B raw7030 raw7030Labels = mixedMoment B raw7030step0 raw7030step0Labels := by
      have hz : ∀ j, raw7030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7030step0 = (fun i j => raw7030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7030step0 raw7030; decide +kernel
      have hl : raw7030step0Labels = raw7030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7030 raw7030Labels permutation346 hz
    _ = mixedMoment B node1422 node1422Labels := by rfl

def raw7031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7031 raw7031Labels = mixedMoment B node1362 node1362Labels := by
  calc
    mixedMoment B raw7031 raw7031Labels = mixedMoment B raw7031step0 raw7031step0Labels := by
      have hz : ∀ j, raw7031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7031step0 = (fun i j => raw7031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7031step0 raw7031; decide +kernel
      have hl : raw7031step0Labels = raw7031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7031 raw7031Labels permutation346 hz
    mixedMoment B raw7031step0 raw7031step0Labels = mixedMoment B raw7031step1 raw7031step1Labels := by
      have ha : raw7031step1 = (fun i j => raw7031step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7031step1 raw7031step0; decide +kernel
      have hl : raw7031step1Labels = raw7031step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7031step0 raw7031step0Labels permutation38 permutation2
    _ = mixedMoment B node1362 node1362Labels := by rfl

def raw7032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw7032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7032 raw7032Labels = mixedMoment B node1359 node1359Labels := by
  calc
    mixedMoment B raw7032 raw7032Labels = mixedMoment B raw7032step0 raw7032step0Labels := by
      have hz : ∀ j, raw7032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7032step0 = (fun i j => raw7032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7032step0 raw7032; decide +kernel
      have hl : raw7032step0Labels = raw7032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7032 raw7032Labels permutation346 hz
    mixedMoment B raw7032step0 raw7032step0Labels = mixedMoment B raw7032step1 raw7032step1Labels := by
      have ha : raw7032step1 = (fun i j => raw7032step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7032step1 raw7032step0; decide +kernel
      have hl : raw7032step1Labels = raw7032step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7032step0 raw7032step0Labels permutation38 permutation2
    _ = mixedMoment B node1359 node1359Labels := by rfl

def raw7033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7033 raw7033Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw7033 raw7033Labels = mixedMoment B raw7033step0 raw7033step0Labels := by
      have ha : raw7033step0 = (fun i j => raw7033 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7033step0 raw7033; decide +kernel
      have hl : raw7033step0Labels = raw7033Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7033 raw7033Labels permutation184 permutation2
    _ = mixedMoment B node2974 node2974Labels := by rfl

def raw7034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7034 raw7034Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw7034 raw7034Labels = mixedMoment B raw7034step0 raw7034step0Labels := by
      have hz : ∀ j, raw7034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7034step0 = (fun i j => raw7034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7034step0 raw7034; decide +kernel
      have hl : raw7034step0Labels = raw7034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7034 raw7034Labels permutation346 hz
    mixedMoment B raw7034step0 raw7034step0Labels = mixedMoment B raw7034step1 raw7034step1Labels := by
      have ha : raw7034step1 = (fun i j => raw7034step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7034step1 raw7034step0; decide +kernel
      have hl : raw7034step1Labels = raw7034step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7034step0 raw7034step0Labels permutation40 permutation2
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw7035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw7035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw7035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7035step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw7035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7035step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw7035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7035 raw7035Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw7035 raw7035Labels = mixedMoment B raw7035step0 raw7035step0Labels := by
      have hz : ∀ j, raw7035 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7035step0 = (fun i j => raw7035 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7035step0 raw7035; decide +kernel
      have hl : raw7035step0Labels = raw7035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7035 raw7035Labels permutation520 hz
    mixedMoment B raw7035step0 raw7035step0Labels = mixedMoment B raw7035step1 raw7035step1Labels := by
      have hz : ∀ j, raw7035step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw7035step1 = (fun i j => raw7035step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw7035step1 raw7035step0; decide +kernel
      have hl : raw7035step1Labels = raw7035step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7035step0 raw7035step0Labels permutation80 hz
    mixedMoment B raw7035step1 raw7035step1Labels = mixedMoment B raw7035step2 raw7035step2Labels := by
      have ha : raw7035step2 = (fun i j => raw7035step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7035step2 raw7035step1; decide +kernel
      have hl : raw7035step2Labels = raw7035step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7035step1 raw7035step1Labels permutation10 permutation2
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw7036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7036 raw7036Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw7036 raw7036Labels = mixedMoment B raw7036step0 raw7036step0Labels := by
      have hz : ∀ j, raw7036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7036step0 = (fun i j => raw7036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7036step0 raw7036; decide +kernel
      have hl : raw7036step0Labels = raw7036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7036 raw7036Labels permutation346 hz
    mixedMoment B raw7036step0 raw7036step0Labels = mixedMoment B raw7036step1 raw7036step1Labels := by
      have ha : raw7036step1 = (fun i j => raw7036step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7036step1 raw7036step0; decide +kernel
      have hl : raw7036step1Labels = raw7036step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7036step0 raw7036step0Labels permutation40 permutation2
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw7037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7037 raw7037Labels = mixedMoment B node3007 node3007Labels := by
  calc
    mixedMoment B raw7037 raw7037Labels = mixedMoment B raw7037step0 raw7037step0Labels := by
      have ha : raw7037step0 = (fun i j => raw7037 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7037step0 raw7037; decide +kernel
      have hl : raw7037step0Labels = raw7037Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7037 raw7037Labels permutation158 permutation2
    _ = mixedMoment B node3007 node3007Labels := by rfl

def raw7038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw7038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7038 raw7038Labels = mixedMoment B node2582 node2582Labels := by
  calc
    mixedMoment B raw7038 raw7038Labels = mixedMoment B raw7038step0 raw7038step0Labels := by
      have hz : ∀ j, raw7038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7038step0 = (fun i j => raw7038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7038step0 raw7038; decide +kernel
      have hl : raw7038step0Labels = raw7038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7038 raw7038Labels permutation346 hz
    mixedMoment B raw7038step0 raw7038step0Labels = mixedMoment B raw7038step1 raw7038step1Labels := by
      have ha : raw7038step1 = (fun i j => raw7038step0 (permutation96 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7038step1 raw7038step0; decide +kernel
      have hl : raw7038step1Labels = raw7038step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7038step0 raw7038step0Labels permutation96 permutation4
    _ = mixedMoment B node2582 node2582Labels := by rfl

def raw7039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7039Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7039step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7039 raw7039Labels = mixedMoment B node3010 node3010Labels := by
  calc
    mixedMoment B raw7039 raw7039Labels = mixedMoment B raw7039step0 raw7039step0Labels := by
      have hz : ∀ j, raw7039 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7039step0 = (fun i j => raw7039 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7039step0 raw7039; decide +kernel
      have hl : raw7039step0Labels = raw7039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7039 raw7039Labels permutation346 hz
    _ = mixedMoment B node3010 node3010Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
