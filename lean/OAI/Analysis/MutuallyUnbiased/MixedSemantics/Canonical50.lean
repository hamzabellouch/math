import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6400 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6400 raw6400Labels = mixedMoment B node2663 node2663Labels := by
  calc
    mixedMoment B raw6400 raw6400Labels = mixedMoment B raw6400step0 raw6400step0Labels := by
      have ha : raw6400step0 = (fun i j => raw6400 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6400step0 raw6400; decide +kernel
      have hl : raw6400step0Labels = raw6400Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6400 raw6400Labels permutation152 permutation6
    _ = mixedMoment B node2663 node2663Labels := by rfl

def raw6401 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6401 raw6401Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw6401 raw6401Labels = mixedMoment B raw6401step0 raw6401step0Labels := by
      have ha : raw6401step0 = (fun i j => raw6401 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6401step0 raw6401; decide +kernel
      have hl : raw6401step0Labels = raw6401Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6401 raw6401Labels permutation152 permutation6
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw6402 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6402 raw6402Labels = mixedMoment B node2711 node2711Labels := by
  calc
    mixedMoment B raw6402 raw6402Labels = mixedMoment B raw6402step0 raw6402step0Labels := by
      have ha : raw6402step0 = (fun i j => raw6402 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6402step0 raw6402; decide +kernel
      have hl : raw6402step0Labels = raw6402Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6402 raw6402Labels permutation152 permutation6
    _ = mixedMoment B node2711 node2711Labels := by rfl

def raw6403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6403 raw6403Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw6403 raw6403Labels = mixedMoment B raw6403step0 raw6403step0Labels := by
      have hz : ∀ j, raw6403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6403step0 = (fun i j => raw6403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6403step0 raw6403; decide +kernel
      have hl : raw6403step0Labels = raw6403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6403 raw6403Labels permutation346 hz
    mixedMoment B raw6403step0 raw6403step0Labels = mixedMoment B raw6403step1 raw6403step1Labels := by
      have ha : raw6403step1 = (fun i j => raw6403step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6403step1 raw6403step0; decide +kernel
      have hl : raw6403step1Labels = raw6403step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6403step0 raw6403step0Labels permutation32 permutation6
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw6404 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6404 raw6404Labels = mixedMoment B node2679 node2679Labels := by
  calc
    mixedMoment B raw6404 raw6404Labels = mixedMoment B raw6404step0 raw6404step0Labels := by
      have hz : ∀ j, raw6404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6404step0 = (fun i j => raw6404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6404step0 raw6404; decide +kernel
      have hl : raw6404step0Labels = raw6404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6404 raw6404Labels permutation346 hz
    mixedMoment B raw6404step0 raw6404step0Labels = mixedMoment B raw6404step1 raw6404step1Labels := by
      have ha : raw6404step1 = (fun i j => raw6404step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6404step1 raw6404step0; decide +kernel
      have hl : raw6404step1Labels = raw6404step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6404step0 raw6404step0Labels permutation32 permutation6
    _ = mixedMoment B node2679 node2679Labels := by rfl

def raw6405 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6405 raw6405Labels = mixedMoment B node2699 node2699Labels := by
  calc
    mixedMoment B raw6405 raw6405Labels = mixedMoment B raw6405step0 raw6405step0Labels := by
      have ha : raw6405step0 = (fun i j => raw6405 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6405step0 raw6405; decide +kernel
      have hl : raw6405step0Labels = raw6405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6405 raw6405Labels permutation152 permutation6
    _ = mixedMoment B node2699 node2699Labels := by rfl

def raw6406 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6406 raw6406Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw6406 raw6406Labels = mixedMoment B raw6406step0 raw6406step0Labels := by
      have hz : ∀ j, raw6406 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6406step0 = (fun i j => raw6406 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6406step0 raw6406; decide +kernel
      have hl : raw6406step0Labels = raw6406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6406 raw6406Labels permutation346 hz
    mixedMoment B raw6406step0 raw6406step0Labels = mixedMoment B raw6406step1 raw6406step1Labels := by
      have ha : raw6406step1 = (fun i j => raw6406step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6406step1 raw6406step0; decide +kernel
      have hl : raw6406step1Labels = raw6406step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6406step0 raw6406step0Labels permutation32 permutation6
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw6407 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw6407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6407 raw6407Labels = mixedMoment B node2733 node2733Labels := by
  calc
    mixedMoment B raw6407 raw6407Labels = mixedMoment B raw6407step0 raw6407step0Labels := by
      have hz : ∀ j, raw6407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6407step0 = (fun i j => raw6407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6407step0 raw6407; decide +kernel
      have hl : raw6407step0Labels = raw6407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6407 raw6407Labels permutation346 hz
    mixedMoment B raw6407step0 raw6407step0Labels = mixedMoment B raw6407step1 raw6407step1Labels := by
      have ha : raw6407step1 = (fun i j => raw6407step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6407step1 raw6407step0; decide +kernel
      have hl : raw6407step1Labels = raw6407step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6407step0 raw6407step0Labels permutation32 permutation6
    _ = mixedMoment B node2733 node2733Labels := by rfl

def raw6408 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6408step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6408 raw6408Labels = mixedMoment B node2744 node2744Labels := by
  calc
    mixedMoment B raw6408 raw6408Labels = mixedMoment B raw6408step0 raw6408step0Labels := by
      have hz : ∀ j, raw6408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6408step0 = (fun i j => raw6408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6408step0 raw6408; decide +kernel
      have hl : raw6408step0Labels = raw6408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6408 raw6408Labels permutation434 hz
    mixedMoment B raw6408step0 raw6408step0Labels = mixedMoment B raw6408step1 raw6408step1Labels := by
      have hz : ∀ j, raw6408step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6408step1 = (fun i j => raw6408step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6408step1 raw6408step0; decide +kernel
      have hl : raw6408step1Labels = raw6408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6408step0 raw6408step0Labels permutation80 hz
    mixedMoment B raw6408step1 raw6408step1Labels = mixedMoment B raw6408step2 raw6408step2Labels := by
      have ha : raw6408step2 = (fun i j => raw6408step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6408step2 raw6408step1; decide +kernel
      have hl : raw6408step2Labels = raw6408step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6408step1 raw6408step1Labels permutation8 permutation6
    _ = mixedMoment B node2744 node2744Labels := by rfl

def raw6409 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6409 raw6409Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw6409 raw6409Labels = mixedMoment B raw6409step0 raw6409step0Labels := by
      have hz : ∀ j, raw6409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6409step0 = (fun i j => raw6409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6409step0 raw6409; decide +kernel
      have hl : raw6409step0Labels = raw6409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6409 raw6409Labels permutation346 hz
    mixedMoment B raw6409step0 raw6409step0Labels = mixedMoment B raw6409step1 raw6409step1Labels := by
      have ha : raw6409step1 = (fun i j => raw6409step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6409step1 raw6409step0; decide +kernel
      have hl : raw6409step1Labels = raw6409step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6409step0 raw6409step0Labels permutation32 permutation6
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw6410 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6410 raw6410Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw6410 raw6410Labels = mixedMoment B raw6410step0 raw6410step0Labels := by
      have hz : ∀ j, raw6410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6410step0 = (fun i j => raw6410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6410step0 raw6410; decide +kernel
      have hl : raw6410step0Labels = raw6410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6410 raw6410Labels permutation346 hz
    mixedMoment B raw6410step0 raw6410step0Labels = mixedMoment B raw6410step1 raw6410step1Labels := by
      have ha : raw6410step1 = (fun i j => raw6410step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6410step1 raw6410step0; decide +kernel
      have hl : raw6410step1Labels = raw6410step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6410step0 raw6410step0Labels permutation32 permutation6
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw6411 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6411 raw6411Labels = mixedMoment B node2695 node2695Labels := by
  calc
    mixedMoment B raw6411 raw6411Labels = mixedMoment B raw6411step0 raw6411step0Labels := by
      have ha : raw6411step0 = (fun i j => raw6411 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6411step0 raw6411; decide +kernel
      have hl : raw6411step0Labels = raw6411Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6411 raw6411Labels permutation152 permutation6
    _ = mixedMoment B node2695 node2695Labels := by rfl

def raw6412 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6412step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6412 raw6412Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw6412 raw6412Labels = mixedMoment B raw6412step0 raw6412step0Labels := by
      have hz : ∀ j, raw6412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6412step0 = (fun i j => raw6412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6412step0 raw6412; decide +kernel
      have hl : raw6412step0Labels = raw6412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6412 raw6412Labels permutation346 hz
    mixedMoment B raw6412step0 raw6412step0Labels = mixedMoment B raw6412step1 raw6412step1Labels := by
      have ha : raw6412step1 = (fun i j => raw6412step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6412step1 raw6412step0; decide +kernel
      have hl : raw6412step1Labels = raw6412step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6412step0 raw6412step0Labels permutation32 permutation6
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw6413 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6413step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6413 raw6413Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw6413 raw6413Labels = mixedMoment B raw6413step0 raw6413step0Labels := by
      have hz : ∀ j, raw6413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6413step0 = (fun i j => raw6413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6413step0 raw6413; decide +kernel
      have hl : raw6413step0Labels = raw6413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6413 raw6413Labels permutation346 hz
    mixedMoment B raw6413step0 raw6413step0Labels = mixedMoment B raw6413step1 raw6413step1Labels := by
      have ha : raw6413step1 = (fun i j => raw6413step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6413step1 raw6413step0; decide +kernel
      have hl : raw6413step1Labels = raw6413step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6413step0 raw6413step0Labels permutation38 permutation7
    mixedMoment B raw6413step1 raw6413step1Labels = mixedMoment B raw6413step2 raw6413step2Labels := by
      have ha : raw6413step2 = raw6413step1 := by apply Matrix.ext; unfold raw6413step2 raw6413step1; decide +kernel
      have hl : raw6413step1Labels = labelEmbedding1 ∘ raw6413step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6413step1 raw6413step1Labels raw6413step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw6414 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6414 raw6414Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw6414 raw6414Labels = mixedMoment B raw6414step0 raw6414step0Labels := by
      have ha : raw6414step0 = (fun i j => raw6414 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6414step0 raw6414; decide +kernel
      have hl : raw6414step0Labels = raw6414Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6414 raw6414Labels permutation200 permutation7
    mixedMoment B raw6414step0 raw6414step0Labels = mixedMoment B raw6414step1 raw6414step1Labels := by
      have ha : raw6414step1 = raw6414step0 := by apply Matrix.ext; unfold raw6414step1 raw6414step0; decide +kernel
      have hl : raw6414step0Labels = labelEmbedding1 ∘ raw6414step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6414step0 raw6414step0Labels raw6414step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw6415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6415step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6415 raw6415Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw6415 raw6415Labels = mixedMoment B raw6415step0 raw6415step0Labels := by
      have hz : ∀ j, raw6415 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6415step0 = (fun i j => raw6415 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6415step0 raw6415; decide +kernel
      have hl : raw6415step0Labels = raw6415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6415 raw6415Labels permutation346 hz
    mixedMoment B raw6415step0 raw6415step0Labels = mixedMoment B raw6415step1 raw6415step1Labels := by
      have ha : raw6415step1 = (fun i j => raw6415step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6415step1 raw6415step0; decide +kernel
      have hl : raw6415step1Labels = raw6415step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6415step0 raw6415step0Labels permutation38 permutation7
    mixedMoment B raw6415step1 raw6415step1Labels = mixedMoment B raw6415step2 raw6415step2Labels := by
      have ha : raw6415step2 = raw6415step1 := by apply Matrix.ext; unfold raw6415step2 raw6415step1; decide +kernel
      have hl : raw6415step1Labels = labelEmbedding1 ∘ raw6415step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6415step1 raw6415step1Labels raw6415step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw6416 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6416step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6416step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6416 raw6416Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw6416 raw6416Labels = mixedMoment B raw6416step0 raw6416step0Labels := by
      have hz : ∀ j, raw6416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6416step0 = (fun i j => raw6416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6416step0 raw6416; decide +kernel
      have hl : raw6416step0Labels = raw6416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6416 raw6416Labels permutation346 hz
    mixedMoment B raw6416step0 raw6416step0Labels = mixedMoment B raw6416step1 raw6416step1Labels := by
      have ha : raw6416step1 = (fun i j => raw6416step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6416step1 raw6416step0; decide +kernel
      have hl : raw6416step1Labels = raw6416step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6416step0 raw6416step0Labels permutation38 permutation7
    mixedMoment B raw6416step1 raw6416step1Labels = mixedMoment B raw6416step2 raw6416step2Labels := by
      have ha : raw6416step2 = raw6416step1 := by apply Matrix.ext; unfold raw6416step2 raw6416step1; decide +kernel
      have hl : raw6416step1Labels = labelEmbedding1 ∘ raw6416step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6416step1 raw6416step1Labels raw6416step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw6417 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6417step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6417step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6417step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6417step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6417step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6417step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6417 raw6417Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw6417 raw6417Labels = mixedMoment B raw6417step0 raw6417step0Labels := by
      have hz : ∀ j, raw6417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6417step0 = (fun i j => raw6417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6417step0 raw6417; decide +kernel
      have hl : raw6417step0Labels = raw6417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6417 raw6417Labels permutation346 hz
    mixedMoment B raw6417step0 raw6417step0Labels = mixedMoment B raw6417step1 raw6417step1Labels := by
      have hz : ∀ j, raw6417step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6417step1 = (fun i j => raw6417step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6417step1 raw6417step0; decide +kernel
      have hl : raw6417step1Labels = raw6417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6417step0 raw6417step0Labels permutation56 hz
    mixedMoment B raw6417step1 raw6417step1Labels = mixedMoment B raw6417step2 raw6417step2Labels := by
      have ha : raw6417step2 = (fun i j => raw6417step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6417step2 raw6417step1; decide +kernel
      have hl : raw6417step2Labels = raw6417step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6417step1 raw6417step1Labels permutation12 permutation5
    mixedMoment B raw6417step2 raw6417step2Labels = mixedMoment B raw6417step3 raw6417step3Labels := by
      have ha : raw6417step3 = -raw6417step2 := by apply Matrix.ext; change ∀ i j, raw6417step3 i j = -(raw6417step2 i j); unfold raw6417step3 raw6417step2; decide +kernel
      have hl : raw6417step3Labels = raw6417step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6417step3 raw6417step3Labels = mixedMoment B raw6417step4 raw6417step4Labels := by
      have ha : raw6417step4 = raw6417step3 := by apply Matrix.ext; unfold raw6417step4 raw6417step3; decide +kernel
      have hl : raw6417step3Labels = labelEmbedding1 ∘ raw6417step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6417step3 raw6417step3Labels raw6417step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw6418 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6418step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6418step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6418 raw6418Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw6418 raw6418Labels = mixedMoment B raw6418step0 raw6418step0Labels := by
      have hz : ∀ j, raw6418 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw6418step0 = (fun i j => raw6418 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw6418step0 raw6418; decide +kernel
      have hl : raw6418step0Labels = raw6418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6418 raw6418Labels permutation265 hz
    mixedMoment B raw6418step0 raw6418step0Labels = mixedMoment B raw6418step1 raw6418step1Labels := by
      have ha : raw6418step1 = (fun i j => raw6418step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6418step1 raw6418step0; decide +kernel
      have hl : raw6418step1Labels = raw6418step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6418step0 raw6418step0Labels permutation38 permutation7
    mixedMoment B raw6418step1 raw6418step1Labels = mixedMoment B raw6418step2 raw6418step2Labels := by
      have ha : raw6418step2 = raw6418step1 := by apply Matrix.ext; unfold raw6418step2 raw6418step1; decide +kernel
      have hl : raw6418step1Labels = labelEmbedding1 ∘ raw6418step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6418step1 raw6418step1Labels raw6418step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw6419 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6419Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6419step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6419step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6419step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6419step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6419step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6419 raw6419Labels = mixedMoment B node3101 node3101Labels := by
  calc
    mixedMoment B raw6419 raw6419Labels = mixedMoment B raw6419step0 raw6419step0Labels := by
      have hz : ∀ j, raw6419 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6419step0 = (fun i j => raw6419 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6419step0 raw6419; decide +kernel
      have hl : raw6419step0Labels = raw6419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6419 raw6419Labels permutation346 hz
    mixedMoment B raw6419step0 raw6419step0Labels = mixedMoment B raw6419step1 raw6419step1Labels := by
      have hz : ∀ j, raw6419step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6419step1 = (fun i j => raw6419step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6419step1 raw6419step0; decide +kernel
      have hl : raw6419step1Labels = raw6419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6419step0 raw6419step0Labels permutation56 hz
    mixedMoment B raw6419step1 raw6419step1Labels = mixedMoment B raw6419step2 raw6419step2Labels := by
      have ha : raw6419step2 = (fun i j => raw6419step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6419step2 raw6419step1; decide +kernel
      have hl : raw6419step2Labels = raw6419step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6419step1 raw6419step1Labels permutation8 permutation7
    mixedMoment B raw6419step2 raw6419step2Labels = mixedMoment B raw6419step3 raw6419step3Labels := by
      have ha : raw6419step3 = raw6419step2 := by apply Matrix.ext; unfold raw6419step3 raw6419step2; decide +kernel
      have hl : raw6419step2Labels = labelEmbedding1 ∘ raw6419step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6419step2 raw6419step2Labels raw6419step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3101 node3101Labels := by rfl

def raw6420 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6420step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6420step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw6420step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6420step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw6420step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6420 raw6420Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw6420 raw6420Labels = mixedMoment B raw6420step0 raw6420step0Labels := by
      have hz : ∀ j, raw6420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6420step0 = (fun i j => raw6420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6420step0 raw6420; decide +kernel
      have hl : raw6420step0Labels = raw6420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6420 raw6420Labels permutation346 hz
    mixedMoment B raw6420step0 raw6420step0Labels = mixedMoment B raw6420step1 raw6420step1Labels := by
      have hz : ∀ j, raw6420step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6420step1 = (fun i j => raw6420step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6420step1 raw6420step0; decide +kernel
      have hl : raw6420step1Labels = raw6420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6420step0 raw6420step0Labels permutation56 hz
    mixedMoment B raw6420step1 raw6420step1Labels = mixedMoment B raw6420step2 raw6420step2Labels := by
      have ha : raw6420step2 = (fun i j => raw6420step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6420step2 raw6420step1; decide +kernel
      have hl : raw6420step2Labels = raw6420step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6420step1 raw6420step1Labels permutation8 permutation7
    mixedMoment B raw6420step2 raw6420step2Labels = mixedMoment B raw6420step3 raw6420step3Labels := by
      have ha : raw6420step3 = raw6420step2 := by apply Matrix.ext; unfold raw6420step3 raw6420step2; decide +kernel
      have hl : raw6420step2Labels = labelEmbedding1 ∘ raw6420step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6420step2 raw6420step2Labels raw6420step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw6421 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6421step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6421step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6421step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6421 raw6421Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw6421 raw6421Labels = mixedMoment B raw6421step0 raw6421step0Labels := by
      have ha : raw6421step0 = (fun i j => raw6421 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6421step0 raw6421; decide +kernel
      have hl : raw6421step0Labels = raw6421Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6421 raw6421Labels permutation170 permutation5
    mixedMoment B raw6421step0 raw6421step0Labels = mixedMoment B raw6421step1 raw6421step1Labels := by
      have ha : raw6421step1 = -raw6421step0 := by apply Matrix.ext; change ∀ i j, raw6421step1 i j = -(raw6421step0 i j); unfold raw6421step1 raw6421step0; decide +kernel
      have hl : raw6421step1Labels = raw6421step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6421step1 raw6421step1Labels = mixedMoment B raw6421step2 raw6421step2Labels := by
      have ha : raw6421step2 = raw6421step1 := by apply Matrix.ext; unfold raw6421step2 raw6421step1; decide +kernel
      have hl : raw6421step1Labels = labelEmbedding1 ∘ raw6421step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6421step1 raw6421step1Labels raw6421step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3197 node3197Labels := by rfl

def raw6422 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6422step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6422 raw6422Labels = mixedMoment B node3067 node3067Labels := by
  calc
    mixedMoment B raw6422 raw6422Labels = mixedMoment B raw6422step0 raw6422step0Labels := by
      have ha : raw6422step0 = (fun i j => raw6422 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6422step0 raw6422; decide +kernel
      have hl : raw6422step0Labels = raw6422Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6422 raw6422Labels permutation182 permutation7
    mixedMoment B raw6422step0 raw6422step0Labels = mixedMoment B raw6422step1 raw6422step1Labels := by
      have ha : raw6422step1 = raw6422step0 := by apply Matrix.ext; unfold raw6422step1 raw6422step0; decide +kernel
      have hl : raw6422step0Labels = labelEmbedding1 ∘ raw6422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6422step0 raw6422step0Labels raw6422step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3067 node3067Labels := by rfl

def raw6423 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6423step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6423 raw6423Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw6423 raw6423Labels = mixedMoment B raw6423step0 raw6423step0Labels := by
      have ha : raw6423step0 = (fun i j => raw6423 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6423step0 raw6423; decide +kernel
      have hl : raw6423step0Labels = raw6423Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6423 raw6423Labels permutation182 permutation7
    mixedMoment B raw6423step0 raw6423step0Labels = mixedMoment B raw6423step1 raw6423step1Labels := by
      have ha : raw6423step1 = raw6423step0 := by apply Matrix.ext; unfold raw6423step1 raw6423step0; decide +kernel
      have hl : raw6423step0Labels = labelEmbedding1 ∘ raw6423step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6423step0 raw6423step0Labels raw6423step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw6424 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6424 raw6424Labels = mixedMoment B node3063 node3063Labels := by
  calc
    mixedMoment B raw6424 raw6424Labels = mixedMoment B raw6424step0 raw6424step0Labels := by
      have ha : raw6424step0 = (fun i j => raw6424 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6424step0 raw6424; decide +kernel
      have hl : raw6424step0Labels = raw6424Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6424 raw6424Labels permutation182 permutation7
    mixedMoment B raw6424step0 raw6424step0Labels = mixedMoment B raw6424step1 raw6424step1Labels := by
      have ha : raw6424step1 = raw6424step0 := by apply Matrix.ext; unfold raw6424step1 raw6424step0; decide +kernel
      have hl : raw6424step0Labels = labelEmbedding1 ∘ raw6424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6424step0 raw6424step0Labels raw6424step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3063 node3063Labels := by rfl

def raw6425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-2, 1, 1], ![-2, 0, 2]]
def raw6425step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw6425step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6425step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw6425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6425 raw6425Labels = mixedMoment B node3198 node3198Labels := by
  calc
    mixedMoment B raw6425 raw6425Labels = mixedMoment B raw6425step0 raw6425step0Labels := by
      have hz : ∀ j, raw6425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6425step0 = (fun i j => raw6425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6425step0 raw6425; decide +kernel
      have hl : raw6425step0Labels = raw6425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6425 raw6425Labels permutation346 hz
    mixedMoment B raw6425step0 raw6425step0Labels = mixedMoment B raw6425step1 raw6425step1Labels := by
      have ha : raw6425step1 = (fun i j => raw6425step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6425step1 raw6425step0; decide +kernel
      have hl : raw6425step1Labels = raw6425step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6425step0 raw6425step0Labels permutation37 permutation5
    mixedMoment B raw6425step1 raw6425step1Labels = mixedMoment B raw6425step2 raw6425step2Labels := by
      have ha : raw6425step2 = -raw6425step1 := by apply Matrix.ext; change ∀ i j, raw6425step2 i j = -(raw6425step1 i j); unfold raw6425step2 raw6425step1; decide +kernel
      have hl : raw6425step2Labels = raw6425step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6425step2 raw6425step2Labels = mixedMoment B raw6425step3 raw6425step3Labels := by
      have ha : raw6425step3 = raw6425step2 := by apply Matrix.ext; unfold raw6425step3 raw6425step2; decide +kernel
      have hl : raw6425step2Labels = labelEmbedding1 ∘ raw6425step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6425step2 raw6425step2Labels raw6425step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3198 node3198Labels := by rfl

def raw6426 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6426step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6426 raw6426Labels = mixedMoment B node3042 node3042Labels := by
  calc
    mixedMoment B raw6426 raw6426Labels = mixedMoment B raw6426step0 raw6426step0Labels := by
      have hz : ∀ j, raw6426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6426step0 = (fun i j => raw6426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6426step0 raw6426; decide +kernel
      have hl : raw6426step0Labels = raw6426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6426 raw6426Labels permutation346 hz
    mixedMoment B raw6426step0 raw6426step0Labels = mixedMoment B raw6426step1 raw6426step1Labels := by
      have ha : raw6426step1 = (fun i j => raw6426step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6426step1 raw6426step0; decide +kernel
      have hl : raw6426step1Labels = raw6426step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6426step0 raw6426step0Labels permutation38 permutation7
    mixedMoment B raw6426step1 raw6426step1Labels = mixedMoment B raw6426step2 raw6426step2Labels := by
      have ha : raw6426step2 = raw6426step1 := by apply Matrix.ext; unfold raw6426step2 raw6426step1; decide +kernel
      have hl : raw6426step1Labels = labelEmbedding1 ∘ raw6426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6426step1 raw6426step1Labels raw6426step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3042 node3042Labels := by rfl

def raw6427 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6427step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6427 raw6427Labels = mixedMoment B node3028 node3028Labels := by
  calc
    mixedMoment B raw6427 raw6427Labels = mixedMoment B raw6427step0 raw6427step0Labels := by
      have ha : raw6427step0 = (fun i j => raw6427 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6427step0 raw6427; decide +kernel
      have hl : raw6427step0Labels = raw6427Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6427 raw6427Labels permutation200 permutation7
    mixedMoment B raw6427step0 raw6427step0Labels = mixedMoment B raw6427step1 raw6427step1Labels := by
      have ha : raw6427step1 = raw6427step0 := by apply Matrix.ext; unfold raw6427step1 raw6427step0; decide +kernel
      have hl : raw6427step0Labels = labelEmbedding1 ∘ raw6427step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6427step0 raw6427step0Labels raw6427step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3028 node3028Labels := by rfl

def raw6428 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6428step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6428step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6428 raw6428Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw6428 raw6428Labels = mixedMoment B raw6428step0 raw6428step0Labels := by
      have hz : ∀ j, raw6428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6428step0 = (fun i j => raw6428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6428step0 raw6428; decide +kernel
      have hl : raw6428step0Labels = raw6428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6428 raw6428Labels permutation346 hz
    mixedMoment B raw6428step0 raw6428step0Labels = mixedMoment B raw6428step1 raw6428step1Labels := by
      have ha : raw6428step1 = (fun i j => raw6428step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6428step1 raw6428step0; decide +kernel
      have hl : raw6428step1Labels = raw6428step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6428step0 raw6428step0Labels permutation38 permutation7
    mixedMoment B raw6428step1 raw6428step1Labels = mixedMoment B raw6428step2 raw6428step2Labels := by
      have ha : raw6428step2 = raw6428step1 := by apply Matrix.ext; unfold raw6428step2 raw6428step1; decide +kernel
      have hl : raw6428step1Labels = labelEmbedding1 ∘ raw6428step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6428step1 raw6428step1Labels raw6428step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw6429 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6429step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6429 raw6429Labels = mixedMoment B node3035 node3035Labels := by
  calc
    mixedMoment B raw6429 raw6429Labels = mixedMoment B raw6429step0 raw6429step0Labels := by
      have hz : ∀ j, raw6429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6429step0 = (fun i j => raw6429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6429step0 raw6429; decide +kernel
      have hl : raw6429step0Labels = raw6429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6429 raw6429Labels permutation346 hz
    mixedMoment B raw6429step0 raw6429step0Labels = mixedMoment B raw6429step1 raw6429step1Labels := by
      have ha : raw6429step1 = (fun i j => raw6429step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6429step1 raw6429step0; decide +kernel
      have hl : raw6429step1Labels = raw6429step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6429step0 raw6429step0Labels permutation38 permutation7
    mixedMoment B raw6429step1 raw6429step1Labels = mixedMoment B raw6429step2 raw6429step2Labels := by
      have ha : raw6429step2 = raw6429step1 := by apply Matrix.ext; unfold raw6429step2 raw6429step1; decide +kernel
      have hl : raw6429step1Labels = labelEmbedding1 ∘ raw6429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6429step1 raw6429step1Labels raw6429step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3035 node3035Labels := by rfl

def raw6430 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6430step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6430step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6430step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw6430step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6430 raw6430Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw6430 raw6430Labels = mixedMoment B raw6430step0 raw6430step0Labels := by
      have hz : ∀ j, raw6430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6430step0 = (fun i j => raw6430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6430step0 raw6430; decide +kernel
      have hl : raw6430step0Labels = raw6430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6430 raw6430Labels permutation434 hz
    mixedMoment B raw6430step0 raw6430step0Labels = mixedMoment B raw6430step1 raw6430step1Labels := by
      have hz : ∀ j, raw6430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6430step1 = (fun i j => raw6430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6430step1 raw6430step0; decide +kernel
      have hl : raw6430step1Labels = raw6430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6430step0 raw6430step0Labels permutation80 hz
    mixedMoment B raw6430step1 raw6430step1Labels = mixedMoment B raw6430step2 raw6430step2Labels := by
      have ha : raw6430step2 = (fun i j => raw6430step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6430step2 raw6430step1; decide +kernel
      have hl : raw6430step2Labels = raw6430step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6430step1 raw6430step1Labels permutation25 permutation5
    mixedMoment B raw6430step2 raw6430step2Labels = mixedMoment B raw6430step3 raw6430step3Labels := by
      have ha : raw6430step3 = raw6430step2 := by apply Matrix.ext; unfold raw6430step3 raw6430step2; decide +kernel
      have hl : raw6430step2Labels = labelEmbedding1 ∘ raw6430step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6430step2 raw6430step2Labels raw6430step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw6431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6431step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6431step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6431step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6431step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6431 raw6431Labels = mixedMoment B node3211 node3211Labels := by
  calc
    mixedMoment B raw6431 raw6431Labels = mixedMoment B raw6431step0 raw6431step0Labels := by
      have hz : ∀ j, raw6431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6431step0 = (fun i j => raw6431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6431step0 raw6431; decide +kernel
      have hl : raw6431step0Labels = raw6431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6431 raw6431Labels permutation346 hz
    mixedMoment B raw6431step0 raw6431step0Labels = mixedMoment B raw6431step1 raw6431step1Labels := by
      have ha : raw6431step1 = (fun i j => raw6431step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6431step1 raw6431step0; decide +kernel
      have hl : raw6431step1Labels = raw6431step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6431step0 raw6431step0Labels permutation36 permutation5
    mixedMoment B raw6431step1 raw6431step1Labels = mixedMoment B raw6431step2 raw6431step2Labels := by
      have ha : raw6431step2 = -raw6431step1 := by apply Matrix.ext; change ∀ i j, raw6431step2 i j = -(raw6431step1 i j); unfold raw6431step2 raw6431step1; decide +kernel
      have hl : raw6431step2Labels = raw6431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6431step2 raw6431step2Labels = mixedMoment B raw6431step3 raw6431step3Labels := by
      have ha : raw6431step3 = raw6431step2 := by apply Matrix.ext; unfold raw6431step3 raw6431step2; decide +kernel
      have hl : raw6431step2Labels = labelEmbedding1 ∘ raw6431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6431step2 raw6431step2Labels raw6431step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3211 node3211Labels := by rfl

def raw6432 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6432step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6432step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6432 raw6432Labels = mixedMoment B node3092 node3092Labels := by
  calc
    mixedMoment B raw6432 raw6432Labels = mixedMoment B raw6432step0 raw6432step0Labels := by
      have hz : ∀ j, raw6432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6432step0 = (fun i j => raw6432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6432step0 raw6432; decide +kernel
      have hl : raw6432step0Labels = raw6432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6432 raw6432Labels permutation346 hz
    mixedMoment B raw6432step0 raw6432step0Labels = mixedMoment B raw6432step1 raw6432step1Labels := by
      have ha : raw6432step1 = (fun i j => raw6432step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6432step1 raw6432step0; decide +kernel
      have hl : raw6432step1Labels = raw6432step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6432step0 raw6432step0Labels permutation38 permutation7
    mixedMoment B raw6432step1 raw6432step1Labels = mixedMoment B raw6432step2 raw6432step2Labels := by
      have ha : raw6432step2 = raw6432step1 := by apply Matrix.ext; unfold raw6432step2 raw6432step1; decide +kernel
      have hl : raw6432step1Labels = labelEmbedding1 ∘ raw6432step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6432step1 raw6432step1Labels raw6432step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3092 node3092Labels := by rfl

def raw6433 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6433step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6433 raw6433Labels = mixedMoment B node3080 node3080Labels := by
  calc
    mixedMoment B raw6433 raw6433Labels = mixedMoment B raw6433step0 raw6433step0Labels := by
      have ha : raw6433step0 = (fun i j => raw6433 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6433step0 raw6433; decide +kernel
      have hl : raw6433step0Labels = raw6433Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6433 raw6433Labels permutation200 permutation7
    mixedMoment B raw6433step0 raw6433step0Labels = mixedMoment B raw6433step1 raw6433step1Labels := by
      have ha : raw6433step1 = raw6433step0 := by apply Matrix.ext; unfold raw6433step1 raw6433step0; decide +kernel
      have hl : raw6433step0Labels = labelEmbedding1 ∘ raw6433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6433step0 raw6433step0Labels raw6433step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3080 node3080Labels := by rfl

def raw6434 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6434step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6434 raw6434Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw6434 raw6434Labels = mixedMoment B raw6434step0 raw6434step0Labels := by
      have hz : ∀ j, raw6434 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6434step0 = (fun i j => raw6434 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6434step0 raw6434; decide +kernel
      have hl : raw6434step0Labels = raw6434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6434 raw6434Labels permutation346 hz
    mixedMoment B raw6434step0 raw6434step0Labels = mixedMoment B raw6434step1 raw6434step1Labels := by
      have ha : raw6434step1 = (fun i j => raw6434step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6434step1 raw6434step0; decide +kernel
      have hl : raw6434step1Labels = raw6434step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6434step0 raw6434step0Labels permutation38 permutation7
    mixedMoment B raw6434step1 raw6434step1Labels = mixedMoment B raw6434step2 raw6434step2Labels := by
      have ha : raw6434step2 = raw6434step1 := by apply Matrix.ext; unfold raw6434step2 raw6434step1; decide +kernel
      have hl : raw6434step1Labels = labelEmbedding1 ∘ raw6434step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6434step1 raw6434step1Labels raw6434step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw6435 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6435 raw6435Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw6435 raw6435Labels = mixedMoment B raw6435step0 raw6435step0Labels := by
      have hz : ∀ j, raw6435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6435step0 = (fun i j => raw6435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6435step0 raw6435; decide +kernel
      have hl : raw6435step0Labels = raw6435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6435 raw6435Labels permutation346 hz
    mixedMoment B raw6435step0 raw6435step0Labels = mixedMoment B raw6435step1 raw6435step1Labels := by
      have ha : raw6435step1 = (fun i j => raw6435step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6435step1 raw6435step0; decide +kernel
      have hl : raw6435step1Labels = raw6435step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6435step0 raw6435step0Labels permutation40 permutation2
    mixedMoment B raw6435step1 raw6435step1Labels = mixedMoment B raw6435step2 raw6435step2Labels := by
      have ha : raw6435step2 = -raw6435step1 := by apply Matrix.ext; change ∀ i j, raw6435step2 i j = -(raw6435step1 i j); unfold raw6435step2 raw6435step1; decide +kernel
      have hl : raw6435step2Labels = raw6435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3506 node3506Labels := by rfl

def raw6436 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw6436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw6436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6436 raw6436Labels = mixedMoment B node3502 node3502Labels := by
  calc
    mixedMoment B raw6436 raw6436Labels = mixedMoment B raw6436step0 raw6436step0Labels := by
      have ha : raw6436step0 = (fun i j => raw6436 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6436step0 raw6436; decide +kernel
      have hl : raw6436step0Labels = raw6436Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6436 raw6436Labels permutation212 permutation2
    mixedMoment B raw6436step0 raw6436step0Labels = mixedMoment B raw6436step1 raw6436step1Labels := by
      have ha : raw6436step1 = -raw6436step0 := by apply Matrix.ext; change ∀ i j, raw6436step1 i j = -(raw6436step0 i j); unfold raw6436step1 raw6436step0; decide +kernel
      have hl : raw6436step1Labels = raw6436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3502 node3502Labels := by rfl

def raw6437 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6437step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6437 raw6437Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw6437 raw6437Labels = mixedMoment B raw6437step0 raw6437step0Labels := by
      have hz : ∀ j, raw6437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6437step0 = (fun i j => raw6437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6437step0 raw6437; decide +kernel
      have hl : raw6437step0Labels = raw6437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6437 raw6437Labels permutation346 hz
    mixedMoment B raw6437step0 raw6437step0Labels = mixedMoment B raw6437step1 raw6437step1Labels := by
      have ha : raw6437step1 = (fun i j => raw6437step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6437step1 raw6437step0; decide +kernel
      have hl : raw6437step1Labels = raw6437step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6437step0 raw6437step0Labels permutation40 permutation2
    mixedMoment B raw6437step1 raw6437step1Labels = mixedMoment B raw6437step2 raw6437step2Labels := by
      have ha : raw6437step2 = -raw6437step1 := by apply Matrix.ext; change ∀ i j, raw6437step2 i j = -(raw6437step1 i j); unfold raw6437step2 raw6437step1; decide +kernel
      have hl : raw6437step2Labels = raw6437step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw6438 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw6438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6438 raw6438Labels = mixedMoment B node2588 node2588Labels := by
  calc
    mixedMoment B raw6438 raw6438Labels = mixedMoment B raw6438step0 raw6438step0Labels := by
      have hz : ∀ j, raw6438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6438step0 = (fun i j => raw6438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6438step0 raw6438; decide +kernel
      have hl : raw6438step0Labels = raw6438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6438 raw6438Labels permutation346 hz
    mixedMoment B raw6438step0 raw6438step0Labels = mixedMoment B raw6438step1 raw6438step1Labels := by
      have ha : raw6438step1 = (fun i j => raw6438step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6438step1 raw6438step0; decide +kernel
      have hl : raw6438step1Labels = raw6438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6438step0 raw6438step0Labels permutation139 permutation2
    _ = mixedMoment B node2588 node2588Labels := by rfl

def raw6439 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6439step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6439step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6439 raw6439Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw6439 raw6439Labels = mixedMoment B raw6439step0 raw6439step0Labels := by
      have hz : ∀ j, raw6439 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6439step0 = (fun i j => raw6439 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6439step0 raw6439; decide +kernel
      have hl : raw6439step0Labels = raw6439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6439 raw6439Labels permutation346 hz
    mixedMoment B raw6439step0 raw6439step0Labels = mixedMoment B raw6439step1 raw6439step1Labels := by
      have hz : ∀ j, raw6439step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6439step1 = (fun i j => raw6439step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6439step1 raw6439step0; decide +kernel
      have hl : raw6439step1Labels = raw6439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6439step0 raw6439step0Labels permutation56 hz
    mixedMoment B raw6439step1 raw6439step1Labels = mixedMoment B raw6439step2 raw6439step2Labels := by
      have ha : raw6439step2 = (fun i j => raw6439step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6439step2 raw6439step1; decide +kernel
      have hl : raw6439step2Labels = raw6439step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6439step1 raw6439step1Labels permutation12 permutation4
    mixedMoment B raw6439step2 raw6439step2Labels = mixedMoment B raw6439step3 raw6439step3Labels := by
      have ha : raw6439step3 = -raw6439step2 := by apply Matrix.ext; change ∀ i j, raw6439step3 i j = -(raw6439step2 i j); unfold raw6439step3 raw6439step2; decide +kernel
      have hl : raw6439step3Labels = raw6439step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw6440 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw6440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6440 raw6440Labels = mixedMoment B node2033 node2033Labels := by
  calc
    mixedMoment B raw6440 raw6440Labels = mixedMoment B raw6440step0 raw6440step0Labels := by
      have ha : raw6440step0 = (fun i j => raw6440 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6440step0 raw6440; decide +kernel
      have hl : raw6440step0Labels = raw6440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6440 raw6440Labels permutation170 permutation4
    mixedMoment B raw6440step0 raw6440step0Labels = mixedMoment B raw6440step1 raw6440step1Labels := by
      have ha : raw6440step1 = -raw6440step0 := by apply Matrix.ext; change ∀ i j, raw6440step1 i j = -(raw6440step0 i j); unfold raw6440step1 raw6440step0; decide +kernel
      have hl : raw6440step1Labels = raw6440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2033 node2033Labels := by rfl

def raw6441 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw6441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6441 raw6441Labels = mixedMoment B node2039 node2039Labels := by
  calc
    mixedMoment B raw6441 raw6441Labels = mixedMoment B raw6441step0 raw6441step0Labels := by
      have hz : ∀ j, raw6441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6441step0 = (fun i j => raw6441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6441step0 raw6441; decide +kernel
      have hl : raw6441step0Labels = raw6441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6441 raw6441Labels permutation346 hz
    mixedMoment B raw6441step0 raw6441step0Labels = mixedMoment B raw6441step1 raw6441step1Labels := by
      have ha : raw6441step1 = (fun i j => raw6441step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6441step1 raw6441step0; decide +kernel
      have hl : raw6441step1Labels = raw6441step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6441step0 raw6441step0Labels permutation36 permutation4
    mixedMoment B raw6441step1 raw6441step1Labels = mixedMoment B raw6441step2 raw6441step2Labels := by
      have ha : raw6441step2 = -raw6441step1 := by apply Matrix.ext; change ∀ i j, raw6441step2 i j = -(raw6441step1 i j); unfold raw6441step2 raw6441step1; decide +kernel
      have hl : raw6441step2Labels = raw6441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2039 node2039Labels := by rfl

def raw6442 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6442 raw6442Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw6442 raw6442Labels = mixedMoment B raw6442step0 raw6442step0Labels := by
      have hz : ∀ j, raw6442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6442step0 = (fun i j => raw6442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6442step0 raw6442; decide +kernel
      have hl : raw6442step0Labels = raw6442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6442 raw6442Labels permutation346 hz
    mixedMoment B raw6442step0 raw6442step0Labels = mixedMoment B raw6442step1 raw6442step1Labels := by
      have ha : raw6442step1 = (fun i j => raw6442step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6442step1 raw6442step0; decide +kernel
      have hl : raw6442step1Labels = raw6442step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6442step0 raw6442step0Labels permutation36 permutation4
    mixedMoment B raw6442step1 raw6442step1Labels = mixedMoment B raw6442step2 raw6442step2Labels := by
      have ha : raw6442step2 = -raw6442step1 := by apply Matrix.ext; change ∀ i j, raw6442step2 i j = -(raw6442step1 i j); unfold raw6442step2 raw6442step1; decide +kernel
      have hl : raw6442step2Labels = raw6442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

def raw6443 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6443step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6443 raw6443Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw6443 raw6443Labels = mixedMoment B raw6443step0 raw6443step0Labels := by
      have hz : ∀ j, raw6443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6443step0 = (fun i j => raw6443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6443step0 raw6443; decide +kernel
      have hl : raw6443step0Labels = raw6443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6443 raw6443Labels permutation346 hz
    mixedMoment B raw6443step0 raw6443step0Labels = mixedMoment B raw6443step1 raw6443step1Labels := by
      have ha : raw6443step1 = (fun i j => raw6443step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6443step1 raw6443step0; decide +kernel
      have hl : raw6443step1Labels = raw6443step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6443step0 raw6443step0Labels permutation33 permutation4
    mixedMoment B raw6443step1 raw6443step1Labels = mixedMoment B raw6443step2 raw6443step2Labels := by
      have ha : raw6443step2 = -raw6443step1 := by apply Matrix.ext; change ∀ i j, raw6443step2 i j = -(raw6443step1 i j); unfold raw6443step2 raw6443step1; decide +kernel
      have hl : raw6443step2Labels = raw6443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw6444 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6444 raw6444Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw6444 raw6444Labels = mixedMoment B raw6444step0 raw6444step0Labels := by
      have hz : ∀ j, raw6444 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw6444step0 = (fun i j => raw6444 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw6444step0 raw6444; decide +kernel
      have hl : raw6444step0Labels = raw6444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6444 raw6444Labels permutation265 hz
    mixedMoment B raw6444step0 raw6444step0Labels = mixedMoment B raw6444step1 raw6444step1Labels := by
      have ha : raw6444step1 = (fun i j => raw6444step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6444step1 raw6444step0; decide +kernel
      have hl : raw6444step1Labels = raw6444step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6444step0 raw6444step0Labels permutation36 permutation4
    mixedMoment B raw6444step1 raw6444step1Labels = mixedMoment B raw6444step2 raw6444step2Labels := by
      have ha : raw6444step2 = -raw6444step1 := by apply Matrix.ext; change ∀ i j, raw6444step2 i j = -(raw6444step1 i j); unfold raw6444step2 raw6444step1; decide +kernel
      have hl : raw6444step2Labels = raw6444step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw6445 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw6445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6445step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6445 raw6445Labels = mixedMoment B node3632 node3632Labels := by
  calc
    mixedMoment B raw6445 raw6445Labels = mixedMoment B raw6445step0 raw6445step0Labels := by
      have hz : ∀ j, raw6445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6445step0 = (fun i j => raw6445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6445step0 raw6445; decide +kernel
      have hl : raw6445step0Labels = raw6445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6445 raw6445Labels permutation346 hz
    mixedMoment B raw6445step0 raw6445step0Labels = mixedMoment B raw6445step1 raw6445step1Labels := by
      have hz : ∀ j, raw6445step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6445step1 = (fun i j => raw6445step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6445step1 raw6445step0; decide +kernel
      have hl : raw6445step1Labels = raw6445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6445step0 raw6445step0Labels permutation56 hz
    mixedMoment B raw6445step1 raw6445step1Labels = mixedMoment B raw6445step2 raw6445step2Labels := by
      have ha : raw6445step2 = (fun i j => raw6445step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6445step2 raw6445step1; decide +kernel
      have hl : raw6445step2Labels = raw6445step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6445step1 raw6445step1Labels permutation12 permutation4
    mixedMoment B raw6445step2 raw6445step2Labels = mixedMoment B raw6445step3 raw6445step3Labels := by
      have ha : raw6445step3 = -raw6445step2 := by apply Matrix.ext; change ∀ i j, raw6445step3 i j = -(raw6445step2 i j); unfold raw6445step3 raw6445step2; decide +kernel
      have hl : raw6445step3Labels = raw6445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3632 node3632Labels := by rfl

def raw6446 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw6446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6446 raw6446Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw6446 raw6446Labels = mixedMoment B raw6446step0 raw6446step0Labels := by
      have hz : ∀ j, raw6446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6446step0 = (fun i j => raw6446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6446step0 raw6446; decide +kernel
      have hl : raw6446step0Labels = raw6446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6446 raw6446Labels permutation346 hz
    mixedMoment B raw6446step0 raw6446step0Labels = mixedMoment B raw6446step1 raw6446step1Labels := by
      have hz : ∀ j, raw6446step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6446step1 = (fun i j => raw6446step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6446step1 raw6446step0; decide +kernel
      have hl : raw6446step1Labels = raw6446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6446step0 raw6446step0Labels permutation56 hz
    mixedMoment B raw6446step1 raw6446step1Labels = mixedMoment B raw6446step2 raw6446step2Labels := by
      have ha : raw6446step2 = (fun i j => raw6446step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6446step2 raw6446step1; decide +kernel
      have hl : raw6446step2Labels = raw6446step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6446step1 raw6446step1Labels permutation31 permutation2
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw6447 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw6447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6447step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6447 raw6447Labels = mixedMoment B node3381 node3381Labels := by
  calc
    mixedMoment B raw6447 raw6447Labels = mixedMoment B raw6447step0 raw6447step0Labels := by
      have ha : raw6447step0 = (fun i j => raw6447 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6447step0 raw6447; decide +kernel
      have hl : raw6447step0Labels = raw6447Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6447 raw6447Labels permutation170 permutation4
    mixedMoment B raw6447step0 raw6447step0Labels = mixedMoment B raw6447step1 raw6447step1Labels := by
      have ha : raw6447step1 = -raw6447step0 := by apply Matrix.ext; change ∀ i j, raw6447step1 i j = -(raw6447step0 i j); unfold raw6447step1 raw6447step0; decide +kernel
      have hl : raw6447step1Labels = raw6447step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3381 node3381Labels := by rfl

def raw6448 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw6448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6448 raw6448Labels = mixedMoment B node3383 node3383Labels := by
  calc
    mixedMoment B raw6448 raw6448Labels = mixedMoment B raw6448step0 raw6448step0Labels := by
      have hz : ∀ j, raw6448 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6448step0 = (fun i j => raw6448 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6448step0 raw6448; decide +kernel
      have hl : raw6448step0Labels = raw6448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6448 raw6448Labels permutation346 hz
    mixedMoment B raw6448step0 raw6448step0Labels = mixedMoment B raw6448step1 raw6448step1Labels := by
      have ha : raw6448step1 = (fun i j => raw6448step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6448step1 raw6448step0; decide +kernel
      have hl : raw6448step1Labels = raw6448step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6448step0 raw6448step0Labels permutation36 permutation4
    mixedMoment B raw6448step1 raw6448step1Labels = mixedMoment B raw6448step2 raw6448step2Labels := by
      have ha : raw6448step2 = -raw6448step1 := by apply Matrix.ext; change ∀ i j, raw6448step2 i j = -(raw6448step1 i j); unfold raw6448step2 raw6448step1; decide +kernel
      have hl : raw6448step2Labels = raw6448step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3383 node3383Labels := by rfl

def raw6449 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6449 raw6449Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw6449 raw6449Labels = mixedMoment B raw6449step0 raw6449step0Labels := by
      have hz : ∀ j, raw6449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6449step0 = (fun i j => raw6449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6449step0 raw6449; decide +kernel
      have hl : raw6449step0Labels = raw6449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6449 raw6449Labels permutation346 hz
    mixedMoment B raw6449step0 raw6449step0Labels = mixedMoment B raw6449step1 raw6449step1Labels := by
      have ha : raw6449step1 = (fun i j => raw6449step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6449step1 raw6449step0; decide +kernel
      have hl : raw6449step1Labels = raw6449step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6449step0 raw6449step0Labels permutation33 permutation4
    mixedMoment B raw6449step1 raw6449step1Labels = mixedMoment B raw6449step2 raw6449step2Labels := by
      have ha : raw6449step2 = -raw6449step1 := by apply Matrix.ext; change ∀ i j, raw6449step2 i j = -(raw6449step1 i j); unfold raw6449step2 raw6449step1; decide +kernel
      have hl : raw6449step2Labels = raw6449step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3392 node3392Labels := by rfl

def raw6450 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw6450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6450 raw6450Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw6450 raw6450Labels = mixedMoment B raw6450step0 raw6450step0Labels := by
      have ha : raw6450step0 = (fun i j => raw6450 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6450step0 raw6450; decide +kernel
      have hl : raw6450step0Labels = raw6450Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6450 raw6450Labels permutation170 permutation4
    mixedMoment B raw6450step0 raw6450step0Labels = mixedMoment B raw6450step1 raw6450step1Labels := by
      have ha : raw6450step1 = -raw6450step0 := by apply Matrix.ext; change ∀ i j, raw6450step1 i j = -(raw6450step0 i j); unfold raw6450step1 raw6450step0; decide +kernel
      have hl : raw6450step1Labels = raw6450step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw6451 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6451 raw6451Labels = mixedMoment B node2586 node2586Labels := by
  calc
    mixedMoment B raw6451 raw6451Labels = mixedMoment B raw6451step0 raw6451step0Labels := by
      have ha : raw6451step0 = (fun i j => raw6451 (permutation620 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6451step0 raw6451; decide +kernel
      have hl : raw6451step0Labels = raw6451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6451 raw6451Labels permutation620 permutation2
    _ = mixedMoment B node2586 node2586Labels := by rfl

def raw6452 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw6452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6452 raw6452Labels = mixedMoment B node3490 node3490Labels := by
  calc
    mixedMoment B raw6452 raw6452Labels = mixedMoment B raw6452step0 raw6452step0Labels := by
      have ha : raw6452step0 = (fun i j => raw6452 (permutation156 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6452step0 raw6452; decide +kernel
      have hl : raw6452step0Labels = raw6452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6452 raw6452Labels permutation156 permutation4
    mixedMoment B raw6452step0 raw6452step0Labels = mixedMoment B raw6452step1 raw6452step1Labels := by
      have ha : raw6452step1 = -raw6452step0 := by apply Matrix.ext; change ∀ i j, raw6452step1 i j = -(raw6452step0 i j); unfold raw6452step1 raw6452step0; decide +kernel
      have hl : raw6452step1Labels = raw6452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3490 node3490Labels := by rfl

def raw6453 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6453step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6453 raw6453Labels = mixedMoment B node3494 node3494Labels := by
  calc
    mixedMoment B raw6453 raw6453Labels = mixedMoment B raw6453step0 raw6453step0Labels := by
      have ha : raw6453step0 = (fun i j => raw6453 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6453step0 raw6453; decide +kernel
      have hl : raw6453step0Labels = raw6453Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6453 raw6453Labels permutation153 permutation4
    mixedMoment B raw6453step0 raw6453step0Labels = mixedMoment B raw6453step1 raw6453step1Labels := by
      have ha : raw6453step1 = -raw6453step0 := by apply Matrix.ext; change ∀ i j, raw6453step1 i j = -(raw6453step0 i j); unfold raw6453step1 raw6453step0; decide +kernel
      have hl : raw6453step1Labels = raw6453step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3494 node3494Labels := by rfl

def raw6454 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6454step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6454 raw6454Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw6454 raw6454Labels = mixedMoment B raw6454step0 raw6454step0Labels := by
      have hz : ∀ j, raw6454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6454step0 = (fun i j => raw6454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6454step0 raw6454; decide +kernel
      have hl : raw6454step0Labels = raw6454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6454 raw6454Labels permutation346 hz
    mixedMoment B raw6454step0 raw6454step0Labels = mixedMoment B raw6454step1 raw6454step1Labels := by
      have ha : raw6454step1 = (fun i j => raw6454step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6454step1 raw6454step0; decide +kernel
      have hl : raw6454step1Labels = raw6454step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6454step0 raw6454step0Labels permutation37 permutation4
    mixedMoment B raw6454step1 raw6454step1Labels = mixedMoment B raw6454step2 raw6454step2Labels := by
      have ha : raw6454step2 = -raw6454step1 := by apply Matrix.ext; change ∀ i j, raw6454step2 i j = -(raw6454step1 i j); unfold raw6454step2 raw6454step1; decide +kernel
      have hl : raw6454step2Labels = raw6454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw6455 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6455 raw6455Labels = mixedMoment B node2592 node2592Labels := by
  calc
    mixedMoment B raw6455 raw6455Labels = mixedMoment B raw6455step0 raw6455step0Labels := by
      have hz : ∀ j, raw6455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6455step0 = (fun i j => raw6455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6455step0 raw6455; decide +kernel
      have hl : raw6455step0Labels = raw6455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6455 raw6455Labels permutation346 hz
    mixedMoment B raw6455step0 raw6455step0Labels = mixedMoment B raw6455step1 raw6455step1Labels := by
      have ha : raw6455step1 = (fun i j => raw6455step0 (permutation138 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6455step1 raw6455step0; decide +kernel
      have hl : raw6455step1Labels = raw6455step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6455step0 raw6455step0Labels permutation138 permutation2
    _ = mixedMoment B node2592 node2592Labels := by rfl

def raw6456 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6456 raw6456Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw6456 raw6456Labels = mixedMoment B raw6456step0 raw6456step0Labels := by
      have hz : ∀ j, raw6456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6456step0 = (fun i j => raw6456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6456step0 raw6456; decide +kernel
      have hl : raw6456step0Labels = raw6456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6456 raw6456Labels permutation346 hz
    mixedMoment B raw6456step0 raw6456step0Labels = mixedMoment B raw6456step1 raw6456step1Labels := by
      have ha : raw6456step1 = (fun i j => raw6456step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6456step1 raw6456step0; decide +kernel
      have hl : raw6456step1Labels = raw6456step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6456step0 raw6456step0Labels permutation32 permutation4
    mixedMoment B raw6456step1 raw6456step1Labels = mixedMoment B raw6456step2 raw6456step2Labels := by
      have ha : raw6456step2 = -raw6456step1 := by apply Matrix.ext; change ∀ i j, raw6456step2 i j = -(raw6456step1 i j); unfold raw6456step2 raw6456step1; decide +kernel
      have hl : raw6456step2Labels = raw6456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw6457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6457step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6457step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6457step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6457step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6457 raw6457Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw6457 raw6457Labels = mixedMoment B raw6457step0 raw6457step0Labels := by
      have hz : ∀ j, raw6457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6457step0 = (fun i j => raw6457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6457step0 raw6457; decide +kernel
      have hl : raw6457step0Labels = raw6457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6457 raw6457Labels permutation346 hz
    mixedMoment B raw6457step0 raw6457step0Labels = mixedMoment B raw6457step1 raw6457step1Labels := by
      have ha : raw6457step1 = (fun i j => raw6457step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6457step1 raw6457step0; decide +kernel
      have hl : raw6457step1Labels = raw6457step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6457step0 raw6457step0Labels permutation35 permutation7
    mixedMoment B raw6457step1 raw6457step1Labels = mixedMoment B raw6457step2 raw6457step2Labels := by
      have ha : raw6457step2 = -raw6457step1 := by apply Matrix.ext; change ∀ i j, raw6457step2 i j = -(raw6457step1 i j); unfold raw6457step2 raw6457step1; decide +kernel
      have hl : raw6457step2Labels = raw6457step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6457step2 raw6457step2Labels = mixedMoment B raw6457step3 raw6457step3Labels := by
      have ha : raw6457step3 = raw6457step2 := by apply Matrix.ext; unfold raw6457step3 raw6457step2; decide +kernel
      have hl : raw6457step2Labels = labelEmbedding10 ∘ raw6457step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6457step2 raw6457step2Labels raw6457step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw6458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6458step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6458step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6458step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6458step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6458 raw6458Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw6458 raw6458Labels = mixedMoment B raw6458step0 raw6458step0Labels := by
      have ha : raw6458step0 = (fun i j => raw6458 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6458step0 raw6458; decide +kernel
      have hl : raw6458step0Labels = raw6458Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6458 raw6458Labels permutation155 permutation7
    mixedMoment B raw6458step0 raw6458step0Labels = mixedMoment B raw6458step1 raw6458step1Labels := by
      have ha : raw6458step1 = -raw6458step0 := by apply Matrix.ext; change ∀ i j, raw6458step1 i j = -(raw6458step0 i j); unfold raw6458step1 raw6458step0; decide +kernel
      have hl : raw6458step1Labels = raw6458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6458step1 raw6458step1Labels = mixedMoment B raw6458step2 raw6458step2Labels := by
      have ha : raw6458step2 = raw6458step1 := by apply Matrix.ext; unfold raw6458step2 raw6458step1; decide +kernel
      have hl : raw6458step1Labels = labelEmbedding10 ∘ raw6458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6458step1 raw6458step1Labels raw6458step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw6459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6459step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6459step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw6459step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6459step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6459step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6459step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6459step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6459 raw6459Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw6459 raw6459Labels = mixedMoment B raw6459step0 raw6459step0Labels := by
      have hz : ∀ j, raw6459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6459step0 = (fun i j => raw6459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6459step0 raw6459; decide +kernel
      have hl : raw6459step0Labels = raw6459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6459 raw6459Labels permutation346 hz
    mixedMoment B raw6459step0 raw6459step0Labels = mixedMoment B raw6459step1 raw6459step1Labels := by
      have ha : raw6459step1 = (fun i j => raw6459step0 (permutation85 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6459step1 raw6459step0; decide +kernel
      have hl : raw6459step1Labels = raw6459step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6459step0 raw6459step0Labels permutation85 permutation4
    mixedMoment B raw6459step1 raw6459step1Labels = mixedMoment B raw6459step2 raw6459step2Labels := by
      have ha : raw6459step2 = -raw6459step1 := by apply Matrix.ext; change ∀ i j, raw6459step2 i j = -(raw6459step1 i j); unfold raw6459step2 raw6459step1; decide +kernel
      have hl : raw6459step2Labels = raw6459step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6459step2 raw6459step2Labels = mixedMoment B raw6459step3 raw6459step3Labels := by
      have ha : raw6459step3 = raw6459step2 := by apply Matrix.ext; unfold raw6459step3 raw6459step2; decide +kernel
      have hl : raw6459step2Labels = labelEmbedding7 ∘ raw6459step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6459step2 raw6459step2Labels raw6459step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw6460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6460step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6460step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw6460step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6460step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6460step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6460step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6460step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6460 raw6460Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw6460 raw6460Labels = mixedMoment B raw6460step0 raw6460step0Labels := by
      have hz : ∀ j, raw6460 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6460step0 = (fun i j => raw6460 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6460step0 raw6460; decide +kernel
      have hl : raw6460step0Labels = raw6460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6460 raw6460Labels permutation520 hz
    mixedMoment B raw6460step0 raw6460step0Labels = mixedMoment B raw6460step1 raw6460step1Labels := by
      have hz : ∀ j, raw6460step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6460step1 = (fun i j => raw6460step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6460step1 raw6460step0; decide +kernel
      have hl : raw6460step1Labels = raw6460step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6460step0 raw6460step0Labels permutation80 hz
    mixedMoment B raw6460step1 raw6460step1Labels = mixedMoment B raw6460step2 raw6460step2Labels := by
      have ha : raw6460step2 = (fun i j => raw6460step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6460step2 raw6460step1; decide +kernel
      have hl : raw6460step2Labels = raw6460step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6460step1 raw6460step1Labels permutation9 permutation7
    mixedMoment B raw6460step2 raw6460step2Labels = mixedMoment B raw6460step3 raw6460step3Labels := by
      have ha : raw6460step3 = -raw6460step2 := by apply Matrix.ext; change ∀ i j, raw6460step3 i j = -(raw6460step2 i j); unfold raw6460step3 raw6460step2; decide +kernel
      have hl : raw6460step3Labels = raw6460step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6460step3 raw6460step3Labels = mixedMoment B raw6460step4 raw6460step4Labels := by
      have ha : raw6460step4 = raw6460step3 := by apply Matrix.ext; unfold raw6460step4 raw6460step3; decide +kernel
      have hl : raw6460step3Labels = labelEmbedding10 ∘ raw6460step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6460step3 raw6460step3Labels raw6460step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw6461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6461step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6461step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6461 raw6461Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw6461 raw6461Labels = mixedMoment B raw6461step0 raw6461step0Labels := by
      have hz : ∀ j, raw6461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6461step0 = (fun i j => raw6461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6461step0 raw6461; decide +kernel
      have hl : raw6461step0Labels = raw6461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6461 raw6461Labels permutation346 hz
    mixedMoment B raw6461step0 raw6461step0Labels = mixedMoment B raw6461step1 raw6461step1Labels := by
      have ha : raw6461step1 = (fun i j => raw6461step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6461step1 raw6461step0; decide +kernel
      have hl : raw6461step1Labels = raw6461step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6461step0 raw6461step0Labels permutation103 permutation6
    mixedMoment B raw6461step1 raw6461step1Labels = mixedMoment B raw6461step2 raw6461step2Labels := by
      have ha : raw6461step2 = raw6461step1 := by apply Matrix.ext; unfold raw6461step2 raw6461step1; decide +kernel
      have hl : raw6461step1Labels = labelEmbedding9 ∘ raw6461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6461step1 raw6461step1Labels raw6461step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw6462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6462step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6462step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6462 raw6462Labels = mixedMoment B node4571 node4571Labels := by
  calc
    mixedMoment B raw6462 raw6462Labels = mixedMoment B raw6462step0 raw6462step0Labels := by
      have hz : ∀ j, raw6462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6462step0 = (fun i j => raw6462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6462step0 raw6462; decide +kernel
      have hl : raw6462step0Labels = raw6462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6462 raw6462Labels permutation346 hz
    mixedMoment B raw6462step0 raw6462step0Labels = mixedMoment B raw6462step1 raw6462step1Labels := by
      have ha : raw6462step1 = (fun i j => raw6462step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6462step1 raw6462step0; decide +kernel
      have hl : raw6462step1Labels = raw6462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6462step0 raw6462step0Labels permutation40 permutation3
    mixedMoment B raw6462step1 raw6462step1Labels = mixedMoment B raw6462step2 raw6462step2Labels := by
      have ha : raw6462step2 = raw6462step1 := by apply Matrix.ext; unfold raw6462step2 raw6462step1; decide +kernel
      have hl : raw6462step1Labels = labelEmbedding6 ∘ raw6462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6462step1 raw6462step1Labels raw6462step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4571 node4571Labels := by rfl

def raw6463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw6463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6463 raw6463Labels = mixedMoment B node5153 node5153Labels := by
  calc
    mixedMoment B raw6463 raw6463Labels = mixedMoment B raw6463step0 raw6463step0Labels := by
      have ha : raw6463step0 = (fun i j => raw6463 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6463step0 raw6463; decide +kernel
      have hl : raw6463step0Labels = raw6463Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6463 raw6463Labels permutation182 permutation2
    _ = mixedMoment B node5153 node5153Labels := by rfl

def raw6464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw6464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6464 raw6464Labels = mixedMoment B node5211 node5211Labels := by
  calc
    mixedMoment B raw6464 raw6464Labels = mixedMoment B raw6464step0 raw6464step0Labels := by
      have hz : ∀ j, raw6464 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6464step0 = (fun i j => raw6464 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6464step0 raw6464; decide +kernel
      have hl : raw6464step0Labels = raw6464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6464 raw6464Labels permutation346 hz
    mixedMoment B raw6464step0 raw6464step0Labels = mixedMoment B raw6464step1 raw6464step1Labels := by
      have ha : raw6464step1 = (fun i j => raw6464step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6464step1 raw6464step0; decide +kernel
      have hl : raw6464step1Labels = raw6464step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6464step0 raw6464step0Labels permutation38 permutation2
    _ = mixedMoment B node5211 node5211Labels := by rfl

def raw6465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6465step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6465step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6465 raw6465Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw6465 raw6465Labels = mixedMoment B raw6465step0 raw6465step0Labels := by
      have hz : ∀ j, raw6465 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6465step0 = (fun i j => raw6465 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6465step0 raw6465; decide +kernel
      have hl : raw6465step0Labels = raw6465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6465 raw6465Labels permutation520 hz
    mixedMoment B raw6465step0 raw6465step0Labels = mixedMoment B raw6465step1 raw6465step1Labels := by
      have hz : ∀ j, raw6465step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6465step1 = (fun i j => raw6465step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6465step1 raw6465step0; decide +kernel
      have hl : raw6465step1Labels = raw6465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6465step0 raw6465step0Labels permutation80 hz
    mixedMoment B raw6465step1 raw6465step1Labels = mixedMoment B raw6465step2 raw6465step2Labels := by
      have ha : raw6465step2 = (fun i j => raw6465step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6465step2 raw6465step1; decide +kernel
      have hl : raw6465step2Labels = raw6465step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6465step1 raw6465step1Labels permutation10 permutation2
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw6466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6466 raw6466Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw6466 raw6466Labels = mixedMoment B raw6466step0 raw6466step0Labels := by
      have hz : ∀ j, raw6466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6466step0 = (fun i j => raw6466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6466step0 raw6466; decide +kernel
      have hl : raw6466step0Labels = raw6466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6466 raw6466Labels permutation346 hz
    mixedMoment B raw6466step0 raw6466step0Labels = mixedMoment B raw6466step1 raw6466step1Labels := by
      have ha : raw6466step1 = (fun i j => raw6466step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6466step1 raw6466step0; decide +kernel
      have hl : raw6466step1Labels = raw6466step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6466step0 raw6466step0Labels permutation38 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw6467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6467step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6467 raw6467Labels = mixedMoment B node4563 node4563Labels := by
  calc
    mixedMoment B raw6467 raw6467Labels = mixedMoment B raw6467step0 raw6467step0Labels := by
      have ha : raw6467step0 = (fun i j => raw6467 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6467step0 raw6467; decide +kernel
      have hl : raw6467step0Labels = raw6467Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6467 raw6467Labels permutation200 permutation3
    mixedMoment B raw6467step0 raw6467step0Labels = mixedMoment B raw6467step1 raw6467step1Labels := by
      have ha : raw6467step1 = raw6467step0 := by apply Matrix.ext; unfold raw6467step1 raw6467step0; decide +kernel
      have hl : raw6467step0Labels = labelEmbedding6 ∘ raw6467step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6467step0 raw6467step0Labels raw6467step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4563 node4563Labels := by rfl

def raw6468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6468 raw6468Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw6468 raw6468Labels = mixedMoment B raw6468step0 raw6468step0Labels := by
      have ha : raw6468step0 = (fun i j => raw6468 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6468step0 raw6468; decide +kernel
      have hl : raw6468step0Labels = raw6468Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6468 raw6468Labels permutation158 permutation2
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw6469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6469 raw6469Labels = mixedMoment B node5208 node5208Labels := by
  calc
    mixedMoment B raw6469 raw6469Labels = mixedMoment B raw6469step0 raw6469step0Labels := by
      have ha : raw6469step0 = (fun i j => raw6469 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6469step0 raw6469; decide +kernel
      have hl : raw6469step0Labels = raw6469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6469 raw6469Labels permutation200 permutation2
    _ = mixedMoment B node5208 node5208Labels := by rfl

def raw6470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6470 raw6470Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw6470 raw6470Labels = mixedMoment B raw6470step0 raw6470step0Labels := by
      have hz : ∀ j, raw6470 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6470step0 = (fun i j => raw6470 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6470step0 raw6470; decide +kernel
      have hl : raw6470step0Labels = raw6470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6470 raw6470Labels permutation520 hz
    mixedMoment B raw6470step0 raw6470step0Labels = mixedMoment B raw6470step1 raw6470step1Labels := by
      have ha : raw6470step1 = (fun i j => raw6470step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6470step1 raw6470step0; decide +kernel
      have hl : raw6470step1Labels = raw6470step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6470step0 raw6470step0Labels permutation34 permutation2
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw6471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6471 raw6471Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw6471 raw6471Labels = mixedMoment B raw6471step0 raw6471step0Labels := by
      have ha : raw6471step0 = (fun i j => raw6471 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6471step0 raw6471; decide +kernel
      have hl : raw6471step0Labels = raw6471Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6471 raw6471Labels permutation158 permutation2
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw6472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6472 raw6472Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw6472 raw6472Labels = mixedMoment B raw6472step0 raw6472step0Labels := by
      have hz : ∀ j, raw6472 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6472step0 = (fun i j => raw6472 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6472step0 raw6472; decide +kernel
      have hl : raw6472step0Labels = raw6472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6472 raw6472Labels permutation346 hz
    mixedMoment B raw6472step0 raw6472step0Labels = mixedMoment B raw6472step1 raw6472step1Labels := by
      have ha : raw6472step1 = (fun i j => raw6472step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6472step1 raw6472step0; decide +kernel
      have hl : raw6472step1Labels = raw6472step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6472step0 raw6472step0Labels permutation34 permutation2
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw6473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6473 raw6473Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw6473 raw6473Labels = mixedMoment B raw6473step0 raw6473step0Labels := by
      have hz : ∀ j, raw6473 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6473step0 = (fun i j => raw6473 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6473step0 raw6473; decide +kernel
      have hl : raw6473step0Labels = raw6473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6473 raw6473Labels permutation346 hz
    mixedMoment B raw6473step0 raw6473step0Labels = mixedMoment B raw6473step1 raw6473step1Labels := by
      have ha : raw6473step1 = (fun i j => raw6473step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6473step1 raw6473step0; decide +kernel
      have hl : raw6473step1Labels = raw6473step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6473step0 raw6473step0Labels permutation34 permutation2
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw6474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6474 raw6474Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw6474 raw6474Labels = mixedMoment B raw6474step0 raw6474step0Labels := by
      have ha : raw6474step0 = (fun i j => raw6474 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6474step0 raw6474; decide +kernel
      have hl : raw6474step0Labels = raw6474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6474 raw6474Labels permutation178 permutation2
    _ = mixedMoment B node5135 node5135Labels := by rfl

def raw6475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6475 raw6475Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw6475 raw6475Labels = mixedMoment B raw6475step0 raw6475step0Labels := by
      have hz : ∀ j, raw6475 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6475step0 = (fun i j => raw6475 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6475step0 raw6475; decide +kernel
      have hl : raw6475step0Labels = raw6475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6475 raw6475Labels permutation520 hz
    mixedMoment B raw6475step0 raw6475step0Labels = mixedMoment B raw6475step1 raw6475step1Labels := by
      have hz : ∀ j, raw6475step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6475step1 = (fun i j => raw6475step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6475step1 raw6475step0; decide +kernel
      have hl : raw6475step1Labels = raw6475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6475step0 raw6475step0Labels permutation80 hz
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw6476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6476 raw6476Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw6476 raw6476Labels = mixedMoment B raw6476step0 raw6476step0Labels := by
      have hz : ∀ j, raw6476 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6476step0 = (fun i j => raw6476 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6476step0 raw6476; decide +kernel
      have hl : raw6476step0Labels = raw6476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6476 raw6476Labels permutation346 hz
    mixedMoment B raw6476step0 raw6476step0Labels = mixedMoment B raw6476step1 raw6476step1Labels := by
      have ha : raw6476step1 = (fun i j => raw6476step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6476step1 raw6476step0; decide +kernel
      have hl : raw6476step1Labels = raw6476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6476step0 raw6476step0Labels permutation35 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw6477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6477step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6477step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6477 raw6477Labels = mixedMoment B node4565 node4565Labels := by
  calc
    mixedMoment B raw6477 raw6477Labels = mixedMoment B raw6477step0 raw6477step0Labels := by
      have hz : ∀ j, raw6477 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6477step0 = (fun i j => raw6477 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6477step0 raw6477; decide +kernel
      have hl : raw6477step0Labels = raw6477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6477 raw6477Labels permutation346 hz
    mixedMoment B raw6477step0 raw6477step0Labels = mixedMoment B raw6477step1 raw6477step1Labels := by
      have ha : raw6477step1 = (fun i j => raw6477step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6477step1 raw6477step0; decide +kernel
      have hl : raw6477step1Labels = raw6477step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6477step0 raw6477step0Labels permutation39 permutation3
    mixedMoment B raw6477step1 raw6477step1Labels = mixedMoment B raw6477step2 raw6477step2Labels := by
      have ha : raw6477step2 = raw6477step1 := by apply Matrix.ext; unfold raw6477step2 raw6477step1; decide +kernel
      have hl : raw6477step1Labels = labelEmbedding6 ∘ raw6477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6477step1 raw6477step1Labels raw6477step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4565 node4565Labels := by rfl

def raw6478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6478 raw6478Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw6478 raw6478Labels = mixedMoment B raw6478step0 raw6478step0Labels := by
      have hz : ∀ j, raw6478 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6478step0 = (fun i j => raw6478 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6478step0 raw6478; decide +kernel
      have hl : raw6478step0Labels = raw6478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6478 raw6478Labels permutation346 hz
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw6479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6479 raw6479Labels = mixedMoment B node5131 node5131Labels := by
  calc
    mixedMoment B raw6479 raw6479Labels = mixedMoment B raw6479step0 raw6479step0Labels := by
      have ha : raw6479step0 = (fun i j => raw6479 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6479step0 raw6479; decide +kernel
      have hl : raw6479step0Labels = raw6479Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6479 raw6479Labels permutation176 permutation2
    _ = mixedMoment B node5131 node5131Labels := by rfl

def raw6480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6480step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw6480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6480 raw6480Labels = mixedMoment B node5210 node5210Labels := by
  calc
    mixedMoment B raw6480 raw6480Labels = mixedMoment B raw6480step0 raw6480step0Labels := by
      have hz : ∀ j, raw6480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6480step0 = (fun i j => raw6480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6480step0 raw6480; decide +kernel
      have hl : raw6480step0Labels = raw6480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6480 raw6480Labels permutation346 hz
    mixedMoment B raw6480step0 raw6480step0Labels = mixedMoment B raw6480step1 raw6480step1Labels := by
      have ha : raw6480step1 = (fun i j => raw6480step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6480step1 raw6480step0; decide +kernel
      have hl : raw6480step1Labels = raw6480step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6480step0 raw6480step0Labels permutation38 permutation2
    _ = mixedMoment B node5210 node5210Labels := by rfl

def raw6481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6481 raw6481Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw6481 raw6481Labels = mixedMoment B raw6481step0 raw6481step0Labels := by
      have hz : ∀ j, raw6481 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6481step0 = (fun i j => raw6481 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6481step0 raw6481; decide +kernel
      have hl : raw6481step0Labels = raw6481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6481 raw6481Labels permutation346 hz
    mixedMoment B raw6481step0 raw6481step0Labels = mixedMoment B raw6481step1 raw6481step1Labels := by
      have ha : raw6481step1 = (fun i j => raw6481step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6481step1 raw6481step0; decide +kernel
      have hl : raw6481step1Labels = raw6481step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6481step0 raw6481step0Labels permutation33 permutation2
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw6482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw6482step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6482step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw6482step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6482 raw6482Labels = mixedMoment B node4564 node4564Labels := by
  calc
    mixedMoment B raw6482 raw6482Labels = mixedMoment B raw6482step0 raw6482step0Labels := by
      have hz : ∀ j, raw6482 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6482step0 = (fun i j => raw6482 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6482step0 raw6482; decide +kernel
      have hl : raw6482step0Labels = raw6482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6482 raw6482Labels permutation346 hz
    mixedMoment B raw6482step0 raw6482step0Labels = mixedMoment B raw6482step1 raw6482step1Labels := by
      have ha : raw6482step1 = (fun i j => raw6482step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6482step1 raw6482step0; decide +kernel
      have hl : raw6482step1Labels = raw6482step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6482step0 raw6482step0Labels permutation38 permutation3
    mixedMoment B raw6482step1 raw6482step1Labels = mixedMoment B raw6482step2 raw6482step2Labels := by
      have ha : raw6482step2 = raw6482step1 := by apply Matrix.ext; unfold raw6482step2 raw6482step1; decide +kernel
      have hl : raw6482step1Labels = labelEmbedding6 ∘ raw6482step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6482step1 raw6482step1Labels raw6482step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4564 node4564Labels := by rfl

def raw6483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6483 raw6483Labels = mixedMoment B node5087 node5087Labels := by
  calc
    mixedMoment B raw6483 raw6483Labels = mixedMoment B raw6483step0 raw6483step0Labels := by
      have hz : ∀ j, raw6483 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6483step0 = (fun i j => raw6483 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6483step0 raw6483; decide +kernel
      have hl : raw6483step0Labels = raw6483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6483 raw6483Labels permutation346 hz
    _ = mixedMoment B node5087 node5087Labels := by rfl

def raw6484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw6484step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6484step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6484step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6484 raw6484Labels = mixedMoment B node5052 node5052Labels := by
  calc
    mixedMoment B raw6484 raw6484Labels = mixedMoment B raw6484step0 raw6484step0Labels := by
      have ha : raw6484step0 = (fun i j => raw6484 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6484step0 raw6484; decide +kernel
      have hl : raw6484step0Labels = raw6484Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6484 raw6484Labels permutation676 permutation3
    mixedMoment B raw6484step0 raw6484step0Labels = mixedMoment B raw6484step1 raw6484step1Labels := by
      have ha : raw6484step1 = -raw6484step0 := by apply Matrix.ext; change ∀ i j, raw6484step1 i j = -(raw6484step0 i j); unfold raw6484step1 raw6484step0; decide +kernel
      have hl : raw6484step1Labels = raw6484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6484step1 raw6484step1Labels = mixedMoment B raw6484step2 raw6484step2Labels := by
      have ha : raw6484step2 = raw6484step1 := by apply Matrix.ext; unfold raw6484step2 raw6484step1; decide +kernel
      have hl : raw6484step1Labels = labelEmbedding6 ∘ raw6484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6484step1 raw6484step1Labels raw6484step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5052 node5052Labels := by rfl

def raw6485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw6485step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6485step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6485step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6485step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6485 raw6485Labels = mixedMoment B node5062 node5062Labels := by
  calc
    mixedMoment B raw6485 raw6485Labels = mixedMoment B raw6485step0 raw6485step0Labels := by
      have hz : ∀ j, raw6485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6485step0 = (fun i j => raw6485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6485step0 raw6485; decide +kernel
      have hl : raw6485step0Labels = raw6485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6485 raw6485Labels permutation346 hz
    mixedMoment B raw6485step0 raw6485step0Labels = mixedMoment B raw6485step1 raw6485step1Labels := by
      have ha : raw6485step1 = (fun i j => raw6485step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6485step1 raw6485step0; decide +kernel
      have hl : raw6485step1Labels = raw6485step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6485step0 raw6485step0Labels permutation149 permutation3
    mixedMoment B raw6485step1 raw6485step1Labels = mixedMoment B raw6485step2 raw6485step2Labels := by
      have ha : raw6485step2 = -raw6485step1 := by apply Matrix.ext; change ∀ i j, raw6485step2 i j = -(raw6485step1 i j); unfold raw6485step2 raw6485step1; decide +kernel
      have hl : raw6485step2Labels = raw6485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6485step2 raw6485step2Labels = mixedMoment B raw6485step3 raw6485step3Labels := by
      have ha : raw6485step3 = raw6485step2 := by apply Matrix.ext; unfold raw6485step3 raw6485step2; decide +kernel
      have hl : raw6485step2Labels = labelEmbedding6 ∘ raw6485step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6485step2 raw6485step2Labels raw6485step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5062 node5062Labels := by rfl

def raw6486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw6486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw6486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw6486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6486 raw6486Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw6486 raw6486Labels = mixedMoment B raw6486step0 raw6486step0Labels := by
      have hz : ∀ j, raw6486 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6486step0 = (fun i j => raw6486 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6486step0 raw6486; decide +kernel
      have hl : raw6486step0Labels = raw6486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6486 raw6486Labels permutation520 hz
    mixedMoment B raw6486step0 raw6486step0Labels = mixedMoment B raw6486step1 raw6486step1Labels := by
      have hz : ∀ j, raw6486step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6486step1 = (fun i j => raw6486step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6486step1 raw6486step0; decide +kernel
      have hl : raw6486step1Labels = raw6486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6486step0 raw6486step0Labels permutation80 hz
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw6487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6487Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6487step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw6487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6487 raw6487Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw6487 raw6487Labels = mixedMoment B raw6487step0 raw6487step0Labels := by
      have hz : ∀ j, raw6487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6487step0 = (fun i j => raw6487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6487step0 raw6487; decide +kernel
      have hl : raw6487step0Labels = raw6487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6487 raw6487Labels permutation346 hz
    mixedMoment B raw6487step0 raw6487step0Labels = mixedMoment B raw6487step1 raw6487step1Labels := by
      have ha : raw6487step1 = (fun i j => raw6487step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6487step1 raw6487step0; decide +kernel
      have hl : raw6487step1Labels = raw6487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6487step0 raw6487step0Labels permutation103 permutation6
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw6488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6488Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6488 raw6488Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw6488 raw6488Labels = mixedMoment B raw6488step0 raw6488step0Labels := by
      have ha : raw6488step0 = (fun i j => raw6488 (permutation513 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6488step0 raw6488; decide +kernel
      have hl : raw6488step0Labels = raw6488Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6488 raw6488Labels permutation513 permutation6
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw6489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6489Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6489step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6489 raw6489Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw6489 raw6489Labels = mixedMoment B raw6489step0 raw6489step0Labels := by
      have hz : ∀ j, raw6489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6489step0 = (fun i j => raw6489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6489step0 raw6489; decide +kernel
      have hl : raw6489step0Labels = raw6489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6489 raw6489Labels permutation346 hz
    mixedMoment B raw6489step0 raw6489step0Labels = mixedMoment B raw6489step1 raw6489step1Labels := by
      have ha : raw6489step1 = (fun i j => raw6489step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6489step1 raw6489step0; decide +kernel
      have hl : raw6489step1Labels = raw6489step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6489step0 raw6489step0Labels permutation103 permutation6
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw6490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6490Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6490step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6490step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6490step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6490step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6490 raw6490Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw6490 raw6490Labels = mixedMoment B raw6490step0 raw6490step0Labels := by
      have hz : ∀ j, raw6490 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6490step0 = (fun i j => raw6490 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6490step0 raw6490; decide +kernel
      have hl : raw6490step0Labels = raw6490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6490 raw6490Labels permutation520 hz
    mixedMoment B raw6490step0 raw6490step0Labels = mixedMoment B raw6490step1 raw6490step1Labels := by
      have hz : ∀ j, raw6490step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6490step1 = (fun i j => raw6490step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6490step1 raw6490step0; decide +kernel
      have hl : raw6490step1Labels = raw6490step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6490step0 raw6490step0Labels permutation80 hz
    mixedMoment B raw6490step1 raw6490step1Labels = mixedMoment B raw6490step2 raw6490step2Labels := by
      have ha : raw6490step2 = (fun i j => raw6490step1 (permutation25 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6490step2 raw6490step1; decide +kernel
      have hl : raw6490step2Labels = raw6490step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6490step1 raw6490step1Labels permutation25 permutation6
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw6491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6491Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6491step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6491 raw6491Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw6491 raw6491Labels = mixedMoment B raw6491step0 raw6491step0Labels := by
      have hz : ∀ j, raw6491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6491step0 = (fun i j => raw6491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6491step0 raw6491; decide +kernel
      have hl : raw6491step0Labels = raw6491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6491 raw6491Labels permutation346 hz
    mixedMoment B raw6491step0 raw6491step0Labels = mixedMoment B raw6491step1 raw6491step1Labels := by
      have ha : raw6491step1 = (fun i j => raw6491step0 (permutation103 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6491step1 raw6491step0; decide +kernel
      have hl : raw6491step1Labels = raw6491step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6491step0 raw6491step0Labels permutation103 permutation6
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw6492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6492Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6492step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6492 raw6492Labels = mixedMoment B node1189 node1189Labels := by
  calc
    mixedMoment B raw6492 raw6492Labels = mixedMoment B raw6492step0 raw6492step0Labels := by
      have hz : ∀ j, raw6492 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6492step0 = (fun i j => raw6492 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6492step0 raw6492; decide +kernel
      have hl : raw6492step0Labels = raw6492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6492 raw6492Labels permutation346 hz
    mixedMoment B raw6492step0 raw6492step0Labels = mixedMoment B raw6492step1 raw6492step1Labels := by
      have ha : raw6492step1 = (fun i j => raw6492step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6492step1 raw6492step0; decide +kernel
      have hl : raw6492step1Labels = raw6492step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6492step0 raw6492step0Labels permutation40 permutation3
    _ = mixedMoment B node1189 node1189Labels := by rfl

def raw6493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6493Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6493 raw6493Labels = mixedMoment B node2909 node2909Labels := by
  calc
    mixedMoment B raw6493 raw6493Labels = mixedMoment B raw6493step0 raw6493step0Labels := by
      have ha : raw6493step0 = (fun i j => raw6493 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6493step0 raw6493; decide +kernel
      have hl : raw6493step0Labels = raw6493Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6493 raw6493Labels permutation184 permutation3
    _ = mixedMoment B node2909 node2909Labels := by rfl

def raw6494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6494step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6494 raw6494Labels = mixedMoment B node2841 node2841Labels := by
  calc
    mixedMoment B raw6494 raw6494Labels = mixedMoment B raw6494step0 raw6494step0Labels := by
      have hz : ∀ j, raw6494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6494step0 = (fun i j => raw6494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6494step0 raw6494; decide +kernel
      have hl : raw6494step0Labels = raw6494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6494 raw6494Labels permutation346 hz
    mixedMoment B raw6494step0 raw6494step0Labels = mixedMoment B raw6494step1 raw6494step1Labels := by
      have ha : raw6494step1 = (fun i j => raw6494step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6494step1 raw6494step0; decide +kernel
      have hl : raw6494step1Labels = raw6494step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6494step0 raw6494step0Labels permutation40 permutation3
    _ = mixedMoment B node2841 node2841Labels := by rfl

def raw6495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6495step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6495step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6495step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw6495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6495 raw6495Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw6495 raw6495Labels = mixedMoment B raw6495step0 raw6495step0Labels := by
      have hz : ∀ j, raw6495 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6495step0 = (fun i j => raw6495 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6495step0 raw6495; decide +kernel
      have hl : raw6495step0Labels = raw6495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6495 raw6495Labels permutation520 hz
    mixedMoment B raw6495step0 raw6495step0Labels = mixedMoment B raw6495step1 raw6495step1Labels := by
      have hz : ∀ j, raw6495step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6495step1 = (fun i j => raw6495step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6495step1 raw6495step0; decide +kernel
      have hl : raw6495step1Labels = raw6495step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6495step0 raw6495step0Labels permutation80 hz
    mixedMoment B raw6495step1 raw6495step1Labels = mixedMoment B raw6495step2 raw6495step2Labels := by
      have ha : raw6495step2 = (fun i j => raw6495step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6495step2 raw6495step1; decide +kernel
      have hl : raw6495step2Labels = raw6495step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6495step1 raw6495step1Labels permutation10 permutation3
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw6496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6496step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6496step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6496 raw6496Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw6496 raw6496Labels = mixedMoment B raw6496step0 raw6496step0Labels := by
      have hz : ∀ j, raw6496 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6496step0 = (fun i j => raw6496 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6496step0 raw6496; decide +kernel
      have hl : raw6496step0Labels = raw6496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6496 raw6496Labels permutation346 hz
    mixedMoment B raw6496step0 raw6496step0Labels = mixedMoment B raw6496step1 raw6496step1Labels := by
      have ha : raw6496step1 = (fun i j => raw6496step0 (permutation43 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6496step1 raw6496step0; decide +kernel
      have hl : raw6496step1Labels = raw6496step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6496step0 raw6496step0Labels permutation43 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw6497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6497 raw6497Labels = mixedMoment B node1180 node1180Labels := by
  calc
    mixedMoment B raw6497 raw6497Labels = mixedMoment B raw6497step0 raw6497step0Labels := by
      have ha : raw6497step0 = (fun i j => raw6497 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6497step0 raw6497; decide +kernel
      have hl : raw6497step0Labels = raw6497Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6497 raw6497Labels permutation200 permutation3
    _ = mixedMoment B node1180 node1180Labels := by rfl

def raw6498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6498 raw6498Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw6498 raw6498Labels = mixedMoment B raw6498step0 raw6498step0Labels := by
      have ha : raw6498step0 = (fun i j => raw6498 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6498step0 raw6498; decide +kernel
      have hl : raw6498step0Labels = raw6498Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6498 raw6498Labels permutation158 permutation3
    _ = mixedMoment B node2976 node2976Labels := by rfl

def raw6499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6499 raw6499Labels = mixedMoment B node2834 node2834Labels := by
  calc
    mixedMoment B raw6499 raw6499Labels = mixedMoment B raw6499step0 raw6499step0Labels := by
      have ha : raw6499step0 = (fun i j => raw6499 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6499step0 raw6499; decide +kernel
      have hl : raw6499step0Labels = raw6499Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6499 raw6499Labels permutation200 permutation3
    _ = mixedMoment B node2834 node2834Labels := by rfl

def raw6500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6500 raw6500Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw6500 raw6500Labels = mixedMoment B raw6500step0 raw6500step0Labels := by
      have hz : ∀ j, raw6500 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6500step0 = (fun i j => raw6500 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6500step0 raw6500; decide +kernel
      have hl : raw6500step0Labels = raw6500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6500 raw6500Labels permutation520 hz
    mixedMoment B raw6500step0 raw6500step0Labels = mixedMoment B raw6500step1 raw6500step1Labels := by
      have ha : raw6500step1 = (fun i j => raw6500step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6500step1 raw6500step0; decide +kernel
      have hl : raw6500step1Labels = raw6500step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6500step0 raw6500step0Labels permutation44 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw6501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw6501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6501 raw6501Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw6501 raw6501Labels = mixedMoment B raw6501step0 raw6501step0Labels := by
      have ha : raw6501step0 = (fun i j => raw6501 (permutation204 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6501step0 raw6501; decide +kernel
      have hl : raw6501step0Labels = raw6501Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6501 raw6501Labels permutation204 permutation3
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw6502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6502step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6502 raw6502Labels = mixedMoment B node1262 node1262Labels := by
  calc
    mixedMoment B raw6502 raw6502Labels = mixedMoment B raw6502step0 raw6502step0Labels := by
      have hz : ∀ j, raw6502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6502step0 = (fun i j => raw6502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6502step0 raw6502; decide +kernel
      have hl : raw6502step0Labels = raw6502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6502 raw6502Labels permutation346 hz
    mixedMoment B raw6502step0 raw6502step0Labels = mixedMoment B raw6502step1 raw6502step1Labels := by
      have ha : raw6502step1 = (fun i j => raw6502step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6502step1 raw6502step0; decide +kernel
      have hl : raw6502step1Labels = raw6502step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6502step0 raw6502step0Labels permutation32 permutation3
    _ = mixedMoment B node1262 node1262Labels := by rfl

def raw6503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6503step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6503step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6503 raw6503Labels = mixedMoment B node2998 node2998Labels := by
  calc
    mixedMoment B raw6503 raw6503Labels = mixedMoment B raw6503step0 raw6503step0Labels := by
      have hz : ∀ j, raw6503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6503step0 = (fun i j => raw6503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6503step0 raw6503; decide +kernel
      have hl : raw6503step0Labels = raw6503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6503 raw6503Labels permutation346 hz
    mixedMoment B raw6503step0 raw6503step0Labels = mixedMoment B raw6503step1 raw6503step1Labels := by
      have ha : raw6503step1 = (fun i j => raw6503step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6503step1 raw6503step0; decide +kernel
      have hl : raw6503step1Labels = raw6503step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6503step0 raw6503step0Labels permutation32 permutation3
    _ = mixedMoment B node2998 node2998Labels := by rfl

def raw6504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6504 raw6504Labels = mixedMoment B node2934 node2934Labels := by
  calc
    mixedMoment B raw6504 raw6504Labels = mixedMoment B raw6504step0 raw6504step0Labels := by
      have ha : raw6504step0 = (fun i j => raw6504 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6504step0 raw6504; decide +kernel
      have hl : raw6504step0Labels = raw6504Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6504 raw6504Labels permutation176 permutation3
    _ = mixedMoment B node2934 node2934Labels := by rfl

def raw6505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6505step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6505step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6505 raw6505Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw6505 raw6505Labels = mixedMoment B raw6505step0 raw6505step0Labels := by
      have hz : ∀ j, raw6505 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6505step0 = (fun i j => raw6505 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6505step0 raw6505; decide +kernel
      have hl : raw6505step0Labels = raw6505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6505 raw6505Labels permutation520 hz
    mixedMoment B raw6505step0 raw6505step0Labels = mixedMoment B raw6505step1 raw6505step1Labels := by
      have hz : ∀ j, raw6505step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6505step1 = (fun i j => raw6505step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6505step1 raw6505step0; decide +kernel
      have hl : raw6505step1Labels = raw6505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6505step0 raw6505step0Labels permutation80 hz
    mixedMoment B raw6505step1 raw6505step1Labels = mixedMoment B raw6505step2 raw6505step2Labels := by
      have ha : raw6505step2 = (fun i j => raw6505step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6505step2 raw6505step1; decide +kernel
      have hl : raw6505step2Labels = raw6505step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6505step1 raw6505step1Labels permutation8 permutation3
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw6506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6506step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6506step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6506 raw6506Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw6506 raw6506Labels = mixedMoment B raw6506step0 raw6506step0Labels := by
      have hz : ∀ j, raw6506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6506step0 = (fun i j => raw6506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6506step0 raw6506; decide +kernel
      have hl : raw6506step0Labels = raw6506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6506 raw6506Labels permutation346 hz
    mixedMoment B raw6506step0 raw6506step0Labels = mixedMoment B raw6506step1 raw6506step1Labels := by
      have ha : raw6506step1 = (fun i j => raw6506step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6506step1 raw6506step0; decide +kernel
      have hl : raw6506step1Labels = raw6506step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6506step0 raw6506step0Labels permutation33 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw6507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6507step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6507 raw6507Labels = mixedMoment B node1182 node1182Labels := by
  calc
    mixedMoment B raw6507 raw6507Labels = mixedMoment B raw6507step0 raw6507step0Labels := by
      have hz : ∀ j, raw6507 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6507step0 = (fun i j => raw6507 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6507step0 raw6507; decide +kernel
      have hl : raw6507step0Labels = raw6507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6507 raw6507Labels permutation346 hz
    mixedMoment B raw6507step0 raw6507step0Labels = mixedMoment B raw6507step1 raw6507step1Labels := by
      have ha : raw6507step1 = (fun i j => raw6507step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6507step1 raw6507step0; decide +kernel
      have hl : raw6507step1Labels = raw6507step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6507step0 raw6507step0Labels permutation39 permutation3
    _ = mixedMoment B node1182 node1182Labels := by rfl

def raw6508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6508step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw6508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6508 raw6508Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw6508 raw6508Labels = mixedMoment B raw6508step0 raw6508step0Labels := by
      have hz : ∀ j, raw6508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6508step0 = (fun i j => raw6508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6508step0 raw6508; decide +kernel
      have hl : raw6508step0Labels = raw6508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6508 raw6508Labels permutation346 hz
    mixedMoment B raw6508step0 raw6508step0Labels = mixedMoment B raw6508step1 raw6508step1Labels := by
      have ha : raw6508step1 = (fun i j => raw6508step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6508step1 raw6508step0; decide +kernel
      have hl : raw6508step1Labels = raw6508step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6508step0 raw6508step0Labels permutation33 permutation3
    _ = mixedMoment B node2979 node2979Labels := by rfl

def raw6509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6509 raw6509Labels = mixedMoment B node2905 node2905Labels := by
  calc
    mixedMoment B raw6509 raw6509Labels = mixedMoment B raw6509step0 raw6509step0Labels := by
      have ha : raw6509step0 = (fun i j => raw6509 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6509step0 raw6509; decide +kernel
      have hl : raw6509step0Labels = raw6509Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6509 raw6509Labels permutation183 permutation3
    _ = mixedMoment B node2905 node2905Labels := by rfl

def raw6510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6510step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6510 raw6510Labels = mixedMoment B node2835 node2835Labels := by
  calc
    mixedMoment B raw6510 raw6510Labels = mixedMoment B raw6510step0 raw6510step0Labels := by
      have hz : ∀ j, raw6510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6510step0 = (fun i j => raw6510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6510step0 raw6510; decide +kernel
      have hl : raw6510step0Labels = raw6510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6510 raw6510Labels permutation346 hz
    mixedMoment B raw6510step0 raw6510step0Labels = mixedMoment B raw6510step1 raw6510step1Labels := by
      have ha : raw6510step1 = (fun i j => raw6510step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6510step1 raw6510step0; decide +kernel
      have hl : raw6510step1Labels = raw6510step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6510step0 raw6510step0Labels permutation39 permutation3
    _ = mixedMoment B node2835 node2835Labels := by rfl

def raw6511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6511 raw6511Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw6511 raw6511Labels = mixedMoment B raw6511step0 raw6511step0Labels := by
      have hz : ∀ j, raw6511 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6511step0 = (fun i j => raw6511 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6511step0 raw6511; decide +kernel
      have hl : raw6511step0Labels = raw6511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6511 raw6511Labels permutation346 hz
    mixedMoment B raw6511step0 raw6511step0Labels = mixedMoment B raw6511step1 raw6511step1Labels := by
      have ha : raw6511step1 = (fun i j => raw6511step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6511step1 raw6511step0; decide +kernel
      have hl : raw6511step1Labels = raw6511step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6511step0 raw6511step0Labels permutation39 permutation3
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw6512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6512step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6512step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6512step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw6512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6512 raw6512Labels = mixedMoment B node1181 node1181Labels := by
  calc
    mixedMoment B raw6512 raw6512Labels = mixedMoment B raw6512step0 raw6512step0Labels := by
      have hz : ∀ j, raw6512 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6512step0 = (fun i j => raw6512 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6512step0 raw6512; decide +kernel
      have hl : raw6512step0Labels = raw6512Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6512 raw6512Labels permutation346 hz
    mixedMoment B raw6512step0 raw6512step0Labels = mixedMoment B raw6512step1 raw6512step1Labels := by
      have ha : raw6512step1 = (fun i j => raw6512step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6512step1 raw6512step0; decide +kernel
      have hl : raw6512step1Labels = raw6512step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6512step0 raw6512step0Labels permutation38 permutation3
    _ = mixedMoment B node1181 node1181Labels := by rfl

def raw6513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6513step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6513 raw6513Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw6513 raw6513Labels = mixedMoment B raw6513step0 raw6513step0Labels := by
      have hz : ∀ j, raw6513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6513step0 = (fun i j => raw6513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6513step0 raw6513; decide +kernel
      have hl : raw6513step0Labels = raw6513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6513 raw6513Labels permutation346 hz
    mixedMoment B raw6513step0 raw6513step0Labels = mixedMoment B raw6513step1 raw6513step1Labels := by
      have ha : raw6513step1 = (fun i j => raw6513step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6513step1 raw6513step0; decide +kernel
      have hl : raw6513step1Labels = raw6513step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6513step0 raw6513step0Labels permutation151 permutation3
    mixedMoment B raw6513step1 raw6513step1Labels = mixedMoment B raw6513step2 raw6513step2Labels := by
      have ha : raw6513step2 = -raw6513step1 := by apply Matrix.ext; change ∀ i j, raw6513step2 i j = -(raw6513step1 i j); unfold raw6513step2 raw6513step1; decide +kernel
      have hl : raw6513step2Labels = raw6513step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2495 node2495Labels := by rfl

def raw6514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw6514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6514 raw6514Labels = mixedMoment B node2454 node2454Labels := by
  calc
    mixedMoment B raw6514 raw6514Labels = mixedMoment B raw6514step0 raw6514step0Labels := by
      have ha : raw6514step0 = (fun i j => raw6514 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6514step0 raw6514; decide +kernel
      have hl : raw6514step0Labels = raw6514Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6514 raw6514Labels permutation676 permutation3
    mixedMoment B raw6514step0 raw6514step0Labels = mixedMoment B raw6514step1 raw6514step1Labels := by
      have ha : raw6514step1 = -raw6514step0 := by apply Matrix.ext; change ∀ i j, raw6514step1 i j = -(raw6514step0 i j); unfold raw6514step1 raw6514step0; decide +kernel
      have hl : raw6514step1Labels = raw6514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2454 node2454Labels := by rfl

def raw6515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6515step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw6515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6515 raw6515Labels = mixedMoment B node2465 node2465Labels := by
  calc
    mixedMoment B raw6515 raw6515Labels = mixedMoment B raw6515step0 raw6515step0Labels := by
      have hz : ∀ j, raw6515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6515step0 = (fun i j => raw6515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6515step0 raw6515; decide +kernel
      have hl : raw6515step0Labels = raw6515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6515 raw6515Labels permutation346 hz
    mixedMoment B raw6515step0 raw6515step0Labels = mixedMoment B raw6515step1 raw6515step1Labels := by
      have ha : raw6515step1 = (fun i j => raw6515step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6515step1 raw6515step0; decide +kernel
      have hl : raw6515step1Labels = raw6515step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6515step0 raw6515step0Labels permutation149 permutation3
    mixedMoment B raw6515step1 raw6515step1Labels = mixedMoment B raw6515step2 raw6515step2Labels := by
      have ha : raw6515step2 = -raw6515step1 := by apply Matrix.ext; change ∀ i j, raw6515step2 i j = -(raw6515step1 i j); unfold raw6515step2 raw6515step1; decide +kernel
      have hl : raw6515step2Labels = raw6515step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2465 node2465Labels := by rfl

def raw6516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw6516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw6516step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw6516step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw6516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6516step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw6516step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6516 raw6516Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw6516 raw6516Labels = mixedMoment B raw6516step0 raw6516step0Labels := by
      have hz : ∀ j, raw6516 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6516step0 = (fun i j => raw6516 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6516step0 raw6516; decide +kernel
      have hl : raw6516step0Labels = raw6516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6516 raw6516Labels permutation520 hz
    mixedMoment B raw6516step0 raw6516step0Labels = mixedMoment B raw6516step1 raw6516step1Labels := by
      have hz : ∀ j, raw6516step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6516step1 = (fun i j => raw6516step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6516step1 raw6516step0; decide +kernel
      have hl : raw6516step1Labels = raw6516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6516step0 raw6516step0Labels permutation80 hz
    mixedMoment B raw6516step1 raw6516step1Labels = mixedMoment B raw6516step2 raw6516step2Labels := by
      have ha : raw6516step2 = (fun i j => raw6516step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6516step2 raw6516step1; decide +kernel
      have hl : raw6516step2Labels = raw6516step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6516step1 raw6516step1Labels permutation29 permutation3
    mixedMoment B raw6516step2 raw6516step2Labels = mixedMoment B raw6516step3 raw6516step3Labels := by
      have ha : raw6516step3 = -raw6516step2 := by apply Matrix.ext; change ∀ i j, raw6516step3 i j = -(raw6516step2 i j); unfold raw6516step3 raw6516step2; decide +kernel
      have hl : raw6516step3Labels = raw6516step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw6517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6517step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6517step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6517step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6517 raw6517Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw6517 raw6517Labels = mixedMoment B raw6517step0 raw6517step0Labels := by
      have hz : ∀ j, raw6517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6517step0 = (fun i j => raw6517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6517step0 raw6517; decide +kernel
      have hl : raw6517step0Labels = raw6517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6517 raw6517Labels permutation346 hz
    mixedMoment B raw6517step0 raw6517step0Labels = mixedMoment B raw6517step1 raw6517step1Labels := by
      have ha : raw6517step1 = (fun i j => raw6517step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6517step1 raw6517step0; decide +kernel
      have hl : raw6517step1Labels = raw6517step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6517step0 raw6517step0Labels permutation35 permutation7
    mixedMoment B raw6517step1 raw6517step1Labels = mixedMoment B raw6517step2 raw6517step2Labels := by
      have ha : raw6517step2 = -raw6517step1 := by apply Matrix.ext; change ∀ i j, raw6517step2 i j = -(raw6517step1 i j); unfold raw6517step2 raw6517step1; decide +kernel
      have hl : raw6517step2Labels = raw6517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6517step2 raw6517step2Labels = mixedMoment B raw6517step3 raw6517step3Labels := by
      have ha : raw6517step3 = raw6517step2 := by apply Matrix.ext; unfold raw6517step3 raw6517step2; decide +kernel
      have hl : raw6517step2Labels = labelEmbedding1 ∘ raw6517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6517step2 raw6517step2Labels raw6517step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw6518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6518Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6518step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6518step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6518step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6518step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6518 raw6518Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw6518 raw6518Labels = mixedMoment B raw6518step0 raw6518step0Labels := by
      have ha : raw6518step0 = (fun i j => raw6518 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6518step0 raw6518; decide +kernel
      have hl : raw6518step0Labels = raw6518Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6518 raw6518Labels permutation155 permutation7
    mixedMoment B raw6518step0 raw6518step0Labels = mixedMoment B raw6518step1 raw6518step1Labels := by
      have ha : raw6518step1 = -raw6518step0 := by apply Matrix.ext; change ∀ i j, raw6518step1 i j = -(raw6518step0 i j); unfold raw6518step1 raw6518step0; decide +kernel
      have hl : raw6518step1Labels = raw6518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6518step1 raw6518step1Labels = mixedMoment B raw6518step2 raw6518step2Labels := by
      have ha : raw6518step2 = raw6518step1 := by apply Matrix.ext; unfold raw6518step2 raw6518step1; decide +kernel
      have hl : raw6518step1Labels = labelEmbedding1 ∘ raw6518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6518step1 raw6518step1Labels raw6518step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw6519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6519Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6519step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6519step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6519step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6519step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6519step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6519 raw6519Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw6519 raw6519Labels = mixedMoment B raw6519step0 raw6519step0Labels := by
      have hz : ∀ j, raw6519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6519step0 = (fun i j => raw6519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6519step0 raw6519; decide +kernel
      have hl : raw6519step0Labels = raw6519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6519 raw6519Labels permutation346 hz
    mixedMoment B raw6519step0 raw6519step0Labels = mixedMoment B raw6519step1 raw6519step1Labels := by
      have ha : raw6519step1 = (fun i j => raw6519step0 (permutation80 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6519step1 raw6519step0; decide +kernel
      have hl : raw6519step1Labels = raw6519step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6519step0 raw6519step0Labels permutation80 permutation5
    mixedMoment B raw6519step1 raw6519step1Labels = mixedMoment B raw6519step2 raw6519step2Labels := by
      have ha : raw6519step2 = -raw6519step1 := by apply Matrix.ext; change ∀ i j, raw6519step2 i j = -(raw6519step1 i j); unfold raw6519step2 raw6519step1; decide +kernel
      have hl : raw6519step2Labels = raw6519step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6519step2 raw6519step2Labels = mixedMoment B raw6519step3 raw6519step3Labels := by
      have ha : raw6519step3 = raw6519step2 := by apply Matrix.ext; unfold raw6519step3 raw6519step2; decide +kernel
      have hl : raw6519step2Labels = labelEmbedding1 ∘ raw6519step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6519step2 raw6519step2Labels raw6519step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw6520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6520Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6520step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6520step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw6520step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6520step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6520step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6520step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6520step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6520 raw6520Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw6520 raw6520Labels = mixedMoment B raw6520step0 raw6520step0Labels := by
      have hz : ∀ j, raw6520 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6520step0 = (fun i j => raw6520 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6520step0 raw6520; decide +kernel
      have hl : raw6520step0Labels = raw6520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6520 raw6520Labels permutation520 hz
    mixedMoment B raw6520step0 raw6520step0Labels = mixedMoment B raw6520step1 raw6520step1Labels := by
      have hz : ∀ j, raw6520step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6520step1 = (fun i j => raw6520step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6520step1 raw6520step0; decide +kernel
      have hl : raw6520step1Labels = raw6520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6520step0 raw6520step0Labels permutation80 hz
    mixedMoment B raw6520step1 raw6520step1Labels = mixedMoment B raw6520step2 raw6520step2Labels := by
      have ha : raw6520step2 = (fun i j => raw6520step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6520step2 raw6520step1; decide +kernel
      have hl : raw6520step2Labels = raw6520step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6520step1 raw6520step1Labels permutation9 permutation7
    mixedMoment B raw6520step2 raw6520step2Labels = mixedMoment B raw6520step3 raw6520step3Labels := by
      have ha : raw6520step3 = -raw6520step2 := by apply Matrix.ext; change ∀ i j, raw6520step3 i j = -(raw6520step2 i j); unfold raw6520step3 raw6520step2; decide +kernel
      have hl : raw6520step3Labels = raw6520step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6520step3 raw6520step3Labels = mixedMoment B raw6520step4 raw6520step4Labels := by
      have ha : raw6520step4 = raw6520step3 := by apply Matrix.ext; unfold raw6520step4 raw6520step3; decide +kernel
      have hl : raw6520step3Labels = labelEmbedding1 ∘ raw6520step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6520step3 raw6520step3Labels raw6520step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw6521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6521Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6521step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6521step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6521step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6521step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6521step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6521 raw6521Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw6521 raw6521Labels = mixedMoment B raw6521step0 raw6521step0Labels := by
      have hz : ∀ j, raw6521 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6521step0 = (fun i j => raw6521 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6521step0 raw6521; decide +kernel
      have hl : raw6521step0Labels = raw6521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6521 raw6521Labels permutation346 hz
    mixedMoment B raw6521step0 raw6521step0Labels = mixedMoment B raw6521step1 raw6521step1Labels := by
      have ha : raw6521step1 = (fun i j => raw6521step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6521step1 raw6521step0; decide +kernel
      have hl : raw6521step1Labels = raw6521step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6521step0 raw6521step0Labels permutation35 permutation7
    mixedMoment B raw6521step1 raw6521step1Labels = mixedMoment B raw6521step2 raw6521step2Labels := by
      have ha : raw6521step2 = -raw6521step1 := by apply Matrix.ext; change ∀ i j, raw6521step2 i j = -(raw6521step1 i j); unfold raw6521step2 raw6521step1; decide +kernel
      have hl : raw6521step2Labels = raw6521step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6521step2 raw6521step2Labels = mixedMoment B raw6521step3 raw6521step3Labels := by
      have ha : raw6521step3 = raw6521step2 := by apply Matrix.ext; unfold raw6521step3 raw6521step2; decide +kernel
      have hl : raw6521step2Labels = labelEmbedding1 ∘ raw6521step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6521step2 raw6521step2Labels raw6521step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw6522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6522Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6522step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw6522step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6522step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6522step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6522step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6522step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6522 raw6522Labels = mixedMoment B node3246 node3246Labels := by
  calc
    mixedMoment B raw6522 raw6522Labels = mixedMoment B raw6522step0 raw6522step0Labels := by
      have hz : ∀ j, raw6522 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6522step0 = (fun i j => raw6522 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6522step0 raw6522; decide +kernel
      have hl : raw6522step0Labels = raw6522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6522 raw6522Labels permutation346 hz
    mixedMoment B raw6522step0 raw6522step0Labels = mixedMoment B raw6522step1 raw6522step1Labels := by
      have ha : raw6522step1 = (fun i j => raw6522step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6522step1 raw6522step0; decide +kernel
      have hl : raw6522step1Labels = raw6522step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6522step0 raw6522step0Labels permutation41 permutation5
    mixedMoment B raw6522step1 raw6522step1Labels = mixedMoment B raw6522step2 raw6522step2Labels := by
      have ha : raw6522step2 = -raw6522step1 := by apply Matrix.ext; change ∀ i j, raw6522step2 i j = -(raw6522step1 i j); unfold raw6522step2 raw6522step1; decide +kernel
      have hl : raw6522step2Labels = raw6522step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6522step2 raw6522step2Labels = mixedMoment B raw6522step3 raw6522step3Labels := by
      have ha : raw6522step3 = raw6522step2 := by apply Matrix.ext; unfold raw6522step3 raw6522step2; decide +kernel
      have hl : raw6522step2Labels = labelEmbedding1 ∘ raw6522step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6522step2 raw6522step2Labels raw6522step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3246 node3246Labels := by rfl

def raw6523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6523Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6523step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6523step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6523step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6523 raw6523Labels = mixedMoment B node3559 node3559Labels := by
  calc
    mixedMoment B raw6523 raw6523Labels = mixedMoment B raw6523step0 raw6523step0Labels := by
      have ha : raw6523step0 = (fun i j => raw6523 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6523step0 raw6523; decide +kernel
      have hl : raw6523step0Labels = raw6523Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6523 raw6523Labels permutation155 permutation7
    mixedMoment B raw6523step0 raw6523step0Labels = mixedMoment B raw6523step1 raw6523step1Labels := by
      have ha : raw6523step1 = -raw6523step0 := by apply Matrix.ext; change ∀ i j, raw6523step1 i j = -(raw6523step0 i j); unfold raw6523step1 raw6523step0; decide +kernel
      have hl : raw6523step1Labels = raw6523step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6523step1 raw6523step1Labels = mixedMoment B raw6523step2 raw6523step2Labels := by
      have ha : raw6523step2 = raw6523step1 := by apply Matrix.ext; unfold raw6523step2 raw6523step1; decide +kernel
      have hl : raw6523step1Labels = labelEmbedding1 ∘ raw6523step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6523step1 raw6523step1Labels raw6523step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3559 node3559Labels := by rfl

def raw6524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6524Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6524step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw6524step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6524step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6524step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6524step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6524 raw6524Labels = mixedMoment B node2841 node2841Labels := by
  calc
    mixedMoment B raw6524 raw6524Labels = mixedMoment B raw6524step0 raw6524step0Labels := by
      have hz : ∀ j, raw6524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6524step0 = (fun i j => raw6524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6524step0 raw6524; decide +kernel
      have hl : raw6524step0Labels = raw6524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6524 raw6524Labels permutation346 hz
    mixedMoment B raw6524step0 raw6524step0Labels = mixedMoment B raw6524step1 raw6524step1Labels := by
      have ha : raw6524step1 = (fun i j => raw6524step0 (permutation83 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6524step1 raw6524step0; decide +kernel
      have hl : raw6524step1Labels = raw6524step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6524step0 raw6524step0Labels permutation83 permutation5
    mixedMoment B raw6524step1 raw6524step1Labels = mixedMoment B raw6524step2 raw6524step2Labels := by
      have ha : raw6524step2 = -raw6524step1 := by apply Matrix.ext; change ∀ i j, raw6524step2 i j = -(raw6524step1 i j); unfold raw6524step2 raw6524step1; decide +kernel
      have hl : raw6524step2Labels = raw6524step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6524step2 raw6524step2Labels = mixedMoment B raw6524step3 raw6524step3Labels := by
      have ha : raw6524step3 = raw6524step2 := by apply Matrix.ext; unfold raw6524step3 raw6524step2; decide +kernel
      have hl : raw6524step2Labels = labelEmbedding1 ∘ raw6524step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6524step2 raw6524step2Labels raw6524step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2841 node2841Labels := by rfl

def raw6525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6525Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6525step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6525step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6525step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6525step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6525step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6525step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6525step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6525step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6525 raw6525Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw6525 raw6525Labels = mixedMoment B raw6525step0 raw6525step0Labels := by
      have hz : ∀ j, raw6525 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6525step0 = (fun i j => raw6525 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6525step0 raw6525; decide +kernel
      have hl : raw6525step0Labels = raw6525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6525 raw6525Labels permutation520 hz
    mixedMoment B raw6525step0 raw6525step0Labels = mixedMoment B raw6525step1 raw6525step1Labels := by
      have hz : ∀ j, raw6525step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6525step1 = (fun i j => raw6525step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6525step1 raw6525step0; decide +kernel
      have hl : raw6525step1Labels = raw6525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6525step0 raw6525step0Labels permutation80 hz
    mixedMoment B raw6525step1 raw6525step1Labels = mixedMoment B raw6525step2 raw6525step2Labels := by
      have ha : raw6525step2 = (fun i j => raw6525step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6525step2 raw6525step1; decide +kernel
      have hl : raw6525step2Labels = raw6525step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6525step1 raw6525step1Labels permutation9 permutation7
    mixedMoment B raw6525step2 raw6525step2Labels = mixedMoment B raw6525step3 raw6525step3Labels := by
      have ha : raw6525step3 = -raw6525step2 := by apply Matrix.ext; change ∀ i j, raw6525step3 i j = -(raw6525step2 i j); unfold raw6525step3 raw6525step2; decide +kernel
      have hl : raw6525step3Labels = raw6525step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6525step3 raw6525step3Labels = mixedMoment B raw6525step4 raw6525step4Labels := by
      have ha : raw6525step4 = raw6525step3 := by apply Matrix.ext; unfold raw6525step4 raw6525step3; decide +kernel
      have hl : raw6525step3Labels = labelEmbedding1 ∘ raw6525step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6525step3 raw6525step3Labels raw6525step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw6526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6526Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6526step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6526step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6526step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6526step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6526 raw6526Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw6526 raw6526Labels = mixedMoment B raw6526step0 raw6526step0Labels := by
      have hz : ∀ j, raw6526 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6526step0 = (fun i j => raw6526 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6526step0 raw6526; decide +kernel
      have hl : raw6526step0Labels = raw6526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6526 raw6526Labels permutation346 hz
    mixedMoment B raw6526step0 raw6526step0Labels = mixedMoment B raw6526step1 raw6526step1Labels := by
      have ha : raw6526step1 = (fun i j => raw6526step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6526step1 raw6526step0; decide +kernel
      have hl : raw6526step1Labels = raw6526step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6526step0 raw6526step0Labels permutation35 permutation7
    mixedMoment B raw6526step1 raw6526step1Labels = mixedMoment B raw6526step2 raw6526step2Labels := by
      have ha : raw6526step2 = -raw6526step1 := by apply Matrix.ext; change ∀ i j, raw6526step2 i j = -(raw6526step1 i j); unfold raw6526step2 raw6526step1; decide +kernel
      have hl : raw6526step2Labels = raw6526step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6526step2 raw6526step2Labels = mixedMoment B raw6526step3 raw6526step3Labels := by
      have ha : raw6526step3 = raw6526step2 := by apply Matrix.ext; unfold raw6526step3 raw6526step2; decide +kernel
      have hl : raw6526step2Labels = labelEmbedding1 ∘ raw6526step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6526step2 raw6526step2Labels raw6526step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw6527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6527Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw6527step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw6527step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6527step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw6527step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6527 raw6527Labels = mixedMoment B node3241 node3241Labels := by
  calc
    mixedMoment B raw6527 raw6527Labels = mixedMoment B raw6527step0 raw6527step0Labels := by
      have ha : raw6527step0 = (fun i j => raw6527 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6527step0 raw6527; decide +kernel
      have hl : raw6527step0Labels = raw6527Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6527 raw6527Labels permutation200 permutation5
    mixedMoment B raw6527step0 raw6527step0Labels = mixedMoment B raw6527step1 raw6527step1Labels := by
      have ha : raw6527step1 = -raw6527step0 := by apply Matrix.ext; change ∀ i j, raw6527step1 i j = -(raw6527step0 i j); unfold raw6527step1 raw6527step0; decide +kernel
      have hl : raw6527step1Labels = raw6527step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6527step1 raw6527step1Labels = mixedMoment B raw6527step2 raw6527step2Labels := by
      have ha : raw6527step2 = raw6527step1 := by apply Matrix.ext; unfold raw6527step2 raw6527step1; decide +kernel
      have hl : raw6527step1Labels = labelEmbedding1 ∘ raw6527step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6527step1 raw6527step1Labels raw6527step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3241 node3241Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
