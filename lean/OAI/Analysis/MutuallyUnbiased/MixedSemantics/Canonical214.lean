import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw27392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw27392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27392 raw27392Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw27392 raw27392Labels = mixedMoment B raw27392step0 raw27392step0Labels := by
      have ha : raw27392step0 = (fun i j => raw27392 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27392step0 raw27392; decide +kernel
      have hl : raw27392step0Labels = raw27392Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27392 raw27392Labels permutation682 permutation2
    mixedMoment B raw27392step0 raw27392step0Labels = mixedMoment B raw27392step1 raw27392step1Labels := by
      have ha : raw27392step1 = -raw27392step0 := by apply Matrix.ext; change ∀ i j, raw27392step1 i j = -(raw27392step0 i j); unfold raw27392step1 raw27392step0; decide +kernel
      have hl : raw27392step1Labels = raw27392step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw27393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw27393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw27393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27393 raw27393Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw27393 raw27393Labels = mixedMoment B raw27393step0 raw27393step0Labels := by
      have ha : raw27393step0 = (fun i j => raw27393 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27393step0 raw27393; decide +kernel
      have hl : raw27393step0Labels = raw27393Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27393 raw27393Labels permutation682 permutation2
    mixedMoment B raw27393step0 raw27393step0Labels = mixedMoment B raw27393step1 raw27393step1Labels := by
      have ha : raw27393step1 = -raw27393step0 := by apply Matrix.ext; change ∀ i j, raw27393step1 i j = -(raw27393step0 i j); unfold raw27393step1 raw27393step0; decide +kernel
      have hl : raw27393step1Labels = raw27393step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw27394 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![3, -3]]
def raw27394Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27394step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![3, -3]]
def raw27394step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27394step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw27394step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27394step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw27394step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27394 raw27394Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw27394 raw27394Labels = mixedMoment B raw27394step0 raw27394step0Labels := by
      have hz : ∀ j, raw27394 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw27394step0 = (fun i j => raw27394 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw27394step0 raw27394; decide +kernel
      have hl : raw27394step0Labels = raw27394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27394 raw27394Labels permutation152 hz
    mixedMoment B raw27394step0 raw27394step0Labels = mixedMoment B raw27394step1 raw27394step1Labels := by
      have ha : raw27394step1 = (fun i j => raw27394step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27394step1 raw27394step0; decide +kernel
      have hl : raw27394step1Labels = raw27394step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27394step0 raw27394step0Labels permutation146 permutation0
    mixedMoment B raw27394step1 raw27394step1Labels = mixedMoment B raw27394step2 raw27394step2Labels := by
      have ha : raw27394step2 = -raw27394step1 := by apply Matrix.ext; change ∀ i j, raw27394step2 i j = -(raw27394step1 i j); unfold raw27394step2 raw27394step1; decide +kernel
      have hl : raw27394step2Labels = raw27394step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw27395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27395 raw27395Labels = mixedMoment B node1832 node1832Labels := by
  calc
    mixedMoment B raw27395 raw27395Labels = mixedMoment B raw27395step0 raw27395step0Labels := by
      have hz : ∀ j, raw27395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27395step0 = (fun i j => raw27395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27395step0 raw27395; decide +kernel
      have hl : raw27395step0Labels = raw27395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27395 raw27395Labels permutation434 hz
    mixedMoment B raw27395step0 raw27395step0Labels = mixedMoment B raw27395step1 raw27395step1Labels := by
      have hz : ∀ j, raw27395step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27395step1 = (fun i j => raw27395step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27395step1 raw27395step0; decide +kernel
      have hl : raw27395step1Labels = raw27395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27395step0 raw27395step0Labels permutation80 hz
    _ = mixedMoment B node1832 node1832Labels := by rfl

def raw27396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27396 raw27396Labels = mixedMoment B node1980 node1980Labels := by
  calc
    mixedMoment B raw27396 raw27396Labels = mixedMoment B raw27396step0 raw27396step0Labels := by
      have hz : ∀ j, raw27396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27396step0 = (fun i j => raw27396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27396step0 raw27396; decide +kernel
      have hl : raw27396step0Labels = raw27396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27396 raw27396Labels permutation434 hz
    mixedMoment B raw27396step0 raw27396step0Labels = mixedMoment B raw27396step1 raw27396step1Labels := by
      have ha : raw27396step1 = (fun i j => raw27396step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27396step1 raw27396step0; decide +kernel
      have hl : raw27396step1Labels = raw27396step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27396step0 raw27396step0Labels permutation38 permutation2
    _ = mixedMoment B node1980 node1980Labels := by rfl

def raw27397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw27397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27397 raw27397Labels = mixedMoment B node1980 node1980Labels := by
  calc
    mixedMoment B raw27397 raw27397Labels = mixedMoment B raw27397step0 raw27397step0Labels := by
      have hz : ∀ j, raw27397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27397step0 = (fun i j => raw27397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27397step0 raw27397; decide +kernel
      have hl : raw27397step0Labels = raw27397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27397 raw27397Labels permutation346 hz
    mixedMoment B raw27397step0 raw27397step0Labels = mixedMoment B raw27397step1 raw27397step1Labels := by
      have ha : raw27397step1 = (fun i j => raw27397step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27397step1 raw27397step0; decide +kernel
      have hl : raw27397step1Labels = raw27397step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27397step0 raw27397step0Labels permutation38 permutation2
    _ = mixedMoment B node1980 node1980Labels := by rfl

def raw27398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw27398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27398 raw27398Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw27398 raw27398Labels = mixedMoment B raw27398step0 raw27398step0Labels := by
      have hz : ∀ j, raw27398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27398step0 = (fun i j => raw27398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27398step0 raw27398; decide +kernel
      have hl : raw27398step0Labels = raw27398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27398 raw27398Labels permutation434 hz
    mixedMoment B raw27398step0 raw27398step0Labels = mixedMoment B raw27398step1 raw27398step1Labels := by
      have hz : ∀ j, raw27398step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27398step1 = (fun i j => raw27398step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27398step1 raw27398step0; decide +kernel
      have hl : raw27398step1Labels = raw27398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27398step0 raw27398step0Labels permutation80 hz
    _ = mixedMoment B node2113 node2113Labels := by rfl

def raw27399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27399 raw27399Labels = mixedMoment B node1825 node1825Labels := by
  calc
    mixedMoment B raw27399 raw27399Labels = mixedMoment B raw27399step0 raw27399step0Labels := by
      have hz : ∀ j, raw27399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27399step0 = (fun i j => raw27399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27399step0 raw27399; decide +kernel
      have hl : raw27399step0Labels = raw27399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27399 raw27399Labels permutation346 hz
    mixedMoment B raw27399step0 raw27399step0Labels = mixedMoment B raw27399step1 raw27399step1Labels := by
      have ha : raw27399step1 = (fun i j => raw27399step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27399step1 raw27399step0; decide +kernel
      have hl : raw27399step1Labels = raw27399step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27399step0 raw27399step0Labels permutation34 permutation2
    _ = mixedMoment B node1825 node1825Labels := by rfl

def raw27400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27400 raw27400Labels = mixedMoment B node1973 node1973Labels := by
  calc
    mixedMoment B raw27400 raw27400Labels = mixedMoment B raw27400step0 raw27400step0Labels := by
      have ha : raw27400step0 = (fun i j => raw27400 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27400step0 raw27400; decide +kernel
      have hl : raw27400step0Labels = raw27400Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27400 raw27400Labels permutation178 permutation2
    _ = mixedMoment B node1973 node1973Labels := by rfl

def raw27401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27401 raw27401Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw27401 raw27401Labels = mixedMoment B raw27401step0 raw27401step0Labels := by
      have hz : ∀ j, raw27401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27401step0 = (fun i j => raw27401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27401step0 raw27401; decide +kernel
      have hl : raw27401step0Labels = raw27401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27401 raw27401Labels permutation346 hz
    _ = mixedMoment B node2090 node2090Labels := by rfl

def raw27402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw27402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27402step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27402 raw27402Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw27402 raw27402Labels = mixedMoment B raw27402step0 raw27402step0Labels := by
      have hz : ∀ j, raw27402 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27402step0 = (fun i j => raw27402 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27402step0 raw27402; decide +kernel
      have hl : raw27402step0Labels = raw27402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27402 raw27402Labels permutation520 hz
    mixedMoment B raw27402step0 raw27402step0Labels = mixedMoment B raw27402step1 raw27402step1Labels := by
      have hz : ∀ j, raw27402step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27402step1 = (fun i j => raw27402step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27402step1 raw27402step0; decide +kernel
      have hl : raw27402step1Labels = raw27402step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27402step0 raw27402step0Labels permutation80 hz
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw27403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw27403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw27403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27403 raw27403Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw27403 raw27403Labels = mixedMoment B raw27403step0 raw27403step0Labels := by
      have hz : ∀ j, raw27403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27403step0 = (fun i j => raw27403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27403step0 raw27403; decide +kernel
      have hl : raw27403step0Labels = raw27403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27403 raw27403Labels permutation346 hz
    mixedMoment B raw27403step0 raw27403step0Labels = mixedMoment B raw27403step1 raw27403step1Labels := by
      have ha : raw27403step1 = (fun i j => raw27403step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27403step1 raw27403step0; decide +kernel
      have hl : raw27403step1Labels = raw27403step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27403step0 raw27403step0Labels permutation150 permutation2
    mixedMoment B raw27403step1 raw27403step1Labels = mixedMoment B raw27403step2 raw27403step2Labels := by
      have ha : raw27403step2 = -raw27403step1 := by apply Matrix.ext; change ∀ i j, raw27403step2 i j = -(raw27403step1 i j); unfold raw27403step2 raw27403step1; decide +kernel
      have hl : raw27403step2Labels = raw27403step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw27404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27404 raw27404Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw27404 raw27404Labels = mixedMoment B raw27404step0 raw27404step0Labels := by
      have hz : ∀ j, raw27404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27404step0 = (fun i j => raw27404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27404step0 raw27404; decide +kernel
      have hl : raw27404step0Labels = raw27404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27404 raw27404Labels permutation346 hz
    mixedMoment B raw27404step0 raw27404step0Labels = mixedMoment B raw27404step1 raw27404step1Labels := by
      have ha : raw27404step1 = (fun i j => raw27404step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27404step1 raw27404step0; decide +kernel
      have hl : raw27404step1Labels = raw27404step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27404step0 raw27404step0Labels permutation151 permutation2
    mixedMoment B raw27404step1 raw27404step1Labels = mixedMoment B raw27404step2 raw27404step2Labels := by
      have ha : raw27404step2 = -raw27404step1 := by apply Matrix.ext; change ∀ i j, raw27404step2 i j = -(raw27404step1 i j); unfold raw27404step2 raw27404step1; decide +kernel
      have hl : raw27404step2Labels = raw27404step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw27405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw27405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27405 raw27405Labels = mixedMoment B node2423 node2423Labels := by
  calc
    mixedMoment B raw27405 raw27405Labels = mixedMoment B raw27405step0 raw27405step0Labels := by
      have ha : raw27405step0 = (fun i j => raw27405 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27405step0 raw27405; decide +kernel
      have hl : raw27405step0Labels = raw27405Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27405 raw27405Labels permutation682 permutation2
    mixedMoment B raw27405step0 raw27405step0Labels = mixedMoment B raw27405step1 raw27405step1Labels := by
      have ha : raw27405step1 = -raw27405step0 := by apply Matrix.ext; change ∀ i j, raw27405step1 i j = -(raw27405step0 i j); unfold raw27405step1 raw27405step0; decide +kernel
      have hl : raw27405step1Labels = raw27405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2423 node2423Labels := by rfl

def raw27406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw27406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27406 raw27406Labels = mixedMoment B node2443 node2443Labels := by
  calc
    mixedMoment B raw27406 raw27406Labels = mixedMoment B raw27406step0 raw27406step0Labels := by
      have hz : ∀ j, raw27406 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27406step0 = (fun i j => raw27406 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27406step0 raw27406; decide +kernel
      have hl : raw27406step0Labels = raw27406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27406 raw27406Labels permutation346 hz
    mixedMoment B raw27406step0 raw27406step0Labels = mixedMoment B raw27406step1 raw27406step1Labels := by
      have ha : raw27406step1 = (fun i j => raw27406step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27406step1 raw27406step0; decide +kernel
      have hl : raw27406step1Labels = raw27406step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27406step0 raw27406step0Labels permutation151 permutation2
    mixedMoment B raw27406step1 raw27406step1Labels = mixedMoment B raw27406step2 raw27406step2Labels := by
      have ha : raw27406step2 = -raw27406step1 := by apply Matrix.ext; change ∀ i j, raw27406step2 i j = -(raw27406step1 i j); unfold raw27406step2 raw27406step1; decide +kernel
      have hl : raw27406step2Labels = raw27406step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2443 node2443Labels := by rfl

def raw27407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw27407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27407 raw27407Labels = mixedMoment B node2327 node2327Labels := by
  calc
    mixedMoment B raw27407 raw27407Labels = mixedMoment B raw27407step0 raw27407step0Labels := by
      have hz : ∀ j, raw27407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27407step0 = (fun i j => raw27407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27407step0 raw27407; decide +kernel
      have hl : raw27407step0Labels = raw27407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27407 raw27407Labels permutation346 hz
    mixedMoment B raw27407step0 raw27407step0Labels = mixedMoment B raw27407step1 raw27407step1Labels := by
      have ha : raw27407step1 = (fun i j => raw27407step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27407step1 raw27407step0; decide +kernel
      have hl : raw27407step1Labels = raw27407step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27407step0 raw27407step0Labels permutation151 permutation2
    mixedMoment B raw27407step1 raw27407step1Labels = mixedMoment B raw27407step2 raw27407step2Labels := by
      have ha : raw27407step2 = -raw27407step1 := by apply Matrix.ext; change ∀ i j, raw27407step2 i j = -(raw27407step1 i j); unfold raw27407step2 raw27407step1; decide +kernel
      have hl : raw27407step2Labels = raw27407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2327 node2327Labels := by rfl

def raw27408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw27408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27408 raw27408Labels = mixedMoment B node1121 node1121Labels := by
  calc
    mixedMoment B raw27408 raw27408Labels = mixedMoment B raw27408step0 raw27408step0Labels := by
      have hz : ∀ j, raw27408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27408step0 = (fun i j => raw27408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27408step0 raw27408; decide +kernel
      have hl : raw27408step0Labels = raw27408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27408 raw27408Labels permutation346 hz
    mixedMoment B raw27408step0 raw27408step0Labels = mixedMoment B raw27408step1 raw27408step1Labels := by
      have ha : raw27408step1 = (fun i j => raw27408step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27408step1 raw27408step0; decide +kernel
      have hl : raw27408step1Labels = raw27408step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27408step0 raw27408step0Labels permutation151 permutation2
    mixedMoment B raw27408step1 raw27408step1Labels = mixedMoment B raw27408step2 raw27408step2Labels := by
      have ha : raw27408step2 = -raw27408step1 := by apply Matrix.ext; change ∀ i j, raw27408step2 i j = -(raw27408step1 i j); unfold raw27408step2 raw27408step1; decide +kernel
      have hl : raw27408step2Labels = raw27408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1121 node1121Labels := by rfl

def raw27409 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-1, 1], ![1, -1], ![2, -2]]
def raw27409Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27409step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw27409step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27409step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw27409step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27409 raw27409Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw27409 raw27409Labels = mixedMoment B raw27409step0 raw27409step0Labels := by
      have hz : ∀ j, raw27409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27409step0 = (fun i j => raw27409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27409step0 raw27409; decide +kernel
      have hl : raw27409step0Labels = raw27409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27409 raw27409Labels permutation346 hz
    mixedMoment B raw27409step0 raw27409step0Labels = mixedMoment B raw27409step1 raw27409step1Labels := by
      have hz : ∀ j, raw27409step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw27409step1 = (fun i j => raw27409step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw27409step1 raw27409step0; decide +kernel
      have hl : raw27409step1Labels = raw27409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27409step0 raw27409step0Labels permutation32 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw27410 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27410 raw27410Labels = mixedMoment B node3434 node3434Labels := by
  calc
    mixedMoment B raw27410 raw27410Labels = mixedMoment B raw27410step0 raw27410step0Labels := by
      have ha : raw27410step0 = (fun i j => raw27410 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27410step0 raw27410; decide +kernel
      have hl : raw27410step0Labels = raw27410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27410 raw27410Labels permutation681 permutation2
    _ = mixedMoment B node3434 node3434Labels := by rfl

def raw27411 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27411 raw27411Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw27411 raw27411Labels = mixedMoment B raw27411step0 raw27411step0Labels := by
      have hz : ∀ j, raw27411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27411step0 = (fun i j => raw27411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27411step0 raw27411; decide +kernel
      have hl : raw27411step0Labels = raw27411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27411 raw27411Labels permutation434 hz
    mixedMoment B raw27411step0 raw27411step0Labels = mixedMoment B raw27411step1 raw27411step1Labels := by
      have hz : ∀ j, raw27411step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27411step1 = (fun i j => raw27411step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27411step1 raw27411step0; decide +kernel
      have hl : raw27411step1Labels = raw27411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27411step0 raw27411step0Labels permutation80 hz
    mixedMoment B raw27411step1 raw27411step1Labels = mixedMoment B raw27411step2 raw27411step2Labels := by
      have ha : raw27411step2 = (fun i j => raw27411step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27411step2 raw27411step1; decide +kernel
      have hl : raw27411step2Labels = raw27411step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27411step1 raw27411step1Labels permutation30 permutation2
    _ = mixedMoment B node3486 node3486Labels := by rfl

def raw27412 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27412 raw27412Labels = mixedMoment B node3355 node3355Labels := by
  calc
    mixedMoment B raw27412 raw27412Labels = mixedMoment B raw27412step0 raw27412step0Labels := by
      have hz : ∀ j, raw27412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27412step0 = (fun i j => raw27412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27412step0 raw27412; decide +kernel
      have hl : raw27412step0Labels = raw27412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27412 raw27412Labels permutation346 hz
    mixedMoment B raw27412step0 raw27412step0Labels = mixedMoment B raw27412step1 raw27412step1Labels := by
      have ha : raw27412step1 = (fun i j => raw27412step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27412step1 raw27412step0; decide +kernel
      have hl : raw27412step1Labels = raw27412step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27412step0 raw27412step0Labels permutation150 permutation2
    _ = mixedMoment B node3355 node3355Labels := by rfl

def raw27413 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27413 raw27413Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw27413 raw27413Labels = mixedMoment B raw27413step0 raw27413step0Labels := by
      have hz : ∀ j, raw27413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27413step0 = (fun i j => raw27413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27413step0 raw27413; decide +kernel
      have hl : raw27413step0Labels = raw27413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27413 raw27413Labels permutation346 hz
    mixedMoment B raw27413step0 raw27413step0Labels = mixedMoment B raw27413step1 raw27413step1Labels := by
      have ha : raw27413step1 = (fun i j => raw27413step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27413step1 raw27413step0; decide +kernel
      have hl : raw27413step1Labels = raw27413step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27413step0 raw27413step0Labels permutation150 permutation2
    _ = mixedMoment B node1946 node1946Labels := by rfl

def raw27414 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27414step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -2, 3], ![-2, 3, -1]]
def raw27414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27414step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 2, -3], ![2, -3, 1]]
def raw27414step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27414 raw27414Labels = mixedMoment B node2267 node2267Labels := by
  calc
    mixedMoment B raw27414 raw27414Labels = mixedMoment B raw27414step0 raw27414step0Labels := by
      have hz : ∀ j, raw27414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27414step0 = (fun i j => raw27414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27414step0 raw27414; decide +kernel
      have hl : raw27414step0Labels = raw27414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27414 raw27414Labels permutation434 hz
    mixedMoment B raw27414step0 raw27414step0Labels = mixedMoment B raw27414step1 raw27414step1Labels := by
      have hz : ∀ j, raw27414step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27414step1 = (fun i j => raw27414step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27414step1 raw27414step0; decide +kernel
      have hl : raw27414step1Labels = raw27414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27414step0 raw27414step0Labels permutation80 hz
    mixedMoment B raw27414step1 raw27414step1Labels = mixedMoment B raw27414step2 raw27414step2Labels := by
      have ha : raw27414step2 = (fun i j => raw27414step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27414step2 raw27414step1; decide +kernel
      have hl : raw27414step2Labels = raw27414step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27414step1 raw27414step1Labels permutation11 permutation4
    mixedMoment B raw27414step2 raw27414step2Labels = mixedMoment B raw27414step3 raw27414step3Labels := by
      have ha : raw27414step3 = -raw27414step2 := by apply Matrix.ext; change ∀ i j, raw27414step3 i j = -(raw27414step2 i j); unfold raw27414step3 raw27414step2; decide +kernel
      have hl : raw27414step3Labels = raw27414step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2267 node2267Labels := by rfl

def raw27415 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw27415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27415 raw27415Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27415 raw27415Labels = mixedMoment B raw27415step0 raw27415step0Labels := by
      have hz : ∀ j, raw27415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27415step0 = (fun i j => raw27415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27415step0 raw27415; decide +kernel
      have hl : raw27415step0Labels = raw27415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27415 raw27415Labels permutation434 hz
    mixedMoment B raw27415step0 raw27415step0Labels = mixedMoment B raw27415step1 raw27415step1Labels := by
      have ha : raw27415step1 = (fun i j => raw27415step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27415step1 raw27415step0; decide +kernel
      have hl : raw27415step1Labels = raw27415step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27415step0 raw27415step0Labels permutation44 permutation4
    mixedMoment B raw27415step1 raw27415step1Labels = mixedMoment B raw27415step2 raw27415step2Labels := by
      have ha : raw27415step2 = -raw27415step1 := by apply Matrix.ext; change ∀ i j, raw27415step2 i j = -(raw27415step1 i j); unfold raw27415step2 raw27415step1; decide +kernel
      have hl : raw27415step2Labels = raw27415step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw27416 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw27416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27416step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27416 raw27416Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw27416 raw27416Labels = mixedMoment B raw27416step0 raw27416step0Labels := by
      have hz : ∀ j, raw27416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27416step0 = (fun i j => raw27416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27416step0 raw27416; decide +kernel
      have hl : raw27416step0Labels = raw27416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27416 raw27416Labels permutation434 hz
    mixedMoment B raw27416step0 raw27416step0Labels = mixedMoment B raw27416step1 raw27416step1Labels := by
      have hz : ∀ j, raw27416step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27416step1 = (fun i j => raw27416step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27416step1 raw27416step0; decide +kernel
      have hl : raw27416step1Labels = raw27416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27416step0 raw27416step0Labels permutation80 hz
    mixedMoment B raw27416step1 raw27416step1Labels = mixedMoment B raw27416step2 raw27416step2Labels := by
      have ha : raw27416step2 = (fun i j => raw27416step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27416step2 raw27416step1; decide +kernel
      have hl : raw27416step2Labels = raw27416step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27416step1 raw27416step1Labels permutation8 permutation4
    mixedMoment B raw27416step2 raw27416step2Labels = mixedMoment B raw27416step3 raw27416step3Labels := by
      have ha : raw27416step3 = -raw27416step2 := by apply Matrix.ext; change ∀ i j, raw27416step3 i j = -(raw27416step2 i j); unfold raw27416step3 raw27416step2; decide +kernel
      have hl : raw27416step3Labels = raw27416step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw27417 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw27417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw27417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw27417step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27417 raw27417Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw27417 raw27417Labels = mixedMoment B raw27417step0 raw27417step0Labels := by
      have hz : ∀ j, raw27417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27417step0 = (fun i j => raw27417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27417step0 raw27417; decide +kernel
      have hl : raw27417step0Labels = raw27417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27417 raw27417Labels permutation434 hz
    mixedMoment B raw27417step0 raw27417step0Labels = mixedMoment B raw27417step1 raw27417step1Labels := by
      have hz : ∀ j, raw27417step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27417step1 = (fun i j => raw27417step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27417step1 raw27417step0; decide +kernel
      have hl : raw27417step1Labels = raw27417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27417step0 raw27417step0Labels permutation80 hz
    mixedMoment B raw27417step1 raw27417step1Labels = mixedMoment B raw27417step2 raw27417step2Labels := by
      have ha : raw27417step2 = (fun i j => raw27417step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27417step2 raw27417step1; decide +kernel
      have hl : raw27417step2Labels = raw27417step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27417step1 raw27417step1Labels permutation10 permutation4
    mixedMoment B raw27417step2 raw27417step2Labels = mixedMoment B raw27417step3 raw27417step3Labels := by
      have ha : raw27417step3 = -raw27417step2 := by apply Matrix.ext; change ∀ i j, raw27417step3 i j = -(raw27417step2 i j); unfold raw27417step3 raw27417step2; decide +kernel
      have hl : raw27417step3Labels = raw27417step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw27418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw27418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw27418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27418 raw27418Labels = mixedMoment B node1927 node1927Labels := by
  calc
    mixedMoment B raw27418 raw27418Labels = mixedMoment B raw27418step0 raw27418step0Labels := by
      have hz : ∀ j, raw27418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27418step0 = (fun i j => raw27418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27418step0 raw27418; decide +kernel
      have hl : raw27418step0Labels = raw27418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27418 raw27418Labels permutation346 hz
    mixedMoment B raw27418step0 raw27418step0Labels = mixedMoment B raw27418step1 raw27418step1Labels := by
      have ha : raw27418step1 = (fun i j => raw27418step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27418step1 raw27418step0; decide +kernel
      have hl : raw27418step1Labels = raw27418step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27418step0 raw27418step0Labels permutation151 permutation2
    mixedMoment B raw27418step1 raw27418step1Labels = mixedMoment B raw27418step2 raw27418step2Labels := by
      have ha : raw27418step2 = -raw27418step1 := by apply Matrix.ext; change ∀ i j, raw27418step2 i j = -(raw27418step1 i j); unfold raw27418step2 raw27418step1; decide +kernel
      have hl : raw27418step2Labels = raw27418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1927 node1927Labels := by rfl

def raw27419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw27419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27419step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw27419step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27419 raw27419Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw27419 raw27419Labels = mixedMoment B raw27419step0 raw27419step0Labels := by
      have hz : ∀ j, raw27419 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27419step0 = (fun i j => raw27419 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27419step0 raw27419; decide +kernel
      have hl : raw27419step0Labels = raw27419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27419 raw27419Labels permutation346 hz
    mixedMoment B raw27419step0 raw27419step0Labels = mixedMoment B raw27419step1 raw27419step1Labels := by
      have ha : raw27419step1 = (fun i j => raw27419step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27419step1 raw27419step0; decide +kernel
      have hl : raw27419step1Labels = raw27419step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27419step0 raw27419step0Labels permutation150 permutation2
    mixedMoment B raw27419step1 raw27419step1Labels = mixedMoment B raw27419step2 raw27419step2Labels := by
      have ha : raw27419step2 = -raw27419step1 := by apply Matrix.ext; change ∀ i j, raw27419step2 i j = -(raw27419step1 i j); unfold raw27419step2 raw27419step1; decide +kernel
      have hl : raw27419step2Labels = raw27419step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw27420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw27420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw27420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27420 raw27420Labels = mixedMoment B node1923 node1923Labels := by
  calc
    mixedMoment B raw27420 raw27420Labels = mixedMoment B raw27420step0 raw27420step0Labels := by
      have ha : raw27420step0 = (fun i j => raw27420 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27420step0 raw27420; decide +kernel
      have hl : raw27420step0Labels = raw27420Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27420 raw27420Labels permutation688 permutation2
    mixedMoment B raw27420step0 raw27420step0Labels = mixedMoment B raw27420step1 raw27420step1Labels := by
      have ha : raw27420step1 = -raw27420step0 := by apply Matrix.ext; change ∀ i j, raw27420step1 i j = -(raw27420step0 i j); unfold raw27420step1 raw27420step0; decide +kernel
      have hl : raw27420step1Labels = raw27420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1923 node1923Labels := by rfl

def raw27421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw27421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw27421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27421 raw27421Labels = mixedMoment B node1949 node1949Labels := by
  calc
    mixedMoment B raw27421 raw27421Labels = mixedMoment B raw27421step0 raw27421step0Labels := by
      have hz : ∀ j, raw27421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27421step0 = (fun i j => raw27421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27421step0 raw27421; decide +kernel
      have hl : raw27421step0Labels = raw27421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27421 raw27421Labels permutation346 hz
    mixedMoment B raw27421step0 raw27421step0Labels = mixedMoment B raw27421step1 raw27421step1Labels := by
      have ha : raw27421step1 = (fun i j => raw27421step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27421step1 raw27421step0; decide +kernel
      have hl : raw27421step1Labels = raw27421step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27421step0 raw27421step0Labels permutation149 permutation2
    mixedMoment B raw27421step1 raw27421step1Labels = mixedMoment B raw27421step2 raw27421step2Labels := by
      have ha : raw27421step2 = -raw27421step1 := by apply Matrix.ext; change ∀ i j, raw27421step2 i j = -(raw27421step1 i j); unfold raw27421step2 raw27421step1; decide +kernel
      have hl : raw27421step2Labels = raw27421step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1949 node1949Labels := by rfl

def raw27422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw27422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw27422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw27422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw27422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27422 raw27422Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw27422 raw27422Labels = mixedMoment B raw27422step0 raw27422step0Labels := by
      have hz : ∀ j, raw27422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27422step0 = (fun i j => raw27422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27422step0 raw27422; decide +kernel
      have hl : raw27422step0Labels = raw27422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27422 raw27422Labels permutation346 hz
    mixedMoment B raw27422step0 raw27422step0Labels = mixedMoment B raw27422step1 raw27422step1Labels := by
      have ha : raw27422step1 = (fun i j => raw27422step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27422step1 raw27422step0; decide +kernel
      have hl : raw27422step1Labels = raw27422step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27422step0 raw27422step0Labels permutation151 permutation2
    mixedMoment B raw27422step1 raw27422step1Labels = mixedMoment B raw27422step2 raw27422step2Labels := by
      have ha : raw27422step2 = -raw27422step1 := by apply Matrix.ext; change ∀ i j, raw27422step2 i j = -(raw27422step1 i j); unfold raw27422step2 raw27422step1; decide +kernel
      have hl : raw27422step2Labels = raw27422step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw27423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw27423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw27423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw27423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw27423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27423 raw27423Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw27423 raw27423Labels = mixedMoment B raw27423step0 raw27423step0Labels := by
      have hz : ∀ j, raw27423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27423step0 = (fun i j => raw27423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27423step0 raw27423; decide +kernel
      have hl : raw27423step0Labels = raw27423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27423 raw27423Labels permutation346 hz
    mixedMoment B raw27423step0 raw27423step0Labels = mixedMoment B raw27423step1 raw27423step1Labels := by
      have ha : raw27423step1 = (fun i j => raw27423step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27423step1 raw27423step0; decide +kernel
      have hl : raw27423step1Labels = raw27423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27423step0 raw27423step0Labels permutation151 permutation2
    mixedMoment B raw27423step1 raw27423step1Labels = mixedMoment B raw27423step2 raw27423step2Labels := by
      have ha : raw27423step2 = -raw27423step1 := by apply Matrix.ext; change ∀ i j, raw27423step2 i j = -(raw27423step1 i j); unfold raw27423step2 raw27423step1; decide +kernel
      have hl : raw27423step2Labels = raw27423step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw27424 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![3, -3]]
def raw27424Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27424step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw27424step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27424step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw27424step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27424step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw27424step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27424step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw27424step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27424 raw27424Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw27424 raw27424Labels = mixedMoment B raw27424step0 raw27424step0Labels := by
      have hz : ∀ j, raw27424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27424step0 = (fun i j => raw27424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27424step0 raw27424; decide +kernel
      have hl : raw27424step0Labels = raw27424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27424 raw27424Labels permutation346 hz
    mixedMoment B raw27424step0 raw27424step0Labels = mixedMoment B raw27424step1 raw27424step1Labels := by
      have hz : ∀ j, raw27424step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw27424step1 = (fun i j => raw27424step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw27424step1 raw27424step0; decide +kernel
      have hl : raw27424step1Labels = raw27424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27424step0 raw27424step0Labels permutation32 hz
    mixedMoment B raw27424step1 raw27424step1Labels = mixedMoment B raw27424step2 raw27424step2Labels := by
      have ha : raw27424step2 = (fun i j => raw27424step1 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27424step2 raw27424step1; decide +kernel
      have hl : raw27424step2Labels = raw27424step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27424step1 raw27424step1Labels permutation30 permutation0
    mixedMoment B raw27424step2 raw27424step2Labels = mixedMoment B raw27424step3 raw27424step3Labels := by
      have ha : raw27424step3 = -raw27424step2 := by apply Matrix.ext; change ∀ i j, raw27424step3 i j = -(raw27424step2 i j); unfold raw27424step3 raw27424step2; decide +kernel
      have hl : raw27424step3Labels = raw27424step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw27425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw27425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw27425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27425step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw27425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27425 raw27425Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw27425 raw27425Labels = mixedMoment B raw27425step0 raw27425step0Labels := by
      have hz : ∀ j, raw27425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27425step0 = (fun i j => raw27425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27425step0 raw27425; decide +kernel
      have hl : raw27425step0Labels = raw27425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27425 raw27425Labels permutation434 hz
    mixedMoment B raw27425step0 raw27425step0Labels = mixedMoment B raw27425step1 raw27425step1Labels := by
      have hz : ∀ j, raw27425step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27425step1 = (fun i j => raw27425step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27425step1 raw27425step0; decide +kernel
      have hl : raw27425step1Labels = raw27425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27425step0 raw27425step0Labels permutation80 hz
    mixedMoment B raw27425step1 raw27425step1Labels = mixedMoment B raw27425step2 raw27425step2Labels := by
      have ha : raw27425step2 = (fun i j => raw27425step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27425step2 raw27425step1; decide +kernel
      have hl : raw27425step2Labels = raw27425step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27425step1 raw27425step1Labels permutation30 permutation2
    mixedMoment B raw27425step2 raw27425step2Labels = mixedMoment B raw27425step3 raw27425step3Labels := by
      have ha : raw27425step3 = -raw27425step2 := by apply Matrix.ext; change ∀ i j, raw27425step3 i j = -(raw27425step2 i j); unfold raw27425step3 raw27425step2; decide +kernel
      have hl : raw27425step3Labels = raw27425step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw27426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![3, -1, -2]]
def raw27426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27426step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -2, 3], ![-3, 3, 0]]
def raw27426step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27426step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 2, -3], ![3, -3, 0]]
def raw27426step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27426 raw27426Labels = mixedMoment B node2520 node2520Labels := by
  calc
    mixedMoment B raw27426 raw27426Labels = mixedMoment B raw27426step0 raw27426step0Labels := by
      have hz : ∀ j, raw27426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27426step0 = (fun i j => raw27426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27426step0 raw27426; decide +kernel
      have hl : raw27426step0Labels = raw27426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27426 raw27426Labels permutation434 hz
    mixedMoment B raw27426step0 raw27426step0Labels = mixedMoment B raw27426step1 raw27426step1Labels := by
      have hz : ∀ j, raw27426step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27426step1 = (fun i j => raw27426step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27426step1 raw27426step0; decide +kernel
      have hl : raw27426step1Labels = raw27426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27426step0 raw27426step0Labels permutation80 hz
    mixedMoment B raw27426step1 raw27426step1Labels = mixedMoment B raw27426step2 raw27426step2Labels := by
      have ha : raw27426step2 = (fun i j => raw27426step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27426step2 raw27426step1; decide +kernel
      have hl : raw27426step2Labels = raw27426step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27426step1 raw27426step1Labels permutation31 permutation2
    mixedMoment B raw27426step2 raw27426step2Labels = mixedMoment B raw27426step3 raw27426step3Labels := by
      have ha : raw27426step3 = -raw27426step2 := by apply Matrix.ext; change ∀ i j, raw27426step3 i j = -(raw27426step2 i j); unfold raw27426step3 raw27426step2; decide +kernel
      have hl : raw27426step3Labels = raw27426step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2520 node2520Labels := by rfl

def raw27427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 3, 0]]
def raw27427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27427 raw27427Labels = mixedMoment B node2435 node2435Labels := by
  calc
    mixedMoment B raw27427 raw27427Labels = mixedMoment B raw27427step0 raw27427step0Labels := by
      have hz : ∀ j, raw27427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27427step0 = (fun i j => raw27427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27427step0 raw27427; decide +kernel
      have hl : raw27427step0Labels = raw27427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27427 raw27427Labels permutation434 hz
    mixedMoment B raw27427step0 raw27427step0Labels = mixedMoment B raw27427step1 raw27427step1Labels := by
      have ha : raw27427step1 = (fun i j => raw27427step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27427step1 raw27427step0; decide +kernel
      have hl : raw27427step1Labels = raw27427step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27427step0 raw27427step0Labels permutation151 permutation2
    mixedMoment B raw27427step1 raw27427step1Labels = mixedMoment B raw27427step2 raw27427step2Labels := by
      have ha : raw27427step2 = -raw27427step1 := by apply Matrix.ext; change ∀ i j, raw27427step2 i j = -(raw27427step1 i j); unfold raw27427step2 raw27427step1; decide +kernel
      have hl : raw27427step2Labels = raw27427step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2435 node2435Labels := by rfl

def raw27428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, -1, 3], ![-3, 3, 0]]
def raw27428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27428step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27428 raw27428Labels = mixedMoment B node2435 node2435Labels := by
  calc
    mixedMoment B raw27428 raw27428Labels = mixedMoment B raw27428step0 raw27428step0Labels := by
      have hz : ∀ j, raw27428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27428step0 = (fun i j => raw27428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27428step0 raw27428; decide +kernel
      have hl : raw27428step0Labels = raw27428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27428 raw27428Labels permutation346 hz
    mixedMoment B raw27428step0 raw27428step0Labels = mixedMoment B raw27428step1 raw27428step1Labels := by
      have ha : raw27428step1 = (fun i j => raw27428step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27428step1 raw27428step0; decide +kernel
      have hl : raw27428step1Labels = raw27428step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27428step0 raw27428step0Labels permutation151 permutation2
    mixedMoment B raw27428step1 raw27428step1Labels = mixedMoment B raw27428step2 raw27428step2Labels := by
      have ha : raw27428step2 = -raw27428step1 := by apply Matrix.ext; change ∀ i j, raw27428step2 i j = -(raw27428step1 i j); unfold raw27428step2 raw27428step1; decide +kernel
      have hl : raw27428step2Labels = raw27428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2435 node2435Labels := by rfl

def raw27429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw27429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, -1, -1], ![3, -1, -2]]
def raw27429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![3, -1, -2]]
def raw27429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw27429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw27429step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27429 raw27429Labels = mixedMoment B node2346 node2346Labels := by
  calc
    mixedMoment B raw27429 raw27429Labels = mixedMoment B raw27429step0 raw27429step0Labels := by
      have hz : ∀ j, raw27429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27429step0 = (fun i j => raw27429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27429step0 raw27429; decide +kernel
      have hl : raw27429step0Labels = raw27429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27429 raw27429Labels permutation434 hz
    mixedMoment B raw27429step0 raw27429step0Labels = mixedMoment B raw27429step1 raw27429step1Labels := by
      have hz : ∀ j, raw27429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27429step1 = (fun i j => raw27429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27429step1 raw27429step0; decide +kernel
      have hl : raw27429step1Labels = raw27429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27429step0 raw27429step0Labels permutation80 hz
    mixedMoment B raw27429step1 raw27429step1Labels = mixedMoment B raw27429step2 raw27429step2Labels := by
      have ha : raw27429step2 = (fun i j => raw27429step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27429step2 raw27429step1; decide +kernel
      have hl : raw27429step2Labels = raw27429step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27429step1 raw27429step1Labels permutation31 permutation2
    mixedMoment B raw27429step2 raw27429step2Labels = mixedMoment B raw27429step3 raw27429step3Labels := by
      have ha : raw27429step3 = -raw27429step2 := by apply Matrix.ext; change ∀ i j, raw27429step3 i j = -(raw27429step2 i j); unfold raw27429step3 raw27429step2; decide +kernel
      have hl : raw27429step3Labels = raw27429step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2346 node2346Labels := by rfl

def raw27430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw27430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![4, -2, -2]]
def raw27430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![4, -2, -2]]
def raw27430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw27430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27430step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw27430step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27430 raw27430Labels = mixedMoment B node1146 node1146Labels := by
  calc
    mixedMoment B raw27430 raw27430Labels = mixedMoment B raw27430step0 raw27430step0Labels := by
      have hz : ∀ j, raw27430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27430step0 = (fun i j => raw27430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27430step0 raw27430; decide +kernel
      have hl : raw27430step0Labels = raw27430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27430 raw27430Labels permutation434 hz
    mixedMoment B raw27430step0 raw27430step0Labels = mixedMoment B raw27430step1 raw27430step1Labels := by
      have hz : ∀ j, raw27430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27430step1 = (fun i j => raw27430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27430step1 raw27430step0; decide +kernel
      have hl : raw27430step1Labels = raw27430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27430step0 raw27430step0Labels permutation80 hz
    mixedMoment B raw27430step1 raw27430step1Labels = mixedMoment B raw27430step2 raw27430step2Labels := by
      have ha : raw27430step2 = (fun i j => raw27430step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27430step2 raw27430step1; decide +kernel
      have hl : raw27430step2Labels = raw27430step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27430step1 raw27430step1Labels permutation31 permutation2
    mixedMoment B raw27430step2 raw27430step2Labels = mixedMoment B raw27430step3 raw27430step3Labels := by
      have ha : raw27430step3 = -raw27430step2 := by apply Matrix.ext; change ∀ i j, raw27430step3 i j = -(raw27430step2 i j); unfold raw27430step3 raw27430step2; decide +kernel
      have hl : raw27430step3Labels = raw27430step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1146 node1146Labels := by rfl

def raw27431 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![0, 0], ![1, -1], ![2, -2]]
def raw27431Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27431step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw27431step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27431step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![1, -1], ![2, -2]]
def raw27431step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27431step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw27431step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27431 raw27431Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw27431 raw27431Labels = mixedMoment B raw27431step0 raw27431step0Labels := by
      have hz : ∀ j, raw27431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27431step0 = (fun i j => raw27431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27431step0 raw27431; decide +kernel
      have hl : raw27431step0Labels = raw27431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27431 raw27431Labels permutation434 hz
    mixedMoment B raw27431step0 raw27431step0Labels = mixedMoment B raw27431step1 raw27431step1Labels := by
      have hz : ∀ j, raw27431step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27431step1 = (fun i j => raw27431step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27431step1 raw27431step0; decide +kernel
      have hl : raw27431step1Labels = raw27431step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27431step0 raw27431step0Labels permutation80 hz
    mixedMoment B raw27431step1 raw27431step1Labels = mixedMoment B raw27431step2 raw27431step2Labels := by
      have hz : ∀ j, raw27431step1 (permutation8 0) j = 0 := by decide +kernel
      have ha : raw27431step2 = (fun i j => raw27431step1 (permutation8 i.succ) j) := by apply Matrix.ext; unfold raw27431step2 raw27431step1; decide +kernel
      have hl : raw27431step2Labels = raw27431step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27431step1 raw27431step1Labels permutation8 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw27432 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27432 raw27432Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw27432 raw27432Labels = mixedMoment B raw27432step0 raw27432step0Labels := by
      have hz : ∀ j, raw27432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27432step0 = (fun i j => raw27432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27432step0 raw27432; decide +kernel
      have hl : raw27432step0Labels = raw27432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27432 raw27432Labels permutation434 hz
    mixedMoment B raw27432step0 raw27432step0Labels = mixedMoment B raw27432step1 raw27432step1Labels := by
      have ha : raw27432step1 = (fun i j => raw27432step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27432step1 raw27432step0; decide +kernel
      have hl : raw27432step1Labels = raw27432step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27432step0 raw27432step0Labels permutation56 permutation2
    mixedMoment B raw27432step1 raw27432step1Labels = mixedMoment B raw27432step2 raw27432step2Labels := by
      have ha : raw27432step2 = -raw27432step1 := by apply Matrix.ext; change ∀ i j, raw27432step2 i j = -(raw27432step1 i j); unfold raw27432step2 raw27432step1; decide +kernel
      have hl : raw27432step2Labels = raw27432step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2837 node2837Labels := by rfl

def raw27433 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27433step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27433step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27433 raw27433Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw27433 raw27433Labels = mixedMoment B raw27433step0 raw27433step0Labels := by
      have hz : ∀ j, raw27433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27433step0 = (fun i j => raw27433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27433step0 raw27433; decide +kernel
      have hl : raw27433step0Labels = raw27433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27433 raw27433Labels permutation346 hz
    mixedMoment B raw27433step0 raw27433step0Labels = mixedMoment B raw27433step1 raw27433step1Labels := by
      have ha : raw27433step1 = (fun i j => raw27433step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27433step1 raw27433step0; decide +kernel
      have hl : raw27433step1Labels = raw27433step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27433step0 raw27433step0Labels permutation56 permutation2
    mixedMoment B raw27433step1 raw27433step1Labels = mixedMoment B raw27433step2 raw27433step2Labels := by
      have ha : raw27433step2 = -raw27433step1 := by apply Matrix.ext; change ∀ i j, raw27433step2 i j = -(raw27433step1 i j); unfold raw27433step2 raw27433step1; decide +kernel
      have hl : raw27433step2Labels = raw27433step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2837 node2837Labels := by rfl

def raw27434 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw27434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27434step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-2, 1, 1], ![-2, -1, 3]]
def raw27434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27434step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw27434step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27434 raw27434Labels = mixedMoment B node2842 node2842Labels := by
  calc
    mixedMoment B raw27434 raw27434Labels = mixedMoment B raw27434step0 raw27434step0Labels := by
      have hz : ∀ j, raw27434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27434step0 = (fun i j => raw27434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27434step0 raw27434; decide +kernel
      have hl : raw27434step0Labels = raw27434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27434 raw27434Labels permutation434 hz
    mixedMoment B raw27434step0 raw27434step0Labels = mixedMoment B raw27434step1 raw27434step1Labels := by
      have hz : ∀ j, raw27434step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27434step1 = (fun i j => raw27434step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27434step1 raw27434step0; decide +kernel
      have hl : raw27434step1Labels = raw27434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27434step0 raw27434step0Labels permutation80 hz
    mixedMoment B raw27434step1 raw27434step1Labels = mixedMoment B raw27434step2 raw27434step2Labels := by
      have ha : raw27434step2 = (fun i j => raw27434step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27434step2 raw27434step1; decide +kernel
      have hl : raw27434step2Labels = raw27434step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27434step1 raw27434step1Labels permutation14 permutation2
    mixedMoment B raw27434step2 raw27434step2Labels = mixedMoment B raw27434step3 raw27434step3Labels := by
      have ha : raw27434step3 = -raw27434step2 := by apply Matrix.ext; change ∀ i j, raw27434step3 i j = -(raw27434step2 i j); unfold raw27434step3 raw27434step2; decide +kernel
      have hl : raw27434step3Labels = raw27434step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2842 node2842Labels := by rfl

def raw27435 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![3, -2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw27435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27435step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw27435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27435 raw27435Labels = mixedMoment B node1951 node1951Labels := by
  calc
    mixedMoment B raw27435 raw27435Labels = mixedMoment B raw27435step0 raw27435step0Labels := by
      have hz : ∀ j, raw27435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27435step0 = (fun i j => raw27435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27435step0 raw27435; decide +kernel
      have hl : raw27435step0Labels = raw27435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27435 raw27435Labels permutation434 hz
    mixedMoment B raw27435step0 raw27435step0Labels = mixedMoment B raw27435step1 raw27435step1Labels := by
      have hz : ∀ j, raw27435step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27435step1 = (fun i j => raw27435step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27435step1 raw27435step0; decide +kernel
      have hl : raw27435step1Labels = raw27435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27435step0 raw27435step0Labels permutation80 hz
    mixedMoment B raw27435step1 raw27435step1Labels = mixedMoment B raw27435step2 raw27435step2Labels := by
      have ha : raw27435step2 = (fun i j => raw27435step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27435step2 raw27435step1; decide +kernel
      have hl : raw27435step2Labels = raw27435step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27435step1 raw27435step1Labels permutation30 permutation2
    _ = mixedMoment B node1951 node1951Labels := by rfl

def raw27436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27436 raw27436Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw27436 raw27436Labels = mixedMoment B raw27436step0 raw27436step0Labels := by
      have hz : ∀ j, raw27436 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27436step0 = (fun i j => raw27436 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27436step0 raw27436; decide +kernel
      have hl : raw27436step0Labels = raw27436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27436 raw27436Labels permutation346 hz
    mixedMoment B raw27436step0 raw27436step0Labels = mixedMoment B raw27436step1 raw27436step1Labels := by
      have ha : raw27436step1 = (fun i j => raw27436step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27436step1 raw27436step0; decide +kernel
      have hl : raw27436step1Labels = raw27436step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27436step0 raw27436step0Labels permutation34 permutation2
    _ = mixedMoment B node1132 node1132Labels := by rfl

def raw27437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27437 raw27437Labels = mixedMoment B node2335 node2335Labels := by
  calc
    mixedMoment B raw27437 raw27437Labels = mixedMoment B raw27437step0 raw27437step0Labels := by
      have hz : ∀ j, raw27437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27437step0 = (fun i j => raw27437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27437step0 raw27437; decide +kernel
      have hl : raw27437step0Labels = raw27437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27437 raw27437Labels permutation346 hz
    mixedMoment B raw27437step0 raw27437step0Labels = mixedMoment B raw27437step1 raw27437step1Labels := by
      have ha : raw27437step1 = (fun i j => raw27437step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27437step1 raw27437step0; decide +kernel
      have hl : raw27437step1Labels = raw27437step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27437step0 raw27437step0Labels permutation34 permutation2
    _ = mixedMoment B node2335 node2335Labels := by rfl

def raw27438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27438 raw27438Labels = mixedMoment B node2426 node2426Labels := by
  calc
    mixedMoment B raw27438 raw27438Labels = mixedMoment B raw27438step0 raw27438step0Labels := by
      have ha : raw27438step0 = (fun i j => raw27438 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27438step0 raw27438; decide +kernel
      have hl : raw27438step0Labels = raw27438Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27438 raw27438Labels permutation154 permutation2
    _ = mixedMoment B node2426 node2426Labels := by rfl

def raw27439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw27439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27439 raw27439Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw27439 raw27439Labels = mixedMoment B raw27439step0 raw27439step0Labels := by
      have hz : ∀ j, raw27439 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27439step0 = (fun i j => raw27439 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27439step0 raw27439; decide +kernel
      have hl : raw27439step0Labels = raw27439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27439 raw27439Labels permutation520 hz
    mixedMoment B raw27439step0 raw27439step0Labels = mixedMoment B raw27439step1 raw27439step1Labels := by
      have hz : ∀ j, raw27439step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27439step1 = (fun i j => raw27439step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27439step1 raw27439step0; decide +kernel
      have hl : raw27439step1Labels = raw27439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27439step0 raw27439step0Labels permutation80 hz
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw27440 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw27440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27440step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27440 raw27440Labels = mixedMoment B node3385 node3385Labels := by
  calc
    mixedMoment B raw27440 raw27440Labels = mixedMoment B raw27440step0 raw27440step0Labels := by
      have hz : ∀ j, raw27440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27440step0 = (fun i j => raw27440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27440step0 raw27440; decide +kernel
      have hl : raw27440step0Labels = raw27440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27440 raw27440Labels permutation346 hz
    mixedMoment B raw27440step0 raw27440step0Labels = mixedMoment B raw27440step1 raw27440step1Labels := by
      have ha : raw27440step1 = (fun i j => raw27440step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27440step1 raw27440step0; decide +kernel
      have hl : raw27440step1Labels = raw27440step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27440step0 raw27440step0Labels permutation38 permutation2
    mixedMoment B raw27440step1 raw27440step1Labels = mixedMoment B raw27440step2 raw27440step2Labels := by
      have ha : raw27440step2 = -raw27440step1 := by apply Matrix.ext; change ∀ i j, raw27440step2 i j = -(raw27440step1 i j); unfold raw27440step2 raw27440step1; decide +kernel
      have hl : raw27440step2Labels = raw27440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3385 node3385Labels := by rfl

def raw27441 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27441 raw27441Labels = mixedMoment B node3368 node3368Labels := by
  calc
    mixedMoment B raw27441 raw27441Labels = mixedMoment B raw27441step0 raw27441step0Labels := by
      have ha : raw27441step0 = (fun i j => raw27441 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27441step0 raw27441; decide +kernel
      have hl : raw27441step0Labels = raw27441Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27441 raw27441Labels permutation200 permutation2
    mixedMoment B raw27441step0 raw27441step0Labels = mixedMoment B raw27441step1 raw27441step1Labels := by
      have ha : raw27441step1 = -raw27441step0 := by apply Matrix.ext; change ∀ i j, raw27441step1 i j = -(raw27441step0 i j); unfold raw27441step1 raw27441step0; decide +kernel
      have hl : raw27441step1Labels = raw27441step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3368 node3368Labels := by rfl

def raw27442 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27442 raw27442Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw27442 raw27442Labels = mixedMoment B raw27442step0 raw27442step0Labels := by
      have hz : ∀ j, raw27442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27442step0 = (fun i j => raw27442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27442step0 raw27442; decide +kernel
      have hl : raw27442step0Labels = raw27442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27442 raw27442Labels permutation346 hz
    mixedMoment B raw27442step0 raw27442step0Labels = mixedMoment B raw27442step1 raw27442step1Labels := by
      have ha : raw27442step1 = (fun i j => raw27442step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27442step1 raw27442step0; decide +kernel
      have hl : raw27442step1Labels = raw27442step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27442step0 raw27442step0Labels permutation149 permutation2
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw27443 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw27443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27443 raw27443Labels = mixedMoment B node3343 node3343Labels := by
  calc
    mixedMoment B raw27443 raw27443Labels = mixedMoment B raw27443step0 raw27443step0Labels := by
      have hz : ∀ j, raw27443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27443step0 = (fun i j => raw27443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27443step0 raw27443; decide +kernel
      have hl : raw27443step0Labels = raw27443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27443 raw27443Labels permutation346 hz
    mixedMoment B raw27443step0 raw27443step0Labels = mixedMoment B raw27443step1 raw27443step1Labels := by
      have ha : raw27443step1 = (fun i j => raw27443step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27443step1 raw27443step0; decide +kernel
      have hl : raw27443step1Labels = raw27443step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27443step0 raw27443step0Labels permutation149 permutation2
    _ = mixedMoment B node3343 node3343Labels := by rfl

def raw27444 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw27444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27444 raw27444Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw27444 raw27444Labels = mixedMoment B raw27444step0 raw27444step0Labels := by
      have hz : ∀ j, raw27444 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27444step0 = (fun i j => raw27444 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27444step0 raw27444; decide +kernel
      have hl : raw27444step0Labels = raw27444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27444 raw27444Labels permutation346 hz
    mixedMoment B raw27444step0 raw27444step0Labels = mixedMoment B raw27444step1 raw27444step1Labels := by
      have ha : raw27444step1 = (fun i j => raw27444step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27444step1 raw27444step0; decide +kernel
      have hl : raw27444step1Labels = raw27444step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27444step0 raw27444step0Labels permutation149 permutation2
    _ = mixedMoment B node1917 node1917Labels := by rfl

def raw27445 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27445 raw27445Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27445 raw27445Labels = mixedMoment B raw27445step0 raw27445step0Labels := by
      have hz : ∀ j, raw27445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27445step0 = (fun i j => raw27445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27445step0 raw27445; decide +kernel
      have hl : raw27445step0Labels = raw27445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27445 raw27445Labels permutation346 hz
    mixedMoment B raw27445step0 raw27445step0Labels = mixedMoment B raw27445step1 raw27445step1Labels := by
      have ha : raw27445step1 = (fun i j => raw27445step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27445step1 raw27445step0; decide +kernel
      have hl : raw27445step1Labels = raw27445step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27445step0 raw27445step0Labels permutation32 permutation4
    mixedMoment B raw27445step1 raw27445step1Labels = mixedMoment B raw27445step2 raw27445step2Labels := by
      have ha : raw27445step2 = -raw27445step1 := by apply Matrix.ext; change ∀ i j, raw27445step2 i j = -(raw27445step1 i j); unfold raw27445step2 raw27445step1; decide +kernel
      have hl : raw27445step2Labels = raw27445step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw27446 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw27446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27446step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27446 raw27446Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw27446 raw27446Labels = mixedMoment B raw27446step0 raw27446step0Labels := by
      have hz : ∀ j, raw27446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27446step0 = (fun i j => raw27446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27446step0 raw27446; decide +kernel
      have hl : raw27446step0Labels = raw27446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27446 raw27446Labels permutation346 hz
    mixedMoment B raw27446step0 raw27446step0Labels = mixedMoment B raw27446step1 raw27446step1Labels := by
      have ha : raw27446step1 = (fun i j => raw27446step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27446step1 raw27446step0; decide +kernel
      have hl : raw27446step1Labels = raw27446step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27446step0 raw27446step0Labels permutation34 permutation4
    mixedMoment B raw27446step1 raw27446step1Labels = mixedMoment B raw27446step2 raw27446step2Labels := by
      have ha : raw27446step2 = -raw27446step1 := by apply Matrix.ext; change ∀ i j, raw27446step2 i j = -(raw27446step1 i j); unfold raw27446step2 raw27446step1; decide +kernel
      have hl : raw27446step2Labels = raw27446step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw27447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27447 raw27447Labels = mixedMoment B node1112 node1112Labels := by
  calc
    mixedMoment B raw27447 raw27447Labels = mixedMoment B raw27447step0 raw27447step0Labels := by
      have ha : raw27447step0 = (fun i j => raw27447 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27447step0 raw27447; decide +kernel
      have hl : raw27447step0Labels = raw27447Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27447 raw27447Labels permutation160 permutation2
    _ = mixedMoment B node1112 node1112Labels := by rfl

def raw27448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27448 raw27448Labels = mixedMoment B node2320 node2320Labels := by
  calc
    mixedMoment B raw27448 raw27448Labels = mixedMoment B raw27448step0 raw27448step0Labels := by
      have ha : raw27448step0 = (fun i j => raw27448 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27448step0 raw27448; decide +kernel
      have hl : raw27448step0Labels = raw27448Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27448 raw27448Labels permutation160 permutation2
    _ = mixedMoment B node2320 node2320Labels := by rfl

def raw27449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27449 raw27449Labels = mixedMoment B node2437 node2437Labels := by
  calc
    mixedMoment B raw27449 raw27449Labels = mixedMoment B raw27449step0 raw27449step0Labels := by
      have ha : raw27449step0 = (fun i j => raw27449 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27449step0 raw27449; decide +kernel
      have hl : raw27449step0Labels = raw27449Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27449 raw27449Labels permutation160 permutation2
    _ = mixedMoment B node2437 node2437Labels := by rfl

def raw27450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw27450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27450 raw27450Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27450 raw27450Labels = mixedMoment B raw27450step0 raw27450step0Labels := by
      have hz : ∀ j, raw27450 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27450step0 = (fun i j => raw27450 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27450step0 raw27450; decide +kernel
      have hl : raw27450step0Labels = raw27450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27450 raw27450Labels permutation520 hz
    mixedMoment B raw27450step0 raw27450step0Labels = mixedMoment B raw27450step1 raw27450step1Labels := by
      have ha : raw27450step1 = (fun i j => raw27450step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27450step1 raw27450step0; decide +kernel
      have hl : raw27450step1Labels = raw27450step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27450step0 raw27450step0Labels permutation34 permutation2
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw27451 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27451 raw27451Labels = mixedMoment B node3443 node3443Labels := by
  calc
    mixedMoment B raw27451 raw27451Labels = mixedMoment B raw27451step0 raw27451step0Labels := by
      have ha : raw27451step0 = (fun i j => raw27451 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27451step0 raw27451; decide +kernel
      have hl : raw27451step0Labels = raw27451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27451 raw27451Labels permutation674 permutation2
    _ = mixedMoment B node3443 node3443Labels := by rfl

def raw27452 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27452 raw27452Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw27452 raw27452Labels = mixedMoment B raw27452step0 raw27452step0Labels := by
      have hz : ∀ j, raw27452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27452step0 = (fun i j => raw27452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27452step0 raw27452; decide +kernel
      have hl : raw27452step0Labels = raw27452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27452 raw27452Labels permutation434 hz
    mixedMoment B raw27452step0 raw27452step0Labels = mixedMoment B raw27452step1 raw27452step1Labels := by
      have ha : raw27452step1 = (fun i j => raw27452step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27452step1 raw27452step0; decide +kernel
      have hl : raw27452step1Labels = raw27452step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27452step0 raw27452step0Labels permutation149 permutation2
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw27453 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27453 raw27453Labels = mixedMoment B node3339 node3339Labels := by
  calc
    mixedMoment B raw27453 raw27453Labels = mixedMoment B raw27453step0 raw27453step0Labels := by
      have ha : raw27453step0 = (fun i j => raw27453 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27453step0 raw27453; decide +kernel
      have hl : raw27453step0Labels = raw27453Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27453 raw27453Labels permutation674 permutation2
    _ = mixedMoment B node3339 node3339Labels := by rfl

def raw27454 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27454 raw27454Labels = mixedMoment B node1907 node1907Labels := by
  calc
    mixedMoment B raw27454 raw27454Labels = mixedMoment B raw27454step0 raw27454step0Labels := by
      have ha : raw27454step0 = (fun i j => raw27454 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27454step0 raw27454; decide +kernel
      have hl : raw27454step0Labels = raw27454Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27454 raw27454Labels permutation674 permutation2
    _ = mixedMoment B node1907 node1907Labels := by rfl

def raw27455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw27455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw27455step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27455 raw27455Labels = mixedMoment B node1904 node1904Labels := by
  calc
    mixedMoment B raw27455 raw27455Labels = mixedMoment B raw27455step0 raw27455step0Labels := by
      have ha : raw27455step0 = (fun i j => raw27455 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27455step0 raw27455; decide +kernel
      have hl : raw27455step0Labels = raw27455Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27455 raw27455Labels permutation682 permutation2
    mixedMoment B raw27455step0 raw27455step0Labels = mixedMoment B raw27455step1 raw27455step1Labels := by
      have ha : raw27455step1 = -raw27455step0 := by apply Matrix.ext; change ∀ i j, raw27455step1 i j = -(raw27455step0 i j); unfold raw27455step1 raw27455step0; decide +kernel
      have hl : raw27455step1Labels = raw27455step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1904 node1904Labels := by rfl

def raw27456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27456 raw27456Labels = mixedMoment B node1922 node1922Labels := by
  calc
    mixedMoment B raw27456 raw27456Labels = mixedMoment B raw27456step0 raw27456step0Labels := by
      have ha : raw27456step0 = (fun i j => raw27456 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27456step0 raw27456; decide +kernel
      have hl : raw27456step0Labels = raw27456Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27456 raw27456Labels permutation686 permutation2
    mixedMoment B raw27456step0 raw27456step0Labels = mixedMoment B raw27456step1 raw27456step1Labels := by
      have ha : raw27456step1 = -raw27456step0 := by apply Matrix.ext; change ∀ i j, raw27456step1 i j = -(raw27456step0 i j); unfold raw27456step1 raw27456step0; decide +kernel
      have hl : raw27456step1Labels = raw27456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1922 node1922Labels := by rfl

def raw27457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw27457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27457 raw27457Labels = mixedMoment B node1909 node1909Labels := by
  calc
    mixedMoment B raw27457 raw27457Labels = mixedMoment B raw27457step0 raw27457step0Labels := by
      have ha : raw27457step0 = (fun i j => raw27457 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27457step0 raw27457; decide +kernel
      have hl : raw27457step0Labels = raw27457Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27457 raw27457Labels permutation680 permutation2
    mixedMoment B raw27457step0 raw27457step0Labels = mixedMoment B raw27457step1 raw27457step1Labels := by
      have ha : raw27457step1 = -raw27457step0 := by apply Matrix.ext; change ∀ i j, raw27457step1 i j = -(raw27457step0 i j); unfold raw27457step1 raw27457step0; decide +kernel
      have hl : raw27457step1Labels = raw27457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1909 node1909Labels := by rfl

def raw27458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw27458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw27458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27458 raw27458Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw27458 raw27458Labels = mixedMoment B raw27458step0 raw27458step0Labels := by
      have ha : raw27458step0 = (fun i j => raw27458 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27458step0 raw27458; decide +kernel
      have hl : raw27458step0Labels = raw27458Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27458 raw27458Labels permutation682 permutation2
    mixedMoment B raw27458step0 raw27458step0Labels = mixedMoment B raw27458step1 raw27458step1Labels := by
      have ha : raw27458step1 = -raw27458step0 := by apply Matrix.ext; change ∀ i j, raw27458step1 i j = -(raw27458step0 i j); unfold raw27458step1 raw27458step0; decide +kernel
      have hl : raw27458step1Labels = raw27458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw27459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw27459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw27459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27459step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27459 raw27459Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw27459 raw27459Labels = mixedMoment B raw27459step0 raw27459step0Labels := by
      have ha : raw27459step0 = (fun i j => raw27459 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27459step0 raw27459; decide +kernel
      have hl : raw27459step0Labels = raw27459Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27459 raw27459Labels permutation682 permutation2
    mixedMoment B raw27459step0 raw27459step0Labels = mixedMoment B raw27459step1 raw27459step1Labels := by
      have ha : raw27459step1 = -raw27459step0 := by apply Matrix.ext; change ∀ i j, raw27459step1 i j = -(raw27459step0 i j); unfold raw27459step1 raw27459step0; decide +kernel
      have hl : raw27459step1Labels = raw27459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw27460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27460Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw27460step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27460 raw27460Labels = mixedMoment B node2881 node2881Labels := by
  calc
    mixedMoment B raw27460 raw27460Labels = mixedMoment B raw27460step0 raw27460step0Labels := by
      have hz : ∀ j, raw27460 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27460step0 = (fun i j => raw27460 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27460step0 raw27460; decide +kernel
      have hl : raw27460step0Labels = raw27460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27460 raw27460Labels permutation434 hz
    mixedMoment B raw27460step0 raw27460step0Labels = mixedMoment B raw27460step1 raw27460step1Labels := by
      have ha : raw27460step1 = (fun i j => raw27460step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27460step1 raw27460step0; decide +kernel
      have hl : raw27460step1Labels = raw27460step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27460step0 raw27460step0Labels permutation149 permutation2
    mixedMoment B raw27460step1 raw27460step1Labels = mixedMoment B raw27460step2 raw27460step2Labels := by
      have ha : raw27460step2 = -raw27460step1 := by apply Matrix.ext; change ∀ i j, raw27460step2 i j = -(raw27460step1 i j); unfold raw27460step2 raw27460step1; decide +kernel
      have hl : raw27460step2Labels = raw27460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2881 node2881Labels := by rfl

def raw27461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27461Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27461step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27461 raw27461Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw27461 raw27461Labels = mixedMoment B raw27461step0 raw27461step0Labels := by
      have hz : ∀ j, raw27461 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27461step0 = (fun i j => raw27461 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27461step0 raw27461; decide +kernel
      have hl : raw27461step0Labels = raw27461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27461 raw27461Labels permutation434 hz
    mixedMoment B raw27461step0 raw27461step0Labels = mixedMoment B raw27461step1 raw27461step1Labels := by
      have hz : ∀ j, raw27461step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27461step1 = (fun i j => raw27461step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27461step1 raw27461step0; decide +kernel
      have hl : raw27461step1Labels = raw27461step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27461step0 raw27461step0Labels permutation56 hz
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw27462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw27462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27462 raw27462Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw27462 raw27462Labels = mixedMoment B raw27462step0 raw27462step0Labels := by
      have hz : ∀ j, raw27462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27462step0 = (fun i j => raw27462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27462step0 raw27462; decide +kernel
      have hl : raw27462step0Labels = raw27462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27462 raw27462Labels permutation434 hz
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw27463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27463Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27463 raw27463Labels = mixedMoment B node2426 node2426Labels := by
  calc
    mixedMoment B raw27463 raw27463Labels = mixedMoment B raw27463step0 raw27463step0Labels := by
      have ha : raw27463step0 = (fun i j => raw27463 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27463step0 raw27463; decide +kernel
      have hl : raw27463step0Labels = raw27463Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27463 raw27463Labels permutation176 permutation2
    _ = mixedMoment B node2426 node2426Labels := by rfl

def raw27464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27464Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27464step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27464 raw27464Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw27464 raw27464Labels = mixedMoment B raw27464step0 raw27464step0Labels := by
      have hz : ∀ j, raw27464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27464step0 = (fun i j => raw27464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27464step0 raw27464; decide +kernel
      have hl : raw27464step0Labels = raw27464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27464 raw27464Labels permutation434 hz
    mixedMoment B raw27464step0 raw27464step0Labels = mixedMoment B raw27464step1 raw27464step1Labels := by
      have ha : raw27464step1 = (fun i j => raw27464step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27464step1 raw27464step0; decide +kernel
      have hl : raw27464step1Labels = raw27464step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27464step0 raw27464step0Labels permutation38 permutation2
    _ = mixedMoment B node2434 node2434Labels := by rfl

def raw27465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw27465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw27465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -3, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27465step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27465 raw27465Labels = mixedMoment B node1317 node1317Labels := by
  calc
    mixedMoment B raw27465 raw27465Labels = mixedMoment B raw27465step0 raw27465step0Labels := by
      have hz : ∀ j, raw27465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27465step0 = (fun i j => raw27465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27465step0 raw27465; decide +kernel
      have hl : raw27465step0Labels = raw27465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27465 raw27465Labels permutation434 hz
    mixedMoment B raw27465step0 raw27465step0Labels = mixedMoment B raw27465step1 raw27465step1Labels := by
      have ha : raw27465step1 = (fun i j => raw27465step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27465step1 raw27465step0; decide +kernel
      have hl : raw27465step1Labels = raw27465step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27465step0 raw27465step0Labels permutation149 permutation2
    mixedMoment B raw27465step1 raw27465step1Labels = mixedMoment B raw27465step2 raw27465step2Labels := by
      have ha : raw27465step2 = -raw27465step1 := by apply Matrix.ext; change ∀ i j, raw27465step2 i j = -(raw27465step1 i j); unfold raw27465step2 raw27465step1; decide +kernel
      have hl : raw27465step2Labels = raw27465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1317 node1317Labels := by rfl

def raw27466 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]
def raw27466Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27466step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![2, -2], ![1, -1]]
def raw27466step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27466step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw27466step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27466step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw27466step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27466 raw27466Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw27466 raw27466Labels = mixedMoment B raw27466step0 raw27466step0Labels := by
      have hz : ∀ j, raw27466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27466step0 = (fun i j => raw27466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27466step0 raw27466; decide +kernel
      have hl : raw27466step0Labels = raw27466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27466 raw27466Labels permutation434 hz
    mixedMoment B raw27466step0 raw27466step0Labels = mixedMoment B raw27466step1 raw27466step1Labels := by
      have hz : ∀ j, raw27466step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27466step1 = (fun i j => raw27466step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27466step1 raw27466step0; decide +kernel
      have hl : raw27466step1Labels = raw27466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27466step0 raw27466step0Labels permutation56 hz
    mixedMoment B raw27466step1 raw27466step1Labels = mixedMoment B raw27466step2 raw27466step2Labels := by
      have ha : raw27466step2 = (fun i j => raw27466step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27466step2 raw27466step1; decide +kernel
      have hl : raw27466step2Labels = raw27466step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27466step1 raw27466step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw27467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27467Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27467 raw27467Labels = mixedMoment B node1155 node1155Labels := by
  calc
    mixedMoment B raw27467 raw27467Labels = mixedMoment B raw27467step0 raw27467step0Labels := by
      have hz : ∀ j, raw27467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27467step0 = (fun i j => raw27467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27467step0 raw27467; decide +kernel
      have hl : raw27467step0Labels = raw27467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27467 raw27467Labels permutation434 hz
    _ = mixedMoment B node1155 node1155Labels := by rfl

def raw27468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27468 raw27468Labels = mixedMoment B node2352 node2352Labels := by
  calc
    mixedMoment B raw27468 raw27468Labels = mixedMoment B raw27468step0 raw27468step0Labels := by
      have hz : ∀ j, raw27468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27468step0 = (fun i j => raw27468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27468step0 raw27468; decide +kernel
      have hl : raw27468step0Labels = raw27468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27468 raw27468Labels permutation434 hz
    _ = mixedMoment B node2352 node2352Labels := by rfl

def raw27469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw27469Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw27469step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27469 raw27469Labels = mixedMoment B node2524 node2524Labels := by
  calc
    mixedMoment B raw27469 raw27469Labels = mixedMoment B raw27469step0 raw27469step0Labels := by
      have ha : raw27469step0 = (fun i j => raw27469 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27469step0 raw27469; decide +kernel
      have hl : raw27469step0Labels = raw27469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27469 raw27469Labels permutation158 permutation2
    _ = mixedMoment B node2524 node2524Labels := by rfl

def raw27470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw27470Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw27470step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw27470step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27470 raw27470Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw27470 raw27470Labels = mixedMoment B raw27470step0 raw27470step0Labels := by
      have hz : ∀ j, raw27470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27470step0 = (fun i j => raw27470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27470step0 raw27470; decide +kernel
      have hl : raw27470step0Labels = raw27470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27470 raw27470Labels permutation434 hz
    mixedMoment B raw27470step0 raw27470step0Labels = mixedMoment B raw27470step1 raw27470step1Labels := by
      have ha : raw27470step1 = (fun i j => raw27470step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27470step1 raw27470step0; decide +kernel
      have hl : raw27470step1Labels = raw27470step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27470step0 raw27470step0Labels permutation33 permutation2
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw27471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw27471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27471step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27471 raw27471Labels = mixedMoment B node1337 node1337Labels := by
  calc
    mixedMoment B raw27471 raw27471Labels = mixedMoment B raw27471step0 raw27471step0Labels := by
      have hz : ∀ j, raw27471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27471step0 = (fun i j => raw27471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27471step0 raw27471; decide +kernel
      have hl : raw27471step0Labels = raw27471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27471 raw27471Labels permutation434 hz
    mixedMoment B raw27471step0 raw27471step0Labels = mixedMoment B raw27471step1 raw27471step1Labels := by
      have ha : raw27471step1 = (fun i j => raw27471step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27471step1 raw27471step0; decide +kernel
      have hl : raw27471step1Labels = raw27471step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27471step0 raw27471step0Labels permutation34 permutation2
    _ = mixedMoment B node1337 node1337Labels := by rfl

def raw27472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw27472Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27472step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw27472step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw27472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27472 raw27472Labels = mixedMoment B node2442 node2442Labels := by
  calc
    mixedMoment B raw27472 raw27472Labels = mixedMoment B raw27472step0 raw27472step0Labels := by
      have hz : ∀ j, raw27472 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27472step0 = (fun i j => raw27472 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27472step0 raw27472; decide +kernel
      have hl : raw27472step0Labels = raw27472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27472 raw27472Labels permutation434 hz
    mixedMoment B raw27472step0 raw27472step0Labels = mixedMoment B raw27472step1 raw27472step1Labels := by
      have ha : raw27472step1 = (fun i j => raw27472step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27472step1 raw27472step0; decide +kernel
      have hl : raw27472step1Labels = raw27472step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27472step0 raw27472step0Labels permutation145 permutation2
    mixedMoment B raw27472step1 raw27472step1Labels = mixedMoment B raw27472step2 raw27472step2Labels := by
      have ha : raw27472step2 = -raw27472step1 := by apply Matrix.ext; change ∀ i j, raw27472step2 i j = -(raw27472step1 i j); unfold raw27472step2 raw27472step1; decide +kernel
      have hl : raw27472step2Labels = raw27472step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2442 node2442Labels := by rfl

def raw27473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw27473Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw27473step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27473step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27473step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27473step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27473step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27473 raw27473Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw27473 raw27473Labels = mixedMoment B raw27473step0 raw27473step0Labels := by
      have hz : ∀ j, raw27473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27473step0 = (fun i j => raw27473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27473step0 raw27473; decide +kernel
      have hl : raw27473step0Labels = raw27473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27473 raw27473Labels permutation434 hz
    mixedMoment B raw27473step0 raw27473step0Labels = mixedMoment B raw27473step1 raw27473step1Labels := by
      have ha : raw27473step1 = (fun i j => raw27473step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27473step1 raw27473step0; decide +kernel
      have hl : raw27473step1Labels = raw27473step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27473step0 raw27473step0Labels permutation151 permutation2
    mixedMoment B raw27473step1 raw27473step1Labels = mixedMoment B raw27473step2 raw27473step2Labels := by
      have ha : raw27473step2 = -raw27473step1 := by apply Matrix.ext; change ∀ i j, raw27473step2 i j = -(raw27473step1 i j); unfold raw27473step2 raw27473step1; decide +kernel
      have hl : raw27473step2Labels = raw27473step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw27474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw27474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw27474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27474 raw27474Labels = mixedMoment B node2437 node2437Labels := by
  calc
    mixedMoment B raw27474 raw27474Labels = mixedMoment B raw27474step0 raw27474step0Labels := by
      have ha : raw27474step0 = (fun i j => raw27474 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27474step0 raw27474; decide +kernel
      have hl : raw27474step0Labels = raw27474Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27474 raw27474Labels permutation646 permutation2
    mixedMoment B raw27474step0 raw27474step0Labels = mixedMoment B raw27474step1 raw27474step1Labels := by
      have ha : raw27474step1 = -raw27474step0 := by apply Matrix.ext; change ∀ i j, raw27474step1 i j = -(raw27474step0 i j); unfold raw27474step1 raw27474step0; decide +kernel
      have hl : raw27474step1Labels = raw27474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2437 node2437Labels := by rfl

def raw27475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw27475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw27475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27475 raw27475Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw27475 raw27475Labels = mixedMoment B raw27475step0 raw27475step0Labels := by
      have hz : ∀ j, raw27475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27475step0 = (fun i j => raw27475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27475step0 raw27475; decide +kernel
      have hl : raw27475step0Labels = raw27475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27475 raw27475Labels permutation434 hz
    mixedMoment B raw27475step0 raw27475step0Labels = mixedMoment B raw27475step1 raw27475step1Labels := by
      have ha : raw27475step1 = (fun i j => raw27475step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27475step1 raw27475step0; decide +kernel
      have hl : raw27475step1Labels = raw27475step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27475step0 raw27475step0Labels permutation145 permutation2
    mixedMoment B raw27475step1 raw27475step1Labels = mixedMoment B raw27475step2 raw27475step2Labels := by
      have ha : raw27475step2 = -raw27475step1 := by apply Matrix.ext; change ∀ i j, raw27475step2 i j = -(raw27475step1 i j); unfold raw27475step2 raw27475step1; decide +kernel
      have hl : raw27475step2Labels = raw27475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw27476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw27476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw27476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27476step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw27476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27476 raw27476Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw27476 raw27476Labels = mixedMoment B raw27476step0 raw27476step0Labels := by
      have hz : ∀ j, raw27476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27476step0 = (fun i j => raw27476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27476step0 raw27476; decide +kernel
      have hl : raw27476step0Labels = raw27476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27476 raw27476Labels permutation434 hz
    mixedMoment B raw27476step0 raw27476step0Labels = mixedMoment B raw27476step1 raw27476step1Labels := by
      have ha : raw27476step1 = (fun i j => raw27476step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27476step1 raw27476step0; decide +kernel
      have hl : raw27476step1Labels = raw27476step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27476step0 raw27476step0Labels permutation34 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw27477 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27477step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27477step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27477 raw27477Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw27477 raw27477Labels = mixedMoment B raw27477step0 raw27477step0Labels := by
      have hz : ∀ j, raw27477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27477step0 = (fun i j => raw27477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27477step0 raw27477; decide +kernel
      have hl : raw27477step0Labels = raw27477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27477 raw27477Labels permutation434 hz
    mixedMoment B raw27477step0 raw27477step0Labels = mixedMoment B raw27477step1 raw27477step1Labels := by
      have ha : raw27477step1 = (fun i j => raw27477step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27477step1 raw27477step0; decide +kernel
      have hl : raw27477step1Labels = raw27477step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27477step0 raw27477step0Labels permutation39 permutation4
    mixedMoment B raw27477step1 raw27477step1Labels = mixedMoment B raw27477step2 raw27477step2Labels := by
      have ha : raw27477step2 = -raw27477step1 := by apply Matrix.ext; change ∀ i j, raw27477step2 i j = -(raw27477step1 i j); unfold raw27477step2 raw27477step1; decide +kernel
      have hl : raw27477step2Labels = raw27477step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw27478 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27478step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw27478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27478 raw27478Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw27478 raw27478Labels = mixedMoment B raw27478step0 raw27478step0Labels := by
      have hz : ∀ j, raw27478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27478step0 = (fun i j => raw27478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27478step0 raw27478; decide +kernel
      have hl : raw27478step0Labels = raw27478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27478 raw27478Labels permutation434 hz
    mixedMoment B raw27478step0 raw27478step0Labels = mixedMoment B raw27478step1 raw27478step1Labels := by
      have ha : raw27478step1 = (fun i j => raw27478step0 (permutation143 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27478step1 raw27478step0; decide +kernel
      have hl : raw27478step1Labels = raw27478step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27478step0 raw27478step0Labels permutation143 permutation2
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw27479 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27479 raw27479Labels = mixedMoment B node3385 node3385Labels := by
  calc
    mixedMoment B raw27479 raw27479Labels = mixedMoment B raw27479step0 raw27479step0Labels := by
      have hz : ∀ j, raw27479 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27479step0 = (fun i j => raw27479 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27479step0 raw27479; decide +kernel
      have hl : raw27479step0Labels = raw27479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27479 raw27479Labels permutation434 hz
    mixedMoment B raw27479step0 raw27479step0Labels = mixedMoment B raw27479step1 raw27479step1Labels := by
      have ha : raw27479step1 = (fun i j => raw27479step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27479step1 raw27479step0; decide +kernel
      have hl : raw27479step1Labels = raw27479step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27479step0 raw27479step0Labels permutation145 permutation2
    _ = mixedMoment B node3385 node3385Labels := by rfl

def raw27480 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw27480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27480step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27480 raw27480Labels = mixedMoment B node3443 node3443Labels := by
  calc
    mixedMoment B raw27480 raw27480Labels = mixedMoment B raw27480step0 raw27480step0Labels := by
      have ha : raw27480step0 = (fun i j => raw27480 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27480step0 raw27480; decide +kernel
      have hl : raw27480step0Labels = raw27480Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27480 raw27480Labels permutation164 permutation2
    mixedMoment B raw27480step0 raw27480step0Labels = mixedMoment B raw27480step1 raw27480step1Labels := by
      have ha : raw27480step1 = -raw27480step0 := by apply Matrix.ext; change ∀ i j, raw27480step1 i j = -(raw27480step0 i j); unfold raw27480step1 raw27480step0; decide +kernel
      have hl : raw27480step1Labels = raw27480step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3443 node3443Labels := by rfl

def raw27481 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27481Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27481step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw27481step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27481step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27481 raw27481Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw27481 raw27481Labels = mixedMoment B raw27481step0 raw27481step0Labels := by
      have hz : ∀ j, raw27481 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27481step0 = (fun i j => raw27481 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27481step0 raw27481; decide +kernel
      have hl : raw27481step0Labels = raw27481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27481 raw27481Labels permutation434 hz
    mixedMoment B raw27481step0 raw27481step0Labels = mixedMoment B raw27481step1 raw27481step1Labels := by
      have ha : raw27481step1 = (fun i j => raw27481step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27481step1 raw27481step0; decide +kernel
      have hl : raw27481step1Labels = raw27481step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27481step0 raw27481step0Labels permutation34 permutation2
    mixedMoment B raw27481step1 raw27481step1Labels = mixedMoment B raw27481step2 raw27481step2Labels := by
      have ha : raw27481step2 = -raw27481step1 := by apply Matrix.ext; change ∀ i j, raw27481step2 i j = -(raw27481step1 i j); unfold raw27481step2 raw27481step1; decide +kernel
      have hl : raw27481step2Labels = raw27481step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw27482 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27482Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27482step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw27482step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27482 raw27482Labels = mixedMoment B node2047 node2047Labels := by
  calc
    mixedMoment B raw27482 raw27482Labels = mixedMoment B raw27482step0 raw27482step0Labels := by
      have hz : ∀ j, raw27482 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27482step0 = (fun i j => raw27482 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27482step0 raw27482; decide +kernel
      have hl : raw27482step0Labels = raw27482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27482 raw27482Labels permutation434 hz
    mixedMoment B raw27482step0 raw27482step0Labels = mixedMoment B raw27482step1 raw27482step1Labels := by
      have ha : raw27482step1 = (fun i j => raw27482step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27482step1 raw27482step0; decide +kernel
      have hl : raw27482step1Labels = raw27482step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27482step0 raw27482step0Labels permutation145 permutation2
    _ = mixedMoment B node2047 node2047Labels := by rfl

def raw27483 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27483step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27483step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27483step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27483 raw27483Labels = mixedMoment B node2049 node2049Labels := by
  calc
    mixedMoment B raw27483 raw27483Labels = mixedMoment B raw27483step0 raw27483step0Labels := by
      have hz : ∀ j, raw27483 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27483step0 = (fun i j => raw27483 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27483step0 raw27483; decide +kernel
      have hl : raw27483step0Labels = raw27483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27483 raw27483Labels permutation434 hz
    mixedMoment B raw27483step0 raw27483step0Labels = mixedMoment B raw27483step1 raw27483step1Labels := by
      have ha : raw27483step1 = (fun i j => raw27483step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27483step1 raw27483step0; decide +kernel
      have hl : raw27483step1Labels = raw27483step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27483step0 raw27483step0Labels permutation39 permutation4
    mixedMoment B raw27483step1 raw27483step1Labels = mixedMoment B raw27483step2 raw27483step2Labels := by
      have ha : raw27483step2 = -raw27483step1 := by apply Matrix.ext; change ∀ i j, raw27483step2 i j = -(raw27483step1 i j); unfold raw27483step2 raw27483step1; decide +kernel
      have hl : raw27483step2Labels = raw27483step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2049 node2049Labels := by rfl

def raw27484 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27484Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw27484step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27484step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27484 raw27484Labels = mixedMoment B node1998 node1998Labels := by
  calc
    mixedMoment B raw27484 raw27484Labels = mixedMoment B raw27484step0 raw27484step0Labels := by
      have ha : raw27484step0 = (fun i j => raw27484 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27484step0 raw27484; decide +kernel
      have hl : raw27484step0Labels = raw27484Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27484 raw27484Labels permutation177 permutation4
    mixedMoment B raw27484step0 raw27484step0Labels = mixedMoment B raw27484step1 raw27484step1Labels := by
      have ha : raw27484step1 = -raw27484step0 := by apply Matrix.ext; change ∀ i j, raw27484step1 i j = -(raw27484step0 i j); unfold raw27484step1 raw27484step0; decide +kernel
      have hl : raw27484step1Labels = raw27484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1998 node1998Labels := by rfl

def raw27485 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw27485Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw27485step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw27485step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27485step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw27485step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27485 raw27485Labels = mixedMoment B node2004 node2004Labels := by
  calc
    mixedMoment B raw27485 raw27485Labels = mixedMoment B raw27485step0 raw27485step0Labels := by
      have hz : ∀ j, raw27485 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27485step0 = (fun i j => raw27485 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27485step0 raw27485; decide +kernel
      have hl : raw27485step0Labels = raw27485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27485 raw27485Labels permutation434 hz
    mixedMoment B raw27485step0 raw27485step0Labels = mixedMoment B raw27485step1 raw27485step1Labels := by
      have ha : raw27485step1 = (fun i j => raw27485step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27485step1 raw27485step0; decide +kernel
      have hl : raw27485step1Labels = raw27485step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27485step0 raw27485step0Labels permutation39 permutation4
    mixedMoment B raw27485step1 raw27485step1Labels = mixedMoment B raw27485step2 raw27485step2Labels := by
      have ha : raw27485step2 = -raw27485step1 := by apply Matrix.ext; change ∀ i j, raw27485step2 i j = -(raw27485step1 i j); unfold raw27485step2 raw27485step1; decide +kernel
      have hl : raw27485step2Labels = raw27485step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2004 node2004Labels := by rfl

def raw27486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27486step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, -1, 3]]
def raw27486step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27486step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw27486step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27486 raw27486Labels = mixedMoment B node2006 node2006Labels := by
  calc
    mixedMoment B raw27486 raw27486Labels = mixedMoment B raw27486step0 raw27486step0Labels := by
      have hz : ∀ j, raw27486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27486step0 = (fun i j => raw27486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27486step0 raw27486; decide +kernel
      have hl : raw27486step0Labels = raw27486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27486 raw27486Labels permutation434 hz
    mixedMoment B raw27486step0 raw27486step0Labels = mixedMoment B raw27486step1 raw27486step1Labels := by
      have ha : raw27486step1 = (fun i j => raw27486step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27486step1 raw27486step0; decide +kernel
      have hl : raw27486step1Labels = raw27486step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27486step0 raw27486step0Labels permutation38 permutation4
    mixedMoment B raw27486step1 raw27486step1Labels = mixedMoment B raw27486step2 raw27486step2Labels := by
      have ha : raw27486step2 = -raw27486step1 := by apply Matrix.ext; change ∀ i j, raw27486step2 i j = -(raw27486step1 i j); unfold raw27486step2 raw27486step1; decide +kernel
      have hl : raw27486step2Labels = raw27486step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2006 node2006Labels := by rfl

def raw27487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27487Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27487step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![-2, -1, 3]]
def raw27487step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27487step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27487step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27487step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27487 raw27487Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw27487 raw27487Labels = mixedMoment B raw27487step0 raw27487step0Labels := by
      have hz : ∀ j, raw27487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27487step0 = (fun i j => raw27487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27487step0 raw27487; decide +kernel
      have hl : raw27487step0Labels = raw27487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27487 raw27487Labels permutation434 hz
    mixedMoment B raw27487step0 raw27487step0Labels = mixedMoment B raw27487step1 raw27487step1Labels := by
      have hz : ∀ j, raw27487step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27487step1 = (fun i j => raw27487step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27487step1 raw27487step0; decide +kernel
      have hl : raw27487step1Labels = raw27487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27487step0 raw27487step0Labels permutation80 hz
    mixedMoment B raw27487step1 raw27487step1Labels = mixedMoment B raw27487step2 raw27487step2Labels := by
      have ha : raw27487step2 = (fun i j => raw27487step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27487step2 raw27487step1; decide +kernel
      have hl : raw27487step2Labels = raw27487step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27487step1 raw27487step1Labels permutation9 permutation4
    mixedMoment B raw27487step2 raw27487step2Labels = mixedMoment B raw27487step3 raw27487step3Labels := by
      have ha : raw27487step3 = -raw27487step2 := by apply Matrix.ext; change ∀ i j, raw27487step3 i j = -(raw27487step2 i j); unfold raw27487step3 raw27487step2; decide +kernel
      have hl : raw27487step3Labels = raw27487step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3486 node3486Labels := by rfl

def raw27488 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27488Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw27488step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27488step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27488 raw27488Labels = mixedMoment B node3434 node3434Labels := by
  calc
    mixedMoment B raw27488 raw27488Labels = mixedMoment B raw27488step0 raw27488step0Labels := by
      have ha : raw27488step0 = (fun i j => raw27488 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27488step0 raw27488; decide +kernel
      have hl : raw27488step0Labels = raw27488Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27488 raw27488Labels permutation153 permutation4
    mixedMoment B raw27488step0 raw27488step0Labels = mixedMoment B raw27488step1 raw27488step1Labels := by
      have ha : raw27488step1 = -raw27488step0 := by apply Matrix.ext; change ∀ i j, raw27488step1 i j = -(raw27488step0 i j); unfold raw27488step1 raw27488step0; decide +kernel
      have hl : raw27488step1Labels = raw27488step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3434 node3434Labels := by rfl

def raw27489 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw27489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, -1, 3]]
def raw27489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27489step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27489 raw27489Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw27489 raw27489Labels = mixedMoment B raw27489step0 raw27489step0Labels := by
      have hz : ∀ j, raw27489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27489step0 = (fun i j => raw27489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27489step0 raw27489; decide +kernel
      have hl : raw27489step0Labels = raw27489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27489 raw27489Labels permutation434 hz
    mixedMoment B raw27489step0 raw27489step0Labels = mixedMoment B raw27489step1 raw27489step1Labels := by
      have ha : raw27489step1 = (fun i j => raw27489step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27489step1 raw27489step0; decide +kernel
      have hl : raw27489step1Labels = raw27489step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27489step0 raw27489step0Labels permutation127 permutation4
    _ = mixedMoment B node2837 node2837Labels := by rfl

def raw27490 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27490Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27490step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27490step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27490 raw27490Labels = mixedMoment B node3353 node3353Labels := by
  calc
    mixedMoment B raw27490 raw27490Labels = mixedMoment B raw27490step0 raw27490step0Labels := by
      have hz : ∀ j, raw27490 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27490step0 = (fun i j => raw27490 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27490step0 raw27490; decide +kernel
      have hl : raw27490step0Labels = raw27490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27490 raw27490Labels permutation434 hz
    mixedMoment B raw27490step0 raw27490step0Labels = mixedMoment B raw27490step1 raw27490step1Labels := by
      have ha : raw27490step1 = (fun i j => raw27490step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27490step1 raw27490step0; decide +kernel
      have hl : raw27490step1Labels = raw27490step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27490step0 raw27490step0Labels permutation151 permutation4
    _ = mixedMoment B node3353 node3353Labels := by rfl

def raw27491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27491Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27491step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27491step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27491 raw27491Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw27491 raw27491Labels = mixedMoment B raw27491step0 raw27491step0Labels := by
      have hz : ∀ j, raw27491 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27491step0 = (fun i j => raw27491 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27491step0 raw27491; decide +kernel
      have hl : raw27491step0Labels = raw27491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27491 raw27491Labels permutation434 hz
    mixedMoment B raw27491step0 raw27491step0Labels = mixedMoment B raw27491step1 raw27491step1Labels := by
      have ha : raw27491step1 = (fun i j => raw27491step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27491step1 raw27491step0; decide +kernel
      have hl : raw27491step1Labels = raw27491step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27491step0 raw27491step0Labels permutation144 permutation2
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw27492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-2, -1, 3]]
def raw27492step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27492step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27492 raw27492Labels = mixedMoment B node3615 node3615Labels := by
  calc
    mixedMoment B raw27492 raw27492Labels = mixedMoment B raw27492step0 raw27492step0Labels := by
      have hz : ∀ j, raw27492 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27492step0 = (fun i j => raw27492 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27492step0 raw27492; decide +kernel
      have hl : raw27492step0Labels = raw27492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27492 raw27492Labels permutation434 hz
    mixedMoment B raw27492step0 raw27492step0Labels = mixedMoment B raw27492step1 raw27492step1Labels := by
      have hz : ∀ j, raw27492step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27492step1 = (fun i j => raw27492step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27492step1 raw27492step0; decide +kernel
      have hl : raw27492step1Labels = raw27492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27492step0 raw27492step0Labels permutation80 hz
    mixedMoment B raw27492step1 raw27492step1Labels = mixedMoment B raw27492step2 raw27492step2Labels := by
      have ha : raw27492step2 = (fun i j => raw27492step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27492step2 raw27492step1; decide +kernel
      have hl : raw27492step2Labels = raw27492step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27492step1 raw27492step1Labels permutation31 permutation2
    _ = mixedMoment B node3615 node3615Labels := by rfl

def raw27493 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27493Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27493step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27493 raw27493Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw27493 raw27493Labels = mixedMoment B raw27493step0 raw27493step0Labels := by
      have ha : raw27493step0 = (fun i j => raw27493 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27493step0 raw27493; decide +kernel
      have hl : raw27493step0Labels = raw27493Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27493 raw27493Labels permutation646 permutation2
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw27494 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27494Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27494 raw27494Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw27494 raw27494Labels = mixedMoment B raw27494step0 raw27494step0Labels := by
      have hz : ∀ j, raw27494 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27494step0 = (fun i j => raw27494 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27494step0 raw27494; decide +kernel
      have hl : raw27494step0Labels = raw27494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27494 raw27494Labels permutation434 hz
    mixedMoment B raw27494step0 raw27494step0Labels = mixedMoment B raw27494step1 raw27494step1Labels := by
      have ha : raw27494step1 = (fun i j => raw27494step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27494step1 raw27494step0; decide +kernel
      have hl : raw27494step1Labels = raw27494step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27494step0 raw27494step0Labels permutation149 permutation4
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw27495 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw27495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27495 raw27495Labels = mixedMoment B node3343 node3343Labels := by
  calc
    mixedMoment B raw27495 raw27495Labels = mixedMoment B raw27495step0 raw27495step0Labels := by
      have hz : ∀ j, raw27495 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27495step0 = (fun i j => raw27495 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27495step0 raw27495; decide +kernel
      have hl : raw27495step0Labels = raw27495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27495 raw27495Labels permutation434 hz
    mixedMoment B raw27495step0 raw27495step0Labels = mixedMoment B raw27495step1 raw27495step1Labels := by
      have ha : raw27495step1 = (fun i j => raw27495step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27495step1 raw27495step0; decide +kernel
      have hl : raw27495step1Labels = raw27495step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27495step0 raw27495step0Labels permutation149 permutation4
    _ = mixedMoment B node3343 node3343Labels := by rfl

def raw27496 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw27496Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27496 raw27496Labels = mixedMoment B node3339 node3339Labels := by
  calc
    mixedMoment B raw27496 raw27496Labels = mixedMoment B raw27496step0 raw27496step0Labels := by
      have ha : raw27496step0 = (fun i j => raw27496 (permutation674 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27496step0 raw27496; decide +kernel
      have hl : raw27496step0Labels = raw27496Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27496 raw27496Labels permutation674 permutation4
    _ = mixedMoment B node3339 node3339Labels := by rfl

def raw27497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw27497Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw27497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw27497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw27497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27497 raw27497Labels = mixedMoment B node2121 node2121Labels := by
  calc
    mixedMoment B raw27497 raw27497Labels = mixedMoment B raw27497step0 raw27497step0Labels := by
      have hz : ∀ j, raw27497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27497step0 = (fun i j => raw27497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27497step0 raw27497; decide +kernel
      have hl : raw27497step0Labels = raw27497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27497 raw27497Labels permutation434 hz
    mixedMoment B raw27497step0 raw27497step0Labels = mixedMoment B raw27497step1 raw27497step1Labels := by
      have ha : raw27497step1 = (fun i j => raw27497step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27497step1 raw27497step0; decide +kernel
      have hl : raw27497step1Labels = raw27497step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27497step0 raw27497step0Labels permutation151 permutation2
    mixedMoment B raw27497step1 raw27497step1Labels = mixedMoment B raw27497step2 raw27497step2Labels := by
      have ha : raw27497step2 = -raw27497step1 := by apply Matrix.ext; change ∀ i j, raw27497step2 i j = -(raw27497step1 i j); unfold raw27497step2 raw27497step1; decide +kernel
      have hl : raw27497step2Labels = raw27497step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2121 node2121Labels := by rfl

def raw27498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw27498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![3, 0, -3]]
def raw27498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw27498step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27498step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw27498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27498 raw27498Labels = mixedMoment B node2123 node2123Labels := by
  calc
    mixedMoment B raw27498 raw27498Labels = mixedMoment B raw27498step0 raw27498step0Labels := by
      have hz : ∀ j, raw27498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27498step0 = (fun i j => raw27498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27498step0 raw27498; decide +kernel
      have hl : raw27498step0Labels = raw27498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27498 raw27498Labels permutation434 hz
    mixedMoment B raw27498step0 raw27498step0Labels = mixedMoment B raw27498step1 raw27498step1Labels := by
      have ha : raw27498step1 = (fun i j => raw27498step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27498step1 raw27498step0; decide +kernel
      have hl : raw27498step1Labels = raw27498step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27498step0 raw27498step0Labels permutation150 permutation2
    mixedMoment B raw27498step1 raw27498step1Labels = mixedMoment B raw27498step2 raw27498step2Labels := by
      have ha : raw27498step2 = -raw27498step1 := by apply Matrix.ext; change ∀ i j, raw27498step2 i j = -(raw27498step1 i j); unfold raw27498step2 raw27498step1; decide +kernel
      have hl : raw27498step2Labels = raw27498step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2123 node2123Labels := by rfl

def raw27499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw27499Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -3, 2], ![3, 0, -3]]
def raw27499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27499step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw27499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27499 raw27499Labels = mixedMoment B node2129 node2129Labels := by
  calc
    mixedMoment B raw27499 raw27499Labels = mixedMoment B raw27499step0 raw27499step0Labels := by
      have hz : ∀ j, raw27499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27499step0 = (fun i j => raw27499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27499step0 raw27499; decide +kernel
      have hl : raw27499step0Labels = raw27499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27499 raw27499Labels permutation434 hz
    mixedMoment B raw27499step0 raw27499step0Labels = mixedMoment B raw27499step1 raw27499step1Labels := by
      have ha : raw27499step1 = (fun i j => raw27499step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27499step1 raw27499step0; decide +kernel
      have hl : raw27499step1Labels = raw27499step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27499step0 raw27499step0Labels permutation151 permutation2
    mixedMoment B raw27499step1 raw27499step1Labels = mixedMoment B raw27499step2 raw27499step2Labels := by
      have ha : raw27499step2 = -raw27499step1 := by apply Matrix.ext; change ∀ i j, raw27499step2 i j = -(raw27499step1 i j); unfold raw27499step2 raw27499step1; decide +kernel
      have hl : raw27499step2Labels = raw27499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2129 node2129Labels := by rfl

def raw27500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw27500Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27500step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27500 raw27500Labels = mixedMoment B node2118 node2118Labels := by
  calc
    mixedMoment B raw27500 raw27500Labels = mixedMoment B raw27500step0 raw27500step0Labels := by
      have ha : raw27500step0 = (fun i j => raw27500 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27500step0 raw27500; decide +kernel
      have hl : raw27500step0Labels = raw27500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27500 raw27500Labels permutation682 permutation2
    mixedMoment B raw27500step0 raw27500step0Labels = mixedMoment B raw27500step1 raw27500step1Labels := by
      have ha : raw27500step1 = -raw27500step0 := by apply Matrix.ext; change ∀ i j, raw27500step1 i j = -(raw27500step0 i j); unfold raw27500step1 raw27500step0; decide +kernel
      have hl : raw27500step1Labels = raw27500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2118 node2118Labels := by rfl

def raw27501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw27501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw27501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27501step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27501 raw27501Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw27501 raw27501Labels = mixedMoment B raw27501step0 raw27501step0Labels := by
      have hz : ∀ j, raw27501 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27501step0 = (fun i j => raw27501 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27501step0 raw27501; decide +kernel
      have hl : raw27501step0Labels = raw27501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27501 raw27501Labels permutation434 hz
    mixedMoment B raw27501step0 raw27501step0Labels = mixedMoment B raw27501step1 raw27501step1Labels := by
      have ha : raw27501step1 = (fun i j => raw27501step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27501step1 raw27501step0; decide +kernel
      have hl : raw27501step1Labels = raw27501step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27501step0 raw27501step0Labels permutation145 permutation2
    mixedMoment B raw27501step1 raw27501step1Labels = mixedMoment B raw27501step2 raw27501step2Labels := by
      have ha : raw27501step2 = -raw27501step1 := by apply Matrix.ext; change ∀ i j, raw27501step2 i j = -(raw27501step1 i j); unfold raw27501step2 raw27501step1; decide +kernel
      have hl : raw27501step2Labels = raw27501step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw27502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw27502Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw27502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27502step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27502 raw27502Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw27502 raw27502Labels = mixedMoment B raw27502step0 raw27502step0Labels := by
      have hz : ∀ j, raw27502 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27502step0 = (fun i j => raw27502 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27502step0 raw27502; decide +kernel
      have hl : raw27502step0Labels = raw27502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27502 raw27502Labels permutation434 hz
    mixedMoment B raw27502step0 raw27502step0Labels = mixedMoment B raw27502step1 raw27502step1Labels := by
      have ha : raw27502step1 = (fun i j => raw27502step0 (permutation110 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27502step1 raw27502step0; decide +kernel
      have hl : raw27502step1Labels = raw27502step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27502step0 raw27502step0Labels permutation110 permutation4
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw27503 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![-2, 2], ![3, -3]]
def raw27503Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27503step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-2, 2], ![3, -3]]
def raw27503step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27503step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw27503step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27503step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw27503step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27503 raw27503Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw27503 raw27503Labels = mixedMoment B raw27503step0 raw27503step0Labels := by
      have hz : ∀ j, raw27503 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27503step0 = (fun i j => raw27503 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27503step0 raw27503; decide +kernel
      have hl : raw27503step0Labels = raw27503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27503 raw27503Labels permutation434 hz
    mixedMoment B raw27503step0 raw27503step0Labels = mixedMoment B raw27503step1 raw27503step1Labels := by
      have ha : raw27503step1 = (fun i j => raw27503step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27503step1 raw27503step0; decide +kernel
      have hl : raw27503step1Labels = raw27503step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27503step0 raw27503step0Labels permutation140 permutation0
    mixedMoment B raw27503step1 raw27503step1Labels = mixedMoment B raw27503step2 raw27503step2Labels := by
      have ha : raw27503step2 = -raw27503step1 := by apply Matrix.ext; change ∀ i j, raw27503step2 i j = -(raw27503step1 i j); unfold raw27503step2 raw27503step1; decide +kernel
      have hl : raw27503step2Labels = raw27503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw27504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw27504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27504step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27504 raw27504Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw27504 raw27504Labels = mixedMoment B raw27504step0 raw27504step0Labels := by
      have ha : raw27504step0 = (fun i j => raw27504 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27504step0 raw27504; decide +kernel
      have hl : raw27504step0Labels = raw27504Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27504 raw27504Labels permutation686 permutation2
    mixedMoment B raw27504step0 raw27504step0Labels = mixedMoment B raw27504step1 raw27504step1Labels := by
      have ha : raw27504step1 = -raw27504step0 := by apply Matrix.ext; change ∀ i j, raw27504step1 i j = -(raw27504step0 i j); unfold raw27504step1 raw27504step0; decide +kernel
      have hl : raw27504step1Labels = raw27504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw27505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27505Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27505 raw27505Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw27505 raw27505Labels = mixedMoment B raw27505step0 raw27505step0Labels := by
      have hz : ∀ j, raw27505 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27505step0 = (fun i j => raw27505 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27505step0 raw27505; decide +kernel
      have hl : raw27505step0Labels = raw27505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27505 raw27505Labels permutation265 hz
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw27506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27506Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27506 raw27506Labels = mixedMoment B node2542 node2542Labels := by
  calc
    _ = mixedMoment B node2542 node2542Labels := by rfl

def raw27507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw27507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27507 raw27507Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw27507 raw27507Labels = mixedMoment B raw27507step0 raw27507step0Labels := by
      have ha : raw27507step0 = (fun i j => raw27507 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27507step0 raw27507; decide +kernel
      have hl : raw27507step0Labels = raw27507Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27507 raw27507Labels permutation178 permutation2
    _ = mixedMoment B node2425 node2425Labels := by rfl

def raw27508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw27508Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27508 raw27508Labels = mixedMoment B node2347 node2347Labels := by
  calc
    mixedMoment B raw27508 raw27508Labels = mixedMoment B raw27508step0 raw27508step0Labels := by
      have ha : raw27508step0 = (fun i j => raw27508 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27508step0 raw27508; decide +kernel
      have hl : raw27508step0Labels = raw27508Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27508 raw27508Labels permutation686 permutation2
    mixedMoment B raw27508step0 raw27508step0Labels = mixedMoment B raw27508step1 raw27508step1Labels := by
      have ha : raw27508step1 = -raw27508step0 := by apply Matrix.ext; change ∀ i j, raw27508step1 i j = -(raw27508step0 i j); unfold raw27508step1 raw27508step0; decide +kernel
      have hl : raw27508step1Labels = raw27508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2347 node2347Labels := by rfl

def raw27509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw27509Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw27509step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw27509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27509 raw27509Labels = mixedMoment B node1148 node1148Labels := by
  calc
    mixedMoment B raw27509 raw27509Labels = mixedMoment B raw27509step0 raw27509step0Labels := by
      have ha : raw27509step0 = (fun i j => raw27509 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27509step0 raw27509; decide +kernel
      have hl : raw27509step0Labels = raw27509Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27509 raw27509Labels permutation686 permutation2
    mixedMoment B raw27509step0 raw27509step0Labels = mixedMoment B raw27509step1 raw27509step1Labels := by
      have ha : raw27509step1 = -raw27509step0 := by apply Matrix.ext; change ∀ i j, raw27509step1 i j = -(raw27509step0 i j); unfold raw27509step1 raw27509step0; decide +kernel
      have hl : raw27509step1Labels = raw27509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1148 node1148Labels := by rfl

def raw27510 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27510 raw27510Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw27510 raw27510Labels = mixedMoment B raw27510step0 raw27510step0Labels := by
      have ha : raw27510step0 = (fun i j => raw27510 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27510step0 raw27510; decide +kernel
      have hl : raw27510step0Labels = raw27510Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27510 raw27510Labels permutation662 permutation4
    _ = mixedMoment B node3513 node3513Labels := by rfl

def raw27511 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27511 raw27511Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw27511 raw27511Labels = mixedMoment B raw27511step0 raw27511step0Labels := by
      have ha : raw27511step0 = (fun i j => raw27511 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27511step0 raw27511; decide +kernel
      have hl : raw27511step0Labels = raw27511Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27511 raw27511Labels permutation200 permutation2
    mixedMoment B raw27511step0 raw27511step0Labels = mixedMoment B raw27511step1 raw27511step1Labels := by
      have ha : raw27511step1 = -raw27511step0 := by apply Matrix.ext; change ∀ i j, raw27511step1 i j = -(raw27511step0 i j); unfold raw27511step1 raw27511step0; decide +kernel
      have hl : raw27511step1Labels = raw27511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw27512 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw27512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27512step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27512 raw27512Labels = mixedMoment B node3437 node3437Labels := by
  calc
    mixedMoment B raw27512 raw27512Labels = mixedMoment B raw27512step0 raw27512step0Labels := by
      have ha : raw27512step0 = (fun i j => raw27512 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27512step0 raw27512; decide +kernel
      have hl : raw27512step0Labels = raw27512Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27512 raw27512Labels permutation161 permutation2
    mixedMoment B raw27512step0 raw27512step0Labels = mixedMoment B raw27512step1 raw27512step1Labels := by
      have ha : raw27512step1 = -raw27512step0 := by apply Matrix.ext; change ∀ i j, raw27512step1 i j = -(raw27512step0 i j); unfold raw27512step1 raw27512step0; decide +kernel
      have hl : raw27512step1Labels = raw27512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3437 node3437Labels := by rfl

def raw27513 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27513 raw27513Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27513 raw27513Labels = mixedMoment B raw27513step0 raw27513step0Labels := by
      have hz : ∀ j, raw27513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27513step0 = (fun i j => raw27513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27513step0 raw27513; decide +kernel
      have hl : raw27513step0Labels = raw27513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27513 raw27513Labels permutation434 hz
    mixedMoment B raw27513step0 raw27513step0Labels = mixedMoment B raw27513step1 raw27513step1Labels := by
      have ha : raw27513step1 = -raw27513step0 := by apply Matrix.ext; change ∀ i j, raw27513step1 i j = -(raw27513step0 i j); unfold raw27513step1 raw27513step0; decide +kernel
      have hl : raw27513step1Labels = raw27513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw27514 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw27514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw27514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27514 raw27514Labels = mixedMoment B node3434 node3434Labels := by
  calc
    mixedMoment B raw27514 raw27514Labels = mixedMoment B raw27514step0 raw27514step0Labels := by
      have ha : raw27514step0 = (fun i j => raw27514 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27514step0 raw27514; decide +kernel
      have hl : raw27514step0Labels = raw27514Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27514 raw27514Labels permutation159 permutation2
    mixedMoment B raw27514step0 raw27514step0Labels = mixedMoment B raw27514step1 raw27514step1Labels := by
      have ha : raw27514step1 = -raw27514step0 := by apply Matrix.ext; change ∀ i j, raw27514step1 i j = -(raw27514step0 i j); unfold raw27514step1 raw27514step0; decide +kernel
      have hl : raw27514step1Labels = raw27514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3434 node3434Labels := by rfl

def raw27515 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27515 raw27515Labels = mixedMoment B node3432 node3432Labels := by
  calc
    mixedMoment B raw27515 raw27515Labels = mixedMoment B raw27515step0 raw27515step0Labels := by
      have ha : raw27515step0 = (fun i j => raw27515 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27515step0 raw27515; decide +kernel
      have hl : raw27515step0Labels = raw27515Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27515 raw27515Labels permutation682 permutation2
    _ = mixedMoment B node3432 node3432Labels := by rfl

def raw27516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, -1, 3]]
def raw27516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw27516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27516 raw27516Labels = mixedMoment B node2015 node2015Labels := by
  calc
    mixedMoment B raw27516 raw27516Labels = mixedMoment B raw27516step0 raw27516step0Labels := by
      have ha : raw27516step0 = (fun i j => raw27516 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27516step0 raw27516; decide +kernel
      have hl : raw27516step0Labels = raw27516Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27516 raw27516Labels permutation188 permutation4
    mixedMoment B raw27516step0 raw27516step0Labels = mixedMoment B raw27516step1 raw27516step1Labels := by
      have ha : raw27516step1 = -raw27516step0 := by apply Matrix.ext; change ∀ i j, raw27516step1 i j = -(raw27516step0 i j); unfold raw27516step1 raw27516step0; decide +kernel
      have hl : raw27516step1Labels = raw27516step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2015 node2015Labels := by rfl

def raw27517 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw27517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw27517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27517 raw27517Labels = mixedMoment B node1989 node1989Labels := by
  calc
    mixedMoment B raw27517 raw27517Labels = mixedMoment B raw27517step0 raw27517step0Labels := by
      have ha : raw27517step0 = (fun i j => raw27517 (permutation178 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27517step0 raw27517; decide +kernel
      have hl : raw27517step0Labels = raw27517Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27517 raw27517Labels permutation178 permutation4
    mixedMoment B raw27517step0 raw27517step0Labels = mixedMoment B raw27517step1 raw27517step1Labels := by
      have ha : raw27517step1 = -raw27517step0 := by apply Matrix.ext; change ∀ i j, raw27517step1 i j = -(raw27517step0 i j); unfold raw27517step1 raw27517step0; decide +kernel
      have hl : raw27517step1Labels = raw27517step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1989 node1989Labels := by rfl

def raw27518 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw27518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27518 raw27518Labels = mixedMoment B node1996 node1996Labels := by
  calc
    mixedMoment B raw27518 raw27518Labels = mixedMoment B raw27518step0 raw27518step0Labels := by
      have ha : raw27518step0 = (fun i j => raw27518 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27518step0 raw27518; decide +kernel
      have hl : raw27518step0Labels = raw27518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27518 raw27518Labels permutation176 permutation4
    mixedMoment B raw27518step0 raw27518step0Labels = mixedMoment B raw27518step1 raw27518step1Labels := by
      have ha : raw27518step1 = -raw27518step0 := by apply Matrix.ext; change ∀ i j, raw27518step1 i j = -(raw27518step0 i j); unfold raw27518step1 raw27518step0; decide +kernel
      have hl : raw27518step1Labels = raw27518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1996 node1996Labels := by rfl

def raw27519 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw27519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw27519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27519 raw27519Labels = mixedMoment B node1986 node1986Labels := by
  calc
    mixedMoment B raw27519 raw27519Labels = mixedMoment B raw27519step0 raw27519step0Labels := by
      have ha : raw27519step0 = (fun i j => raw27519 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27519step0 raw27519; decide +kernel
      have hl : raw27519step0Labels = raw27519Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27519 raw27519Labels permutation662 permutation4
    _ = mixedMoment B node1986 node1986Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
