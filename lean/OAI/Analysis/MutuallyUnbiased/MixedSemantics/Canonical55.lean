import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-3, 2, 1]]
def raw7040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -2, -1]]
def raw7040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7040 raw7040Labels = mixedMoment B node2579 node2579Labels := by
  calc
    mixedMoment B raw7040 raw7040Labels = mixedMoment B raw7040step0 raw7040step0Labels := by
      have hz : ∀ j, raw7040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7040step0 = (fun i j => raw7040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7040step0 raw7040; decide +kernel
      have hl : raw7040step0Labels = raw7040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7040 raw7040Labels permutation346 hz
    mixedMoment B raw7040step0 raw7040step0Labels = mixedMoment B raw7040step1 raw7040step1Labels := by
      have ha : raw7040step1 = (fun i j => raw7040step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7040step1 raw7040step0; decide +kernel
      have hl : raw7040step1Labels = raw7040step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7040step0 raw7040step0Labels permutation151 permutation2
    mixedMoment B raw7040step1 raw7040step1Labels = mixedMoment B raw7040step2 raw7040step2Labels := by
      have ha : raw7040step2 = -raw7040step1 := by apply Matrix.ext; change ∀ i j, raw7040step2 i j = -(raw7040step1 i j); unfold raw7040step2 raw7040step1; decide +kernel
      have hl : raw7040step2Labels = raw7040step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2579 node2579Labels := by rfl

def raw7041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7041 raw7041Labels = mixedMoment B node2861 node2861Labels := by
  calc
    mixedMoment B raw7041 raw7041Labels = mixedMoment B raw7041step0 raw7041step0Labels := by
      have ha : raw7041step0 = (fun i j => raw7041 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7041step0 raw7041; decide +kernel
      have hl : raw7041step0Labels = raw7041Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7041 raw7041Labels permutation200 permutation2
    _ = mixedMoment B node2861 node2861Labels := by rfl

def raw7042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 0, 0], ![2, 0, -2]]
def raw7042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw7042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7042 raw7042Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw7042 raw7042Labels = mixedMoment B raw7042step0 raw7042step0Labels := by
      have hz : ∀ j, raw7042 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7042step0 = (fun i j => raw7042 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7042step0 raw7042; decide +kernel
      have hl : raw7042step0Labels = raw7042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7042 raw7042Labels permutation520 hz
    mixedMoment B raw7042step0 raw7042step0Labels = mixedMoment B raw7042step1 raw7042step1Labels := by
      have ha : raw7042step1 = (fun i j => raw7042step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7042step1 raw7042step0; decide +kernel
      have hl : raw7042step1Labels = raw7042step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7042step0 raw7042step0Labels permutation44 permutation2
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw7043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2]]
def raw7043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7043 raw7043Labels = mixedMoment B node3036 node3036Labels := by
  calc
    mixedMoment B raw7043 raw7043Labels = mixedMoment B raw7043step0 raw7043step0Labels := by
      have ha : raw7043step0 = (fun i j => raw7043 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7043step0 raw7043; decide +kernel
      have hl : raw7043step0Labels = raw7043Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7043 raw7043Labels permutation200 permutation2
    _ = mixedMoment B node3036 node3036Labels := by rfl

def raw7044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw7044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7044 raw7044Labels = mixedMoment B node2580 node2580Labels := by
  calc
    mixedMoment B raw7044 raw7044Labels = mixedMoment B raw7044step0 raw7044step0Labels := by
      have ha : raw7044step0 = (fun i j => raw7044 (permutation504 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7044step0 raw7044; decide +kernel
      have hl : raw7044step0Labels = raw7044Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7044 raw7044Labels permutation504 permutation4
    _ = mixedMoment B node2580 node2580Labels := by rfl

def raw7045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7045 raw7045Labels = mixedMoment B node2971 node2971Labels := by
  calc
    mixedMoment B raw7045 raw7045Labels = mixedMoment B raw7045step0 raw7045step0Labels := by
      have ha : raw7045step0 = (fun i j => raw7045 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7045step0 raw7045; decide +kernel
      have hl : raw7045step0Labels = raw7045Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7045 raw7045Labels permutation182 permutation2
    _ = mixedMoment B node2971 node2971Labels := by rfl

def raw7046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7046Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw7046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw7046step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7046 raw7046Labels = mixedMoment B node2547 node2547Labels := by
  calc
    mixedMoment B raw7046 raw7046Labels = mixedMoment B raw7046step0 raw7046step0Labels := by
      have ha : raw7046step0 = (fun i j => raw7046 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7046step0 raw7046; decide +kernel
      have hl : raw7046step0Labels = raw7046Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7046 raw7046Labels permutation676 permutation2
    mixedMoment B raw7046step0 raw7046step0Labels = mixedMoment B raw7046step1 raw7046step1Labels := by
      have ha : raw7046step1 = -raw7046step0 := by apply Matrix.ext; change ∀ i j, raw7046step1 i j = -(raw7046step0 i j); unfold raw7046step1 raw7046step0; decide +kernel
      have hl : raw7046step1Labels = raw7046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2547 node2547Labels := by rfl

def raw7047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw7047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7047 raw7047Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw7047 raw7047Labels = mixedMoment B raw7047step0 raw7047step0Labels := by
      have hz : ∀ j, raw7047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7047step0 = (fun i j => raw7047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7047step0 raw7047; decide +kernel
      have hl : raw7047step0Labels = raw7047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7047 raw7047Labels permutation346 hz
    mixedMoment B raw7047step0 raw7047step0Labels = mixedMoment B raw7047step1 raw7047step1Labels := by
      have ha : raw7047step1 = (fun i j => raw7047step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7047step1 raw7047step0; decide +kernel
      have hl : raw7047step1Labels = raw7047step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7047step0 raw7047step0Labels permutation38 permutation2
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw7048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw7048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw7048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7048 raw7048Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw7048 raw7048Labels = mixedMoment B raw7048step0 raw7048step0Labels := by
      have hz : ∀ j, raw7048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7048step0 = (fun i j => raw7048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7048step0 raw7048; decide +kernel
      have hl : raw7048step0Labels = raw7048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7048 raw7048Labels permutation346 hz
    mixedMoment B raw7048step0 raw7048step0Labels = mixedMoment B raw7048step1 raw7048step1Labels := by
      have ha : raw7048step1 = (fun i j => raw7048step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7048step1 raw7048step0; decide +kernel
      have hl : raw7048step1Labels = raw7048step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7048step0 raw7048step0Labels permutation149 permutation2
    mixedMoment B raw7048step1 raw7048step1Labels = mixedMoment B raw7048step2 raw7048step2Labels := by
      have ha : raw7048step2 = -raw7048step1 := by apply Matrix.ext; change ∀ i j, raw7048step2 i j = -(raw7048step1 i j); unfold raw7048step2 raw7048step1; decide +kernel
      have hl : raw7048step2Labels = raw7048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw7049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw7049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw7049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7049 raw7049Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw7049 raw7049Labels = mixedMoment B raw7049step0 raw7049step0Labels := by
      have hz : ∀ j, raw7049 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7049step0 = (fun i j => raw7049 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7049step0 raw7049; decide +kernel
      have hl : raw7049step0Labels = raw7049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7049 raw7049Labels permutation346 hz
    mixedMoment B raw7049step0 raw7049step0Labels = mixedMoment B raw7049step1 raw7049step1Labels := by
      have ha : raw7049step1 = (fun i j => raw7049step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7049step1 raw7049step0; decide +kernel
      have hl : raw7049step1Labels = raw7049step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7049step0 raw7049step0Labels permutation39 permutation2
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw7050 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7050step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7050step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7050 raw7050Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw7050 raw7050Labels = mixedMoment B raw7050step0 raw7050step0Labels := by
      have hz : ∀ j, raw7050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7050step0 = (fun i j => raw7050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7050step0 raw7050; decide +kernel
      have hl : raw7050step0Labels = raw7050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7050 raw7050Labels permutation346 hz
    mixedMoment B raw7050step0 raw7050step0Labels = mixedMoment B raw7050step1 raw7050step1Labels := by
      have ha : raw7050step1 = (fun i j => raw7050step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7050step1 raw7050step0; decide +kernel
      have hl : raw7050step1Labels = raw7050step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7050step0 raw7050step0Labels permutation38 permutation7
    mixedMoment B raw7050step1 raw7050step1Labels = mixedMoment B raw7050step2 raw7050step2Labels := by
      have ha : raw7050step2 = raw7050step1 := by apply Matrix.ext; unfold raw7050step2 raw7050step1; decide +kernel
      have hl : raw7050step1Labels = labelEmbedding10 ∘ raw7050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7050step1 raw7050step1Labels raw7050step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw7051 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7051step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7051step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7051 raw7051Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw7051 raw7051Labels = mixedMoment B raw7051step0 raw7051step0Labels := by
      have ha : raw7051step0 = (fun i j => raw7051 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7051step0 raw7051; decide +kernel
      have hl : raw7051step0Labels = raw7051Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7051 raw7051Labels permutation200 permutation7
    mixedMoment B raw7051step0 raw7051step0Labels = mixedMoment B raw7051step1 raw7051step1Labels := by
      have ha : raw7051step1 = raw7051step0 := by apply Matrix.ext; unfold raw7051step1 raw7051step0; decide +kernel
      have hl : raw7051step0Labels = labelEmbedding10 ∘ raw7051step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7051step0 raw7051step0Labels raw7051step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw7052 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7052step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7052 raw7052Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw7052 raw7052Labels = mixedMoment B raw7052step0 raw7052step0Labels := by
      have hz : ∀ j, raw7052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7052step0 = (fun i j => raw7052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7052step0 raw7052; decide +kernel
      have hl : raw7052step0Labels = raw7052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7052 raw7052Labels permutation346 hz
    mixedMoment B raw7052step0 raw7052step0Labels = mixedMoment B raw7052step1 raw7052step1Labels := by
      have ha : raw7052step1 = (fun i j => raw7052step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7052step1 raw7052step0; decide +kernel
      have hl : raw7052step1Labels = raw7052step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7052step0 raw7052step0Labels permutation139 permutation2
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw7053 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw7053step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7053step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7053step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7053step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7053 raw7053Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw7053 raw7053Labels = mixedMoment B raw7053step0 raw7053step0Labels := by
      have hz : ∀ j, raw7053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7053step0 = (fun i j => raw7053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7053step0 raw7053; decide +kernel
      have hl : raw7053step0Labels = raw7053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7053 raw7053Labels permutation346 hz
    mixedMoment B raw7053step0 raw7053step0Labels = mixedMoment B raw7053step1 raw7053step1Labels := by
      have hz : ∀ j, raw7053step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7053step1 = (fun i j => raw7053step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7053step1 raw7053step0; decide +kernel
      have hl : raw7053step1Labels = raw7053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7053step0 raw7053step0Labels permutation56 hz
    mixedMoment B raw7053step1 raw7053step1Labels = mixedMoment B raw7053step2 raw7053step2Labels := by
      have ha : raw7053step2 = (fun i j => raw7053step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7053step2 raw7053step1; decide +kernel
      have hl : raw7053step2Labels = raw7053step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7053step1 raw7053step1Labels permutation13 permutation4
    mixedMoment B raw7053step2 raw7053step2Labels = mixedMoment B raw7053step3 raw7053step3Labels := by
      have ha : raw7053step3 = -raw7053step2 := by apply Matrix.ext; change ∀ i j, raw7053step3 i j = -(raw7053step2 i j); unfold raw7053step3 raw7053step2; decide +kernel
      have hl : raw7053step3Labels = raw7053step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7053step3 raw7053step3Labels = mixedMoment B raw7053step4 raw7053step4Labels := by
      have ha : raw7053step4 = raw7053step3 := by apply Matrix.ext; unfold raw7053step4 raw7053step3; decide +kernel
      have hl : raw7053step3Labels = labelEmbedding7 ∘ raw7053step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7053step3 raw7053step3Labels raw7053step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw7054 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7054step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7054step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7054 raw7054Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw7054 raw7054Labels = mixedMoment B raw7054step0 raw7054step0Labels := by
      have hz : ∀ j, raw7054 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7054step0 = (fun i j => raw7054 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7054step0 raw7054; decide +kernel
      have hl : raw7054step0Labels = raw7054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7054 raw7054Labels permutation265 hz
    mixedMoment B raw7054step0 raw7054step0Labels = mixedMoment B raw7054step1 raw7054step1Labels := by
      have ha : raw7054step1 = (fun i j => raw7054step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7054step1 raw7054step0; decide +kernel
      have hl : raw7054step1Labels = raw7054step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7054step0 raw7054step0Labels permutation32 permutation6
    mixedMoment B raw7054step1 raw7054step1Labels = mixedMoment B raw7054step2 raw7054step2Labels := by
      have ha : raw7054step2 = raw7054step1 := by apply Matrix.ext; unfold raw7054step2 raw7054step1; decide +kernel
      have hl : raw7054step1Labels = labelEmbedding9 ∘ raw7054step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7054step1 raw7054step1Labels raw7054step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw7055 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7055step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw7055step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7055 raw7055Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw7055 raw7055Labels = mixedMoment B raw7055step0 raw7055step0Labels := by
      have hz : ∀ j, raw7055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7055step0 = (fun i j => raw7055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7055step0 raw7055; decide +kernel
      have hl : raw7055step0Labels = raw7055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7055 raw7055Labels permutation346 hz
    mixedMoment B raw7055step0 raw7055step0Labels = mixedMoment B raw7055step1 raw7055step1Labels := by
      have hz : ∀ j, raw7055step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7055step1 = (fun i j => raw7055step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7055step1 raw7055step0; decide +kernel
      have hl : raw7055step1Labels = raw7055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7055step0 raw7055step0Labels permutation56 hz
    mixedMoment B raw7055step1 raw7055step1Labels = mixedMoment B raw7055step2 raw7055step2Labels := by
      have ha : raw7055step2 = (fun i j => raw7055step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7055step2 raw7055step1; decide +kernel
      have hl : raw7055step2Labels = raw7055step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7055step1 raw7055step1Labels permutation30 permutation2
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw7056 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw7056step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7056step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7056step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7056step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7056 raw7056Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw7056 raw7056Labels = mixedMoment B raw7056step0 raw7056step0Labels := by
      have ha : raw7056step0 = (fun i j => raw7056 (permutation171 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7056step0 raw7056; decide +kernel
      have hl : raw7056step0Labels = raw7056Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7056 raw7056Labels permutation171 permutation4
    mixedMoment B raw7056step0 raw7056step0Labels = mixedMoment B raw7056step1 raw7056step1Labels := by
      have ha : raw7056step1 = -raw7056step0 := by apply Matrix.ext; change ∀ i j, raw7056step1 i j = -(raw7056step0 i j); unfold raw7056step1 raw7056step0; decide +kernel
      have hl : raw7056step1Labels = raw7056step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7056step1 raw7056step1Labels = mixedMoment B raw7056step2 raw7056step2Labels := by
      have ha : raw7056step2 = raw7056step1 := by apply Matrix.ext; unfold raw7056step2 raw7056step1; decide +kernel
      have hl : raw7056step1Labels = labelEmbedding7 ∘ raw7056step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7056step1 raw7056step1Labels raw7056step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw7057 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7057step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7057step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7057 raw7057Labels = mixedMoment B node5224 node5224Labels := by
  calc
    mixedMoment B raw7057 raw7057Labels = mixedMoment B raw7057step0 raw7057step0Labels := by
      have ha : raw7057step0 = (fun i j => raw7057 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7057step0 raw7057; decide +kernel
      have hl : raw7057step0Labels = raw7057Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7057 raw7057Labels permutation152 permutation6
    mixedMoment B raw7057step0 raw7057step0Labels = mixedMoment B raw7057step1 raw7057step1Labels := by
      have ha : raw7057step1 = raw7057step0 := by apply Matrix.ext; unfold raw7057step1 raw7057step0; decide +kernel
      have hl : raw7057step0Labels = labelEmbedding9 ∘ raw7057step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7057step0 raw7057step0Labels raw7057step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5224 node5224Labels := by rfl

def raw7058 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw7058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7058 raw7058Labels = mixedMoment B node5136 node5136Labels := by
  calc
    mixedMoment B raw7058 raw7058Labels = mixedMoment B raw7058step0 raw7058step0Labels := by
      have ha : raw7058step0 = (fun i j => raw7058 (permutation619 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7058step0 raw7058; decide +kernel
      have hl : raw7058step0Labels = raw7058Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7058 raw7058Labels permutation619 permutation2
    _ = mixedMoment B node5136 node5136Labels := by rfl

def raw7059 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw7059step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw7059step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw7059step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw7059step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7059 raw7059Labels = mixedMoment B node4819 node4819Labels := by
  calc
    mixedMoment B raw7059 raw7059Labels = mixedMoment B raw7059step0 raw7059step0Labels := by
      have hz : ∀ j, raw7059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7059step0 = (fun i j => raw7059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7059step0 raw7059; decide +kernel
      have hl : raw7059step0Labels = raw7059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7059 raw7059Labels permutation346 hz
    mixedMoment B raw7059step0 raw7059step0Labels = mixedMoment B raw7059step1 raw7059step1Labels := by
      have ha : raw7059step1 = (fun i j => raw7059step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7059step1 raw7059step0; decide +kernel
      have hl : raw7059step1Labels = raw7059step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7059step0 raw7059step0Labels permutation37 permutation4
    mixedMoment B raw7059step1 raw7059step1Labels = mixedMoment B raw7059step2 raw7059step2Labels := by
      have ha : raw7059step2 = -raw7059step1 := by apply Matrix.ext; change ∀ i j, raw7059step2 i j = -(raw7059step1 i j); unfold raw7059step2 raw7059step1; decide +kernel
      have hl : raw7059step2Labels = raw7059step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7059step2 raw7059step2Labels = mixedMoment B raw7059step3 raw7059step3Labels := by
      have ha : raw7059step3 = raw7059step2 := by apply Matrix.ext; unfold raw7059step3 raw7059step2; decide +kernel
      have hl : raw7059step2Labels = labelEmbedding7 ∘ raw7059step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7059step2 raw7059step2Labels raw7059step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4819 node4819Labels := by rfl

def raw7060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw7060step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw7060step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7060 raw7060Labels = mixedMoment B node4820 node4820Labels := by
  calc
    mixedMoment B raw7060 raw7060Labels = mixedMoment B raw7060step0 raw7060step0Labels := by
      have hz : ∀ j, raw7060 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7060step0 = (fun i j => raw7060 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7060step0 raw7060; decide +kernel
      have hl : raw7060step0Labels = raw7060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7060 raw7060Labels permutation346 hz
    mixedMoment B raw7060step0 raw7060step0Labels = mixedMoment B raw7060step1 raw7060step1Labels := by
      have ha : raw7060step1 = (fun i j => raw7060step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7060step1 raw7060step0; decide +kernel
      have hl : raw7060step1Labels = raw7060step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7060step0 raw7060step0Labels permutation96 permutation5
    mixedMoment B raw7060step1 raw7060step1Labels = mixedMoment B raw7060step2 raw7060step2Labels := by
      have ha : raw7060step2 = raw7060step1 := by apply Matrix.ext; unfold raw7060step2 raw7060step1; decide +kernel
      have hl : raw7060step1Labels = labelEmbedding8 ∘ raw7060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7060step1 raw7060step1Labels raw7060step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4820 node4820Labels := by rfl

def raw7061 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw7061step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7061step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw7061step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7061 raw7061Labels = mixedMoment B node4818 node4818Labels := by
  calc
    mixedMoment B raw7061 raw7061Labels = mixedMoment B raw7061step0 raw7061step0Labels := by
      have ha : raw7061step0 = (fun i j => raw7061 (permutation502 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7061step0 raw7061; decide +kernel
      have hl : raw7061step0Labels = raw7061Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7061 raw7061Labels permutation502 permutation5
    mixedMoment B raw7061step0 raw7061step0Labels = mixedMoment B raw7061step1 raw7061step1Labels := by
      have ha : raw7061step1 = raw7061step0 := by apply Matrix.ext; unfold raw7061step1 raw7061step0; decide +kernel
      have hl : raw7061step0Labels = labelEmbedding8 ∘ raw7061step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7061step0 raw7061step0Labels raw7061step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4818 node4818Labels := by rfl

def raw7062 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7062step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7062step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7062 raw7062Labels = mixedMoment B node4840 node4840Labels := by
  calc
    mixedMoment B raw7062 raw7062Labels = mixedMoment B raw7062step0 raw7062step0Labels := by
      have hz : ∀ j, raw7062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7062step0 = (fun i j => raw7062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7062step0 raw7062; decide +kernel
      have hl : raw7062step0Labels = raw7062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7062 raw7062Labels permutation346 hz
    mixedMoment B raw7062step0 raw7062step0Labels = mixedMoment B raw7062step1 raw7062step1Labels := by
      have ha : raw7062step1 = (fun i j => raw7062step0 (permutation95 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7062step1 raw7062step0; decide +kernel
      have hl : raw7062step1Labels = raw7062step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7062step0 raw7062step0Labels permutation95 permutation5
    mixedMoment B raw7062step1 raw7062step1Labels = mixedMoment B raw7062step2 raw7062step2Labels := by
      have ha : raw7062step2 = raw7062step1 := by apply Matrix.ext; unfold raw7062step2 raw7062step1; decide +kernel
      have hl : raw7062step1Labels = labelEmbedding8 ∘ raw7062step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7062step1 raw7062step1Labels raw7062step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4840 node4840Labels := by rfl

def raw7063 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7063step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7063 raw7063Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw7063 raw7063Labels = mixedMoment B raw7063step0 raw7063step0Labels := by
      have hz : ∀ j, raw7063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7063step0 = (fun i j => raw7063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7063step0 raw7063; decide +kernel
      have hl : raw7063step0Labels = raw7063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7063 raw7063Labels permutation346 hz
    mixedMoment B raw7063step0 raw7063step0Labels = mixedMoment B raw7063step1 raw7063step1Labels := by
      have ha : raw7063step1 = (fun i j => raw7063step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7063step1 raw7063step0; decide +kernel
      have hl : raw7063step1Labels = raw7063step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7063step0 raw7063step0Labels permutation32 permutation6
    mixedMoment B raw7063step1 raw7063step1Labels = mixedMoment B raw7063step2 raw7063step2Labels := by
      have ha : raw7063step2 = raw7063step1 := by apply Matrix.ext; unfold raw7063step2 raw7063step1; decide +kernel
      have hl : raw7063step1Labels = labelEmbedding9 ∘ raw7063step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7063step1 raw7063step1Labels raw7063step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw7064 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7064step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7064 raw7064Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw7064 raw7064Labels = mixedMoment B raw7064step0 raw7064step0Labels := by
      have hz : ∀ j, raw7064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7064step0 = (fun i j => raw7064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7064step0 raw7064; decide +kernel
      have hl : raw7064step0Labels = raw7064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7064 raw7064Labels permutation346 hz
    mixedMoment B raw7064step0 raw7064step0Labels = mixedMoment B raw7064step1 raw7064step1Labels := by
      have ha : raw7064step1 = (fun i j => raw7064step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7064step1 raw7064step0; decide +kernel
      have hl : raw7064step1Labels = raw7064step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7064step0 raw7064step0Labels permutation32 permutation6
    _ = mixedMoment B node3045 node3045Labels := by rfl

def raw7065 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7065 raw7065Labels = mixedMoment B node3069 node3069Labels := by
  calc
    mixedMoment B raw7065 raw7065Labels = mixedMoment B raw7065step0 raw7065step0Labels := by
      have ha : raw7065step0 = (fun i j => raw7065 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7065step0 raw7065; decide +kernel
      have hl : raw7065step0Labels = raw7065Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7065 raw7065Labels permutation152 permutation6
    _ = mixedMoment B node3069 node3069Labels := by rfl

def raw7066 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw7066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7066 raw7066Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw7066 raw7066Labels = mixedMoment B raw7066step0 raw7066step0Labels := by
      have hz : ∀ j, raw7066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7066step0 = (fun i j => raw7066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7066step0 raw7066; decide +kernel
      have hl : raw7066step0Labels = raw7066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7066 raw7066Labels permutation346 hz
    mixedMoment B raw7066step0 raw7066step0Labels = mixedMoment B raw7066step1 raw7066step1Labels := by
      have ha : raw7066step1 = (fun i j => raw7066step0 (permutation138 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7066step1 raw7066step0; decide +kernel
      have hl : raw7066step1Labels = raw7066step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7066step0 raw7066step0Labels permutation138 permutation3
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw7067 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7067step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7067step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7067step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7067 raw7067Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw7067 raw7067Labels = mixedMoment B raw7067step0 raw7067step0Labels := by
      have hz : ∀ j, raw7067 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7067step0 = (fun i j => raw7067 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7067step0 raw7067; decide +kernel
      have hl : raw7067step0Labels = raw7067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7067 raw7067Labels permutation346 hz
    mixedMoment B raw7067step0 raw7067step0Labels = mixedMoment B raw7067step1 raw7067step1Labels := by
      have hz : ∀ j, raw7067step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7067step1 = (fun i j => raw7067step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7067step1 raw7067step0; decide +kernel
      have hl : raw7067step1Labels = raw7067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7067step0 raw7067step0Labels permutation56 hz
    mixedMoment B raw7067step1 raw7067step1Labels = mixedMoment B raw7067step2 raw7067step2Labels := by
      have ha : raw7067step2 = (fun i j => raw7067step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7067step2 raw7067step1; decide +kernel
      have hl : raw7067step2Labels = raw7067step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7067step1 raw7067step1Labels permutation8 permutation6
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw7068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7068step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7068 raw7068Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw7068 raw7068Labels = mixedMoment B raw7068step0 raw7068step0Labels := by
      have hz : ∀ j, raw7068 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7068step0 = (fun i j => raw7068 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7068step0 raw7068; decide +kernel
      have hl : raw7068step0Labels = raw7068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7068 raw7068Labels permutation265 hz
    mixedMoment B raw7068step0 raw7068step0Labels = mixedMoment B raw7068step1 raw7068step1Labels := by
      have ha : raw7068step1 = (fun i j => raw7068step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7068step1 raw7068step0; decide +kernel
      have hl : raw7068step1Labels = raw7068step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7068step0 raw7068step0Labels permutation32 permutation6
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw7069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7069step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7069 raw7069Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw7069 raw7069Labels = mixedMoment B raw7069step0 raw7069step0Labels := by
      have hz : ∀ j, raw7069 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7069step0 = (fun i j => raw7069 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7069step0 raw7069; decide +kernel
      have hl : raw7069step0Labels = raw7069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7069 raw7069Labels permutation346 hz
    mixedMoment B raw7069step0 raw7069step0Labels = mixedMoment B raw7069step1 raw7069step1Labels := by
      have hz : ∀ j, raw7069step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7069step1 = (fun i j => raw7069step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7069step1 raw7069step0; decide +kernel
      have hl : raw7069step1Labels = raw7069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7069step0 raw7069step0Labels permutation56 hz
    mixedMoment B raw7069step1 raw7069step1Labels = mixedMoment B raw7069step2 raw7069step2Labels := by
      have ha : raw7069step2 = (fun i j => raw7069step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7069step2 raw7069step1; decide +kernel
      have hl : raw7069step2Labels = raw7069step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7069step1 raw7069step1Labels permutation8 permutation6
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw7070 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7070 raw7070Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw7070 raw7070Labels = mixedMoment B raw7070step0 raw7070step0Labels := by
      have ha : raw7070step0 = (fun i j => raw7070 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7070step0 raw7070; decide +kernel
      have hl : raw7070step0Labels = raw7070Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7070 raw7070Labels permutation152 permutation6
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw7071 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7071 raw7071Labels = mixedMoment B node2666 node2666Labels := by
  calc
    mixedMoment B raw7071 raw7071Labels = mixedMoment B raw7071step0 raw7071step0Labels := by
      have ha : raw7071step0 = (fun i j => raw7071 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7071step0 raw7071; decide +kernel
      have hl : raw7071step0Labels = raw7071Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7071 raw7071Labels permutation152 permutation6
    _ = mixedMoment B node2666 node2666Labels := by rfl

def raw7072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw7072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7072 raw7072Labels = mixedMoment B node2715 node2715Labels := by
  calc
    mixedMoment B raw7072 raw7072Labels = mixedMoment B raw7072step0 raw7072step0Labels := by
      have ha : raw7072step0 = (fun i j => raw7072 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7072step0 raw7072; decide +kernel
      have hl : raw7072step0Labels = raw7072Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7072 raw7072Labels permutation152 permutation6
    _ = mixedMoment B node2715 node2715Labels := by rfl

def raw7073 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 0, 1], ![-2, 2, 0]]
def raw7073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw7073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7073 raw7073Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw7073 raw7073Labels = mixedMoment B raw7073step0 raw7073step0Labels := by
      have hz : ∀ j, raw7073 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7073step0 = (fun i j => raw7073 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7073step0 raw7073; decide +kernel
      have hl : raw7073step0Labels = raw7073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7073 raw7073Labels permutation346 hz
    mixedMoment B raw7073step0 raw7073step0Labels = mixedMoment B raw7073step1 raw7073step1Labels := by
      have ha : raw7073step1 = (fun i j => raw7073step0 (permutation92 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7073step1 raw7073step0; decide +kernel
      have hl : raw7073step1Labels = raw7073step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7073step0 raw7073step0Labels permutation92 permutation3
    mixedMoment B raw7073step1 raw7073step1Labels = mixedMoment B raw7073step2 raw7073step2Labels := by
      have ha : raw7073step2 = -raw7073step1 := by apply Matrix.ext; change ∀ i j, raw7073step2 i j = -(raw7073step1 i j); unfold raw7073step2 raw7073step1; decide +kernel
      have hl : raw7073step2Labels = raw7073step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2221 node2221Labels := by rfl

def raw7074 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw7074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw7074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7074 raw7074Labels = mixedMoment B node2122 node2122Labels := by
  calc
    mixedMoment B raw7074 raw7074Labels = mixedMoment B raw7074step0 raw7074step0Labels := by
      have hz : ∀ j, raw7074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7074step0 = (fun i j => raw7074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7074step0 raw7074; decide +kernel
      have hl : raw7074step0Labels = raw7074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7074 raw7074Labels permutation346 hz
    mixedMoment B raw7074step0 raw7074step0Labels = mixedMoment B raw7074step1 raw7074step1Labels := by
      have ha : raw7074step1 = (fun i j => raw7074step0 (permutation83 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7074step1 raw7074step0; decide +kernel
      have hl : raw7074step1Labels = raw7074step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7074step0 raw7074step0Labels permutation83 permutation3
    mixedMoment B raw7074step1 raw7074step1Labels = mixedMoment B raw7074step2 raw7074step2Labels := by
      have ha : raw7074step2 = -raw7074step1 := by apply Matrix.ext; change ∀ i j, raw7074step2 i j = -(raw7074step1 i j); unfold raw7074step2 raw7074step1; decide +kernel
      have hl : raw7074step2Labels = raw7074step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2122 node2122Labels := by rfl

def raw7075 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7075Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw7075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7075 raw7075Labels = mixedMoment B node2120 node2120Labels := by
  calc
    mixedMoment B raw7075 raw7075Labels = mixedMoment B raw7075step0 raw7075step0Labels := by
      have ha : raw7075step0 = (fun i j => raw7075 (permutation443 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7075step0 raw7075; decide +kernel
      have hl : raw7075step0Labels = raw7075Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7075 raw7075Labels permutation443 permutation3
    mixedMoment B raw7075step0 raw7075step0Labels = mixedMoment B raw7075step1 raw7075step1Labels := by
      have ha : raw7075step1 = -raw7075step0 := by apply Matrix.ext; change ∀ i j, raw7075step1 i j = -(raw7075step0 i j); unfold raw7075step1 raw7075step0; decide +kernel
      have hl : raw7075step1Labels = raw7075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2120 node2120Labels := by rfl

def raw7076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7076Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7076step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw7076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw7076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7076 raw7076Labels = mixedMoment B node2121 node2121Labels := by
  calc
    mixedMoment B raw7076 raw7076Labels = mixedMoment B raw7076step0 raw7076step0Labels := by
      have hz : ∀ j, raw7076 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7076step0 = (fun i j => raw7076 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7076step0 raw7076; decide +kernel
      have hl : raw7076step0Labels = raw7076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7076 raw7076Labels permutation346 hz
    mixedMoment B raw7076step0 raw7076step0Labels = mixedMoment B raw7076step1 raw7076step1Labels := by
      have ha : raw7076step1 = (fun i j => raw7076step0 (permutation82 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7076step1 raw7076step0; decide +kernel
      have hl : raw7076step1Labels = raw7076step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7076step0 raw7076step0Labels permutation82 permutation3
    mixedMoment B raw7076step1 raw7076step1Labels = mixedMoment B raw7076step2 raw7076step2Labels := by
      have ha : raw7076step2 = -raw7076step1 := by apply Matrix.ext; change ∀ i j, raw7076step2 i j = -(raw7076step1 i j); unfold raw7076step2 raw7076step1; decide +kernel
      have hl : raw7076step2Labels = raw7076step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2121 node2121Labels := by rfl

def raw7077 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7077step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7077 raw7077Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw7077 raw7077Labels = mixedMoment B raw7077step0 raw7077step0Labels := by
      have hz : ∀ j, raw7077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7077step0 = (fun i j => raw7077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7077step0 raw7077; decide +kernel
      have hl : raw7077step0Labels = raw7077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7077 raw7077Labels permutation346 hz
    mixedMoment B raw7077step0 raw7077step0Labels = mixedMoment B raw7077step1 raw7077step1Labels := by
      have ha : raw7077step1 = (fun i j => raw7077step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7077step1 raw7077step0; decide +kernel
      have hl : raw7077step1Labels = raw7077step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7077step0 raw7077step0Labels permutation32 permutation6
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw7078 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7078step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7078 raw7078Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw7078 raw7078Labels = mixedMoment B raw7078step0 raw7078step0Labels := by
      have hz : ∀ j, raw7078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7078step0 = (fun i j => raw7078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7078step0 raw7078; decide +kernel
      have hl : raw7078step0Labels = raw7078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7078 raw7078Labels permutation346 hz
    mixedMoment B raw7078step0 raw7078step0Labels = mixedMoment B raw7078step1 raw7078step1Labels := by
      have ha : raw7078step1 = (fun i j => raw7078step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7078step1 raw7078step0; decide +kernel
      have hl : raw7078step1Labels = raw7078step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7078step0 raw7078step0Labels permutation38 permutation7
    mixedMoment B raw7078step1 raw7078step1Labels = mixedMoment B raw7078step2 raw7078step2Labels := by
      have ha : raw7078step2 = raw7078step1 := by apply Matrix.ext; unfold raw7078step2 raw7078step1; decide +kernel
      have hl : raw7078step1Labels = labelEmbedding1 ∘ raw7078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7078step1 raw7078step1Labels raw7078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw7079 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7079step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7079 raw7079Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw7079 raw7079Labels = mixedMoment B raw7079step0 raw7079step0Labels := by
      have ha : raw7079step0 = (fun i j => raw7079 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7079step0 raw7079; decide +kernel
      have hl : raw7079step0Labels = raw7079Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7079 raw7079Labels permutation200 permutation7
    mixedMoment B raw7079step0 raw7079step0Labels = mixedMoment B raw7079step1 raw7079step1Labels := by
      have ha : raw7079step1 = raw7079step0 := by apply Matrix.ext; unfold raw7079step1 raw7079step0; decide +kernel
      have hl : raw7079step0Labels = labelEmbedding1 ∘ raw7079step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7079step0 raw7079step0Labels raw7079step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw7080 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7080step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7080 raw7080Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw7080 raw7080Labels = mixedMoment B raw7080step0 raw7080step0Labels := by
      have hz : ∀ j, raw7080 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7080step0 = (fun i j => raw7080 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7080step0 raw7080; decide +kernel
      have hl : raw7080step0Labels = raw7080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7080 raw7080Labels permutation346 hz
    mixedMoment B raw7080step0 raw7080step0Labels = mixedMoment B raw7080step1 raw7080step1Labels := by
      have ha : raw7080step1 = (fun i j => raw7080step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7080step1 raw7080step0; decide +kernel
      have hl : raw7080step1Labels = raw7080step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7080step0 raw7080step0Labels permutation38 permutation7
    mixedMoment B raw7080step1 raw7080step1Labels = mixedMoment B raw7080step2 raw7080step2Labels := by
      have ha : raw7080step2 = raw7080step1 := by apply Matrix.ext; unfold raw7080step2 raw7080step1; decide +kernel
      have hl : raw7080step1Labels = labelEmbedding1 ∘ raw7080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7080step1 raw7080step1Labels raw7080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw7081 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7081step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7081step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw7081step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7081step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7081step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw7081step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7081 raw7081Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw7081 raw7081Labels = mixedMoment B raw7081step0 raw7081step0Labels := by
      have hz : ∀ j, raw7081 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7081step0 = (fun i j => raw7081 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7081step0 raw7081; decide +kernel
      have hl : raw7081step0Labels = raw7081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7081 raw7081Labels permutation346 hz
    mixedMoment B raw7081step0 raw7081step0Labels = mixedMoment B raw7081step1 raw7081step1Labels := by
      have hz : ∀ j, raw7081step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7081step1 = (fun i j => raw7081step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7081step1 raw7081step0; decide +kernel
      have hl : raw7081step1Labels = raw7081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7081step0 raw7081step0Labels permutation56 hz
    mixedMoment B raw7081step1 raw7081step1Labels = mixedMoment B raw7081step2 raw7081step2Labels := by
      have ha : raw7081step2 = (fun i j => raw7081step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7081step2 raw7081step1; decide +kernel
      have hl : raw7081step2Labels = raw7081step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7081step1 raw7081step1Labels permutation13 permutation5
    mixedMoment B raw7081step2 raw7081step2Labels = mixedMoment B raw7081step3 raw7081step3Labels := by
      have ha : raw7081step3 = -raw7081step2 := by apply Matrix.ext; change ∀ i j, raw7081step3 i j = -(raw7081step2 i j); unfold raw7081step3 raw7081step2; decide +kernel
      have hl : raw7081step3Labels = raw7081step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7081step3 raw7081step3Labels = mixedMoment B raw7081step4 raw7081step4Labels := by
      have ha : raw7081step4 = raw7081step3 := by apply Matrix.ext; unfold raw7081step4 raw7081step3; decide +kernel
      have hl : raw7081step3Labels = labelEmbedding1 ∘ raw7081step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7081step3 raw7081step3Labels raw7081step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3224 node3224Labels := by rfl

def raw7082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7082step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7082 raw7082Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw7082 raw7082Labels = mixedMoment B raw7082step0 raw7082step0Labels := by
      have hz : ∀ j, raw7082 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7082step0 = (fun i j => raw7082 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7082step0 raw7082; decide +kernel
      have hl : raw7082step0Labels = raw7082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7082 raw7082Labels permutation265 hz
    mixedMoment B raw7082step0 raw7082step0Labels = mixedMoment B raw7082step1 raw7082step1Labels := by
      have ha : raw7082step1 = (fun i j => raw7082step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7082step1 raw7082step0; decide +kernel
      have hl : raw7082step1Labels = raw7082step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7082step0 raw7082step0Labels permutation38 permutation7
    mixedMoment B raw7082step1 raw7082step1Labels = mixedMoment B raw7082step2 raw7082step2Labels := by
      have ha : raw7082step2 = raw7082step1 := by apply Matrix.ext; unfold raw7082step2 raw7082step1; decide +kernel
      have hl : raw7082step1Labels = labelEmbedding1 ∘ raw7082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7082step1 raw7082step1Labels raw7082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw7083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7083step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7083step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw7083step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw7083step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7083 raw7083Labels = mixedMoment B node3052 node3052Labels := by
  calc
    mixedMoment B raw7083 raw7083Labels = mixedMoment B raw7083step0 raw7083step0Labels := by
      have hz : ∀ j, raw7083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7083step0 = (fun i j => raw7083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7083step0 raw7083; decide +kernel
      have hl : raw7083step0Labels = raw7083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7083 raw7083Labels permutation346 hz
    mixedMoment B raw7083step0 raw7083step0Labels = mixedMoment B raw7083step1 raw7083step1Labels := by
      have hz : ∀ j, raw7083step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7083step1 = (fun i j => raw7083step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7083step1 raw7083step0; decide +kernel
      have hl : raw7083step1Labels = raw7083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7083step0 raw7083step0Labels permutation56 hz
    mixedMoment B raw7083step1 raw7083step1Labels = mixedMoment B raw7083step2 raw7083step2Labels := by
      have ha : raw7083step2 = (fun i j => raw7083step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7083step2 raw7083step1; decide +kernel
      have hl : raw7083step2Labels = raw7083step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7083step1 raw7083step1Labels permutation8 permutation7
    mixedMoment B raw7083step2 raw7083step2Labels = mixedMoment B raw7083step3 raw7083step3Labels := by
      have ha : raw7083step3 = raw7083step2 := by apply Matrix.ext; unfold raw7083step3 raw7083step2; decide +kernel
      have hl : raw7083step2Labels = labelEmbedding1 ∘ raw7083step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7083step2 raw7083step2Labels raw7083step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3052 node3052Labels := by rfl

def raw7084 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw7084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw7084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7084 raw7084Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw7084 raw7084Labels = mixedMoment B raw7084step0 raw7084step0Labels := by
      have ha : raw7084step0 = (fun i j => raw7084 (permutation174 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7084step0 raw7084; decide +kernel
      have hl : raw7084step0Labels = raw7084Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7084 raw7084Labels permutation174 permutation5
    mixedMoment B raw7084step0 raw7084step0Labels = mixedMoment B raw7084step1 raw7084step1Labels := by
      have ha : raw7084step1 = -raw7084step0 := by apply Matrix.ext; change ∀ i j, raw7084step1 i j = -(raw7084step0 i j); unfold raw7084step1 raw7084step0; decide +kernel
      have hl : raw7084step1Labels = raw7084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7084step1 raw7084step1Labels = mixedMoment B raw7084step2 raw7084step2Labels := by
      have ha : raw7084step2 = raw7084step1 := by apply Matrix.ext; unfold raw7084step2 raw7084step1; decide +kernel
      have hl : raw7084step1Labels = labelEmbedding1 ∘ raw7084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7084step1 raw7084step1Labels raw7084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3196 node3196Labels := by rfl

def raw7085 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw7085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7085 raw7085Labels = mixedMoment B node3018 node3018Labels := by
  calc
    mixedMoment B raw7085 raw7085Labels = mixedMoment B raw7085step0 raw7085step0Labels := by
      have ha : raw7085step0 = (fun i j => raw7085 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7085step0 raw7085; decide +kernel
      have hl : raw7085step0Labels = raw7085Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7085 raw7085Labels permutation206 permutation7
    mixedMoment B raw7085step0 raw7085step0Labels = mixedMoment B raw7085step1 raw7085step1Labels := by
      have ha : raw7085step1 = raw7085step0 := by apply Matrix.ext; unfold raw7085step1 raw7085step0; decide +kernel
      have hl : raw7085step0Labels = labelEmbedding1 ∘ raw7085step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7085step0 raw7085step0Labels raw7085step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3018 node3018Labels := by rfl

def raw7086 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw7086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7086 raw7086Labels = mixedMoment B node3015 node3015Labels := by
  calc
    mixedMoment B raw7086 raw7086Labels = mixedMoment B raw7086step0 raw7086step0Labels := by
      have ha : raw7086step0 = (fun i j => raw7086 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7086step0 raw7086; decide +kernel
      have hl : raw7086step0Labels = raw7086Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7086 raw7086Labels permutation206 permutation7
    mixedMoment B raw7086step0 raw7086step0Labels = mixedMoment B raw7086step1 raw7086step1Labels := by
      have ha : raw7086step1 = raw7086step0 := by apply Matrix.ext; unfold raw7086step1 raw7086step0; decide +kernel
      have hl : raw7086step0Labels = labelEmbedding1 ∘ raw7086step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7086step0 raw7086step0Labels raw7086step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3015 node3015Labels := by rfl

def raw7087 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7087step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw7087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw7087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7087 raw7087Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw7087 raw7087Labels = mixedMoment B raw7087step0 raw7087step0Labels := by
      have hz : ∀ j, raw7087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7087step0 = (fun i j => raw7087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7087step0 raw7087; decide +kernel
      have hl : raw7087step0Labels = raw7087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7087 raw7087Labels permutation346 hz
    mixedMoment B raw7087step0 raw7087step0Labels = mixedMoment B raw7087step1 raw7087step1Labels := by
      have ha : raw7087step1 = (fun i j => raw7087step0 (permutation97 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7087step1 raw7087step0; decide +kernel
      have hl : raw7087step1Labels = raw7087step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7087step0 raw7087step0Labels permutation97 permutation5
    mixedMoment B raw7087step1 raw7087step1Labels = mixedMoment B raw7087step2 raw7087step2Labels := by
      have ha : raw7087step2 = raw7087step1 := by apply Matrix.ext; unfold raw7087step2 raw7087step1; decide +kernel
      have hl : raw7087step1Labels = labelEmbedding1 ∘ raw7087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7087step1 raw7087step1Labels raw7087step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2037 node2037Labels := by rfl

def raw7088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7088step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw7088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw7088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7088 raw7088Labels = mixedMoment B node2038 node2038Labels := by
  calc
    mixedMoment B raw7088 raw7088Labels = mixedMoment B raw7088step0 raw7088step0Labels := by
      have hz : ∀ j, raw7088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7088step0 = (fun i j => raw7088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7088step0 raw7088; decide +kernel
      have hl : raw7088step0Labels = raw7088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7088 raw7088Labels permutation346 hz
    mixedMoment B raw7088step0 raw7088step0Labels = mixedMoment B raw7088step1 raw7088step1Labels := by
      have ha : raw7088step1 = (fun i j => raw7088step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7088step1 raw7088step0; decide +kernel
      have hl : raw7088step1Labels = raw7088step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7088step0 raw7088step0Labels permutation96 permutation5
    mixedMoment B raw7088step1 raw7088step1Labels = mixedMoment B raw7088step2 raw7088step2Labels := by
      have ha : raw7088step2 = raw7088step1 := by apply Matrix.ext; unfold raw7088step2 raw7088step1; decide +kernel
      have hl : raw7088step1Labels = labelEmbedding1 ∘ raw7088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7088step1 raw7088step1Labels raw7088step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2038 node2038Labels := by rfl

def raw7089 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw7089step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw7089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7089 raw7089Labels = mixedMoment B node2036 node2036Labels := by
  calc
    mixedMoment B raw7089 raw7089Labels = mixedMoment B raw7089step0 raw7089step0Labels := by
      have ha : raw7089step0 = (fun i j => raw7089 (permutation502 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7089step0 raw7089; decide +kernel
      have hl : raw7089step0Labels = raw7089Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7089 raw7089Labels permutation502 permutation5
    mixedMoment B raw7089step0 raw7089step0Labels = mixedMoment B raw7089step1 raw7089step1Labels := by
      have ha : raw7089step1 = raw7089step0 := by apply Matrix.ext; unfold raw7089step1 raw7089step0; decide +kernel
      have hl : raw7089step0Labels = labelEmbedding1 ∘ raw7089step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7089step0 raw7089step0Labels raw7089step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2036 node2036Labels := by rfl

def raw7090 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7090step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -3, 1]]
def raw7090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7090 raw7090Labels = mixedMoment B node2059 node2059Labels := by
  calc
    mixedMoment B raw7090 raw7090Labels = mixedMoment B raw7090step0 raw7090step0Labels := by
      have hz : ∀ j, raw7090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7090step0 = (fun i j => raw7090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7090step0 raw7090; decide +kernel
      have hl : raw7090step0Labels = raw7090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7090 raw7090Labels permutation346 hz
    mixedMoment B raw7090step0 raw7090step0Labels = mixedMoment B raw7090step1 raw7090step1Labels := by
      have ha : raw7090step1 = (fun i j => raw7090step0 (permutation95 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7090step1 raw7090step0; decide +kernel
      have hl : raw7090step1Labels = raw7090step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7090step0 raw7090step0Labels permutation95 permutation5
    mixedMoment B raw7090step1 raw7090step1Labels = mixedMoment B raw7090step2 raw7090step2Labels := by
      have ha : raw7090step2 = raw7090step1 := by apply Matrix.ext; unfold raw7090step2 raw7090step1; decide +kernel
      have hl : raw7090step1Labels = labelEmbedding1 ∘ raw7090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7090step1 raw7090step1Labels raw7090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2059 node2059Labels := by rfl

def raw7091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw7091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7091 raw7091Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw7091 raw7091Labels = mixedMoment B raw7091step0 raw7091step0Labels := by
      have hz : ∀ j, raw7091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7091step0 = (fun i j => raw7091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7091step0 raw7091; decide +kernel
      have hl : raw7091step0Labels = raw7091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7091 raw7091Labels permutation346 hz
    mixedMoment B raw7091step0 raw7091step0Labels = mixedMoment B raw7091step1 raw7091step1Labels := by
      have ha : raw7091step1 = (fun i j => raw7091step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7091step1 raw7091step0; decide +kernel
      have hl : raw7091step1Labels = raw7091step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7091step0 raw7091step0Labels permutation38 permutation7
    mixedMoment B raw7091step1 raw7091step1Labels = mixedMoment B raw7091step2 raw7091step2Labels := by
      have ha : raw7091step2 = raw7091step1 := by apply Matrix.ext; unfold raw7091step2 raw7091step1; decide +kernel
      have hl : raw7091step1Labels = labelEmbedding1 ∘ raw7091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7091step1 raw7091step1Labels raw7091step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw7092 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw7092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7092 raw7092Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw7092 raw7092Labels = mixedMoment B raw7092step0 raw7092step0Labels := by
      have hz : ∀ j, raw7092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7092step0 = (fun i j => raw7092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7092step0 raw7092; decide +kernel
      have hl : raw7092step0Labels = raw7092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7092 raw7092Labels permutation346 hz
    mixedMoment B raw7092step0 raw7092step0Labels = mixedMoment B raw7092step1 raw7092step1Labels := by
      have ha : raw7092step1 = (fun i j => raw7092step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7092step1 raw7092step0; decide +kernel
      have hl : raw7092step1Labels = raw7092step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7092step0 raw7092step0Labels permutation40 permutation2
    mixedMoment B raw7092step1 raw7092step1Labels = mixedMoment B raw7092step2 raw7092step2Labels := by
      have ha : raw7092step2 = -raw7092step1 := by apply Matrix.ext; change ∀ i j, raw7092step2 i j = -(raw7092step1 i j); unfold raw7092step2 raw7092step1; decide +kernel
      have hl : raw7092step2Labels = raw7092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3379 node3379Labels := by rfl

def raw7093 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7093 raw7093Labels = mixedMoment B node3375 node3375Labels := by
  calc
    mixedMoment B raw7093 raw7093Labels = mixedMoment B raw7093step0 raw7093step0Labels := by
      have ha : raw7093step0 = (fun i j => raw7093 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7093step0 raw7093; decide +kernel
      have hl : raw7093step0Labels = raw7093Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7093 raw7093Labels permutation212 permutation2
    mixedMoment B raw7093step0 raw7093step0Labels = mixedMoment B raw7093step1 raw7093step1Labels := by
      have ha : raw7093step1 = -raw7093step0 := by apply Matrix.ext; change ∀ i j, raw7093step1 i j = -(raw7093step0 i j); unfold raw7093step1 raw7093step0; decide +kernel
      have hl : raw7093step1Labels = raw7093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3375 node3375Labels := by rfl

def raw7094 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw7094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7094 raw7094Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw7094 raw7094Labels = mixedMoment B raw7094step0 raw7094step0Labels := by
      have hz : ∀ j, raw7094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7094step0 = (fun i j => raw7094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7094step0 raw7094; decide +kernel
      have hl : raw7094step0Labels = raw7094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7094 raw7094Labels permutation346 hz
    mixedMoment B raw7094step0 raw7094step0Labels = mixedMoment B raw7094step1 raw7094step1Labels := by
      have ha : raw7094step1 = (fun i j => raw7094step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7094step1 raw7094step0; decide +kernel
      have hl : raw7094step1Labels = raw7094step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7094step0 raw7094step0Labels permutation139 permutation2
    _ = mixedMoment B node2560 node2560Labels := by rfl

def raw7095 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7095Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw7095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7095step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7095step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7095 raw7095Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw7095 raw7095Labels = mixedMoment B raw7095step0 raw7095step0Labels := by
      have hz : ∀ j, raw7095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7095step0 = (fun i j => raw7095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7095step0 raw7095; decide +kernel
      have hl : raw7095step0Labels = raw7095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7095 raw7095Labels permutation346 hz
    mixedMoment B raw7095step0 raw7095step0Labels = mixedMoment B raw7095step1 raw7095step1Labels := by
      have hz : ∀ j, raw7095step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw7095step1 = (fun i j => raw7095step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw7095step1 raw7095step0; decide +kernel
      have hl : raw7095step1Labels = raw7095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7095step0 raw7095step0Labels permutation56 hz
    mixedMoment B raw7095step1 raw7095step1Labels = mixedMoment B raw7095step2 raw7095step2Labels := by
      have ha : raw7095step2 = (fun i j => raw7095step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7095step2 raw7095step1; decide +kernel
      have hl : raw7095step2Labels = raw7095step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7095step1 raw7095step1Labels permutation13 permutation4
    mixedMoment B raw7095step2 raw7095step2Labels = mixedMoment B raw7095step3 raw7095step3Labels := by
      have ha : raw7095step3 = -raw7095step2 := by apply Matrix.ext; change ∀ i j, raw7095step3 i j = -(raw7095step2 i j); unfold raw7095step3 raw7095step2; decide +kernel
      have hl : raw7095step3Labels = raw7095step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw7096 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw7096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7096 raw7096Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw7096 raw7096Labels = mixedMoment B raw7096step0 raw7096step0Labels := by
      have ha : raw7096step0 = (fun i j => raw7096 (permutation171 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7096step0 raw7096; decide +kernel
      have hl : raw7096step0Labels = raw7096Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7096 raw7096Labels permutation171 permutation4
    mixedMoment B raw7096step0 raw7096step0Labels = mixedMoment B raw7096step1 raw7096step1Labels := by
      have ha : raw7096step1 = -raw7096step0 := by apply Matrix.ext; change ∀ i j, raw7096step1 i j = -(raw7096step0 i j); unfold raw7096step1 raw7096step0; decide +kernel
      have hl : raw7096step1Labels = raw7096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2034 node2034Labels := by rfl

def raw7097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw7097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw7097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7097 raw7097Labels = mixedMoment B node2037 node2037Labels := by
  calc
    mixedMoment B raw7097 raw7097Labels = mixedMoment B raw7097step0 raw7097step0Labels := by
      have hz : ∀ j, raw7097 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7097step0 = (fun i j => raw7097 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7097step0 raw7097; decide +kernel
      have hl : raw7097step0Labels = raw7097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7097 raw7097Labels permutation346 hz
    mixedMoment B raw7097step0 raw7097step0Labels = mixedMoment B raw7097step1 raw7097step1Labels := by
      have ha : raw7097step1 = (fun i j => raw7097step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7097step1 raw7097step0; decide +kernel
      have hl : raw7097step1Labels = raw7097step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7097step0 raw7097step0Labels permutation37 permutation4
    mixedMoment B raw7097step1 raw7097step1Labels = mixedMoment B raw7097step2 raw7097step2Labels := by
      have ha : raw7097step2 = -raw7097step1 := by apply Matrix.ext; change ∀ i j, raw7097step2 i j = -(raw7097step1 i j); unfold raw7097step2 raw7097step1; decide +kernel
      have hl : raw7097step2Labels = raw7097step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2037 node2037Labels := by rfl

def raw7098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw7098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7098 raw7098Labels = mixedMoment B node3382 node3382Labels := by
  calc
    mixedMoment B raw7098 raw7098Labels = mixedMoment B raw7098step0 raw7098step0Labels := by
      have ha : raw7098step0 = (fun i j => raw7098 (permutation171 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7098step0 raw7098; decide +kernel
      have hl : raw7098step0Labels = raw7098Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7098 raw7098Labels permutation171 permutation4
    mixedMoment B raw7098step0 raw7098step0Labels = mixedMoment B raw7098step1 raw7098step1Labels := by
      have ha : raw7098step1 = -raw7098step0 := by apply Matrix.ext; change ∀ i j, raw7098step1 i j = -(raw7098step0 i j); unfold raw7098step1 raw7098step0; decide +kernel
      have hl : raw7098step1Labels = raw7098step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3382 node3382Labels := by rfl

def raw7099 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw7099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw7099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7099 raw7099Labels = mixedMoment B node3151 node3151Labels := by
  calc
    mixedMoment B raw7099 raw7099Labels = mixedMoment B raw7099step0 raw7099step0Labels := by
      have hz : ∀ j, raw7099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw7099step0 = (fun i j => raw7099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw7099step0 raw7099; decide +kernel
      have hl : raw7099step0Labels = raw7099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7099 raw7099Labels permutation346 hz
    mixedMoment B raw7099step0 raw7099step0Labels = mixedMoment B raw7099step1 raw7099step1Labels := by
      have ha : raw7099step1 = (fun i j => raw7099step0 (permutation82 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7099step1 raw7099step0; decide +kernel
      have hl : raw7099step1Labels = raw7099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7099step0 raw7099step0Labels permutation82 permutation2
    mixedMoment B raw7099step1 raw7099step1Labels = mixedMoment B raw7099step2 raw7099step2Labels := by
      have ha : raw7099step2 = -raw7099step1 := by apply Matrix.ext; change ∀ i j, raw7099step2 i j = -(raw7099step1 i j); unfold raw7099step2 raw7099step1; decide +kernel
      have hl : raw7099step2Labels = raw7099step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3151 node3151Labels := by rfl

def raw7100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 1, 2]]
def raw7100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw7100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7100 raw7100Labels = mixedMoment B node2555 node2555Labels := by
  calc
    mixedMoment B raw7100 raw7100Labels = mixedMoment B raw7100step0 raw7100step0Labels := by
      have ha : raw7100step0 = (fun i j => raw7100 (permutation619 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7100step0 raw7100; decide +kernel
      have hl : raw7100step0Labels = raw7100Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7100 raw7100Labels permutation619 permutation2
    _ = mixedMoment B node2555 node2555Labels := by rfl

def raw7101 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw7101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw7101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7101 raw7101Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw7101 raw7101Labels = mixedMoment B raw7101step0 raw7101step0Labels := by
      have hz : ∀ j, raw7101 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw7101step0 = (fun i j => raw7101 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw7101step0 raw7101; decide +kernel
      have hl : raw7101step0Labels = raw7101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7101 raw7101Labels permutation265 hz
    mixedMoment B raw7101step0 raw7101step0Labels = mixedMoment B raw7101step1 raw7101step1Labels := by
      have ha : raw7101step1 = (fun i j => raw7101step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw7101step1 raw7101step0; decide +kernel
      have hl : raw7101step1Labels = raw7101step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7101step0 raw7101step0Labels permutation37 permutation4
    mixedMoment B raw7101step1 raw7101step1Labels = mixedMoment B raw7101step2 raw7101step2Labels := by
      have ha : raw7101step2 = -raw7101step1 := by apply Matrix.ext; change ∀ i j, raw7101step2 i j = -(raw7101step1 i j); unfold raw7101step2 raw7101step1; decide +kernel
      have hl : raw7101step2Labels = raw7101step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw7102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw7102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw7102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7102 raw7102Labels = mixedMoment B node3148 node3148Labels := by
  calc
    mixedMoment B raw7102 raw7102Labels = mixedMoment B raw7102step0 raw7102step0Labels := by
      have ha : raw7102step0 = (fun i j => raw7102 (permutation443 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7102step0 raw7102; decide +kernel
      have hl : raw7102step0Labels = raw7102Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7102 raw7102Labels permutation443 permutation2
    mixedMoment B raw7102step0 raw7102step0Labels = mixedMoment B raw7102step1 raw7102step1Labels := by
      have ha : raw7102step1 = -raw7102step0 := by apply Matrix.ext; change ∀ i j, raw7102step1 i j = -(raw7102step0 i j); unfold raw7102step1 raw7102step0; decide +kernel
      have hl : raw7102step1Labels = raw7102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3148 node3148Labels := by rfl

def raw7103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7103 raw7103Labels = mixedMoment B node5405 node5405Labels := by
  calc
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw7104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7104step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7104step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7104step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7104 raw7104Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw7104 raw7104Labels = mixedMoment B raw7104step0 raw7104step0Labels := by
      have ha : raw7104step0 = (fun i j => raw7104 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7104step0 raw7104; decide +kernel
      have hl : raw7104step0Labels = raw7104Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7104 raw7104Labels permutation164 permutation7
    mixedMoment B raw7104step0 raw7104step0Labels = mixedMoment B raw7104step1 raw7104step1Labels := by
      have ha : raw7104step1 = -raw7104step0 := by apply Matrix.ext; change ∀ i j, raw7104step1 i j = -(raw7104step0 i j); unfold raw7104step1 raw7104step0; decide +kernel
      have hl : raw7104step1Labels = raw7104step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7104step1 raw7104step1Labels = mixedMoment B raw7104step2 raw7104step2Labels := by
      have ha : raw7104step2 = raw7104step1 := by apply Matrix.ext; unfold raw7104step2 raw7104step1; decide +kernel
      have hl : raw7104step1Labels = labelEmbedding10 ∘ raw7104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7104step1 raw7104step1Labels raw7104step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw7105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7105step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7105step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7105step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7105step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7105 raw7105Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw7105 raw7105Labels = mixedMoment B raw7105step0 raw7105step0Labels := by
      have ha : raw7105step0 = (fun i j => raw7105 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7105step0 raw7105; decide +kernel
      have hl : raw7105step0Labels = raw7105Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7105 raw7105Labels permutation166 permutation7
    mixedMoment B raw7105step0 raw7105step0Labels = mixedMoment B raw7105step1 raw7105step1Labels := by
      have ha : raw7105step1 = -raw7105step0 := by apply Matrix.ext; change ∀ i j, raw7105step1 i j = -(raw7105step0 i j); unfold raw7105step1 raw7105step0; decide +kernel
      have hl : raw7105step1Labels = raw7105step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7105step1 raw7105step1Labels = mixedMoment B raw7105step2 raw7105step2Labels := by
      have ha : raw7105step2 = raw7105step1 := by apply Matrix.ext; unfold raw7105step2 raw7105step1; decide +kernel
      have hl : raw7105step1Labels = labelEmbedding10 ∘ raw7105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7105step1 raw7105step1Labels raw7105step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw7106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7106step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7106step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7106step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7106step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7106 raw7106Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw7106 raw7106Labels = mixedMoment B raw7106step0 raw7106step0Labels := by
      have hz : ∀ j, raw7106 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7106step0 = (fun i j => raw7106 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7106step0 raw7106; decide +kernel
      have hl : raw7106step0Labels = raw7106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7106 raw7106Labels permutation520 hz
    mixedMoment B raw7106step0 raw7106step0Labels = mixedMoment B raw7106step1 raw7106step1Labels := by
      have ha : raw7106step1 = (fun i j => raw7106step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7106step1 raw7106step0; decide +kernel
      have hl : raw7106step1Labels = raw7106step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7106step0 raw7106step0Labels permutation32 permutation7
    mixedMoment B raw7106step1 raw7106step1Labels = mixedMoment B raw7106step2 raw7106step2Labels := by
      have ha : raw7106step2 = -raw7106step1 := by apply Matrix.ext; change ∀ i j, raw7106step2 i j = -(raw7106step1 i j); unfold raw7106step2 raw7106step1; decide +kernel
      have hl : raw7106step2Labels = raw7106step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7106step2 raw7106step2Labels = mixedMoment B raw7106step3 raw7106step3Labels := by
      have ha : raw7106step3 = raw7106step2 := by apply Matrix.ext; unfold raw7106step3 raw7106step2; decide +kernel
      have hl : raw7106step2Labels = labelEmbedding10 ∘ raw7106step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7106step2 raw7106step2Labels raw7106step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw7107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7107step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7107step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7107step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7107 raw7107Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw7107 raw7107Labels = mixedMoment B raw7107step0 raw7107step0Labels := by
      have ha : raw7107step0 = (fun i j => raw7107 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7107step0 raw7107; decide +kernel
      have hl : raw7107step0Labels = raw7107Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7107 raw7107Labels permutation164 permutation7
    mixedMoment B raw7107step0 raw7107step0Labels = mixedMoment B raw7107step1 raw7107step1Labels := by
      have ha : raw7107step1 = -raw7107step0 := by apply Matrix.ext; change ∀ i j, raw7107step1 i j = -(raw7107step0 i j); unfold raw7107step1 raw7107step0; decide +kernel
      have hl : raw7107step1Labels = raw7107step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7107step1 raw7107step1Labels = mixedMoment B raw7107step2 raw7107step2Labels := by
      have ha : raw7107step2 = raw7107step1 := by apply Matrix.ext; unfold raw7107step2 raw7107step1; decide +kernel
      have hl : raw7107step1Labels = labelEmbedding10 ∘ raw7107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7107step1 raw7107step1Labels raw7107step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw7108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7108step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7108 raw7108Labels = mixedMoment B node4582 node4582Labels := by
  calc
    mixedMoment B raw7108 raw7108Labels = mixedMoment B raw7108step0 raw7108step0Labels := by
      have ha : raw7108step0 = (fun i j => raw7108 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7108step0 raw7108; decide +kernel
      have hl : raw7108step0Labels = raw7108Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7108 raw7108Labels permutation184 permutation3
    mixedMoment B raw7108step0 raw7108step0Labels = mixedMoment B raw7108step1 raw7108step1Labels := by
      have ha : raw7108step1 = raw7108step0 := by apply Matrix.ext; unfold raw7108step1 raw7108step0; decide +kernel
      have hl : raw7108step0Labels = labelEmbedding6 ∘ raw7108step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7108step0 raw7108step0Labels raw7108step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4582 node4582Labels := by rfl

def raw7109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7109 raw7109Labels = mixedMoment B node5190 node5190Labels := by
  calc
    mixedMoment B raw7109 raw7109Labels = mixedMoment B raw7109step0 raw7109step0Labels := by
      have ha : raw7109step0 = (fun i j => raw7109 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7109step0 raw7109; decide +kernel
      have hl : raw7109step0Labels = raw7109Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7109 raw7109Labels permutation182 permutation2
    _ = mixedMoment B node5190 node5190Labels := by rfl

def raw7110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw7110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7110 raw7110Labels = mixedMoment B node5190 node5190Labels := by
  calc
    mixedMoment B raw7110 raw7110Labels = mixedMoment B raw7110step0 raw7110step0Labels := by
      have ha : raw7110step0 = (fun i j => raw7110 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7110step0 raw7110; decide +kernel
      have hl : raw7110step0Labels = raw7110Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7110 raw7110Labels permutation206 permutation2
    _ = mixedMoment B node5190 node5190Labels := by rfl

def raw7111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7111step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7111 raw7111Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw7111 raw7111Labels = mixedMoment B raw7111step0 raw7111step0Labels := by
      have hz : ∀ j, raw7111 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7111step0 = (fun i j => raw7111 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7111step0 raw7111; decide +kernel
      have hl : raw7111step0Labels = raw7111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7111 raw7111Labels permutation520 hz
    mixedMoment B raw7111step0 raw7111step0Labels = mixedMoment B raw7111step1 raw7111step1Labels := by
      have ha : raw7111step1 = (fun i j => raw7111step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7111step1 raw7111step0; decide +kernel
      have hl : raw7111step1Labels = raw7111step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7111step0 raw7111step0Labels permutation40 permutation2
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw7112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7112 raw7112Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw7112 raw7112Labels = mixedMoment B raw7112step0 raw7112step0Labels := by
      have ha : raw7112step0 = (fun i j => raw7112 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7112step0 raw7112; decide +kernel
      have hl : raw7112step0Labels = raw7112Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7112 raw7112Labels permutation182 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw7113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7113 raw7113Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw7113 raw7113Labels = mixedMoment B raw7113step0 raw7113step0Labels := by
      have ha : raw7113step0 = (fun i j => raw7113 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7113step0 raw7113; decide +kernel
      have hl : raw7113step0Labels = raw7113Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7113 raw7113Labels permutation160 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw7114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7114 raw7114Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw7114 raw7114Labels = mixedMoment B raw7114step0 raw7114step0Labels := by
      have ha : raw7114step0 = (fun i j => raw7114 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7114step0 raw7114; decide +kernel
      have hl : raw7114step0Labels = raw7114Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7114 raw7114Labels permutation160 permutation2
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw7115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7115 raw7115Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw7115 raw7115Labels = mixedMoment B raw7115step0 raw7115step0Labels := by
      have ha : raw7115step0 = (fun i j => raw7115 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7115step0 raw7115; decide +kernel
      have hl : raw7115step0Labels = raw7115Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7115 raw7115Labels permutation202 permutation2
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw7116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7116 raw7116Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw7116 raw7116Labels = mixedMoment B raw7116step0 raw7116step0Labels := by
      have hz : ∀ j, raw7116 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7116step0 = (fun i j => raw7116 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7116step0 raw7116; decide +kernel
      have hl : raw7116step0Labels = raw7116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7116 raw7116Labels permutation520 hz
    mixedMoment B raw7116step0 raw7116step0Labels = mixedMoment B raw7116step1 raw7116step1Labels := by
      have ha : raw7116step1 = (fun i j => raw7116step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7116step1 raw7116step0; decide +kernel
      have hl : raw7116step1Labels = raw7116step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7116step0 raw7116step0Labels permutation34 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw7117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7117 raw7117Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw7117 raw7117Labels = mixedMoment B raw7117step0 raw7117step0Labels := by
      have ha : raw7117step0 = (fun i j => raw7117 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7117step0 raw7117; decide +kernel
      have hl : raw7117step0Labels = raw7117Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7117 raw7117Labels permutation160 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw7118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7118 raw7118Labels = mixedMoment B node4590 node4590Labels := by
  calc
    mixedMoment B raw7118 raw7118Labels = mixedMoment B raw7118step0 raw7118step0Labels := by
      have ha : raw7118step0 = (fun i j => raw7118 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7118step0 raw7118; decide +kernel
      have hl : raw7118step0Labels = raw7118Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7118 raw7118Labels permutation154 permutation2
    _ = mixedMoment B node4590 node4590Labels := by rfl

def raw7119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7119 raw7119Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw7119 raw7119Labels = mixedMoment B raw7119step0 raw7119step0Labels := by
      have ha : raw7119step0 = (fun i j => raw7119 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7119step0 raw7119; decide +kernel
      have hl : raw7119step0Labels = raw7119Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7119 raw7119Labels permutation154 permutation2
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw7120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7120 raw7120Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw7120 raw7120Labels = mixedMoment B raw7120step0 raw7120step0Labels := by
      have ha : raw7120step0 = (fun i j => raw7120 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7120step0 raw7120; decide +kernel
      have hl : raw7120step0Labels = raw7120Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7120 raw7120Labels permutation178 permutation2
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw7121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7121 raw7121Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw7121 raw7121Labels = mixedMoment B raw7121step0 raw7121step0Labels := by
      have hz : ∀ j, raw7121 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7121step0 = (fun i j => raw7121 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7121step0 raw7121; decide +kernel
      have hl : raw7121step0Labels = raw7121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7121 raw7121Labels permutation520 hz
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw7122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7122 raw7122Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw7122 raw7122Labels = mixedMoment B raw7122step0 raw7122step0Labels := by
      have ha : raw7122step0 = (fun i j => raw7122 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7122step0 raw7122; decide +kernel
      have hl : raw7122step0Labels = raw7122Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7122 raw7122Labels permutation154 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw7123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7123step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7123 raw7123Labels = mixedMoment B node4578 node4578Labels := by
  calc
    mixedMoment B raw7123 raw7123Labels = mixedMoment B raw7123step0 raw7123step0Labels := by
      have ha : raw7123step0 = (fun i j => raw7123 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7123step0 raw7123; decide +kernel
      have hl : raw7123step0Labels = raw7123Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7123 raw7123Labels permutation183 permutation3
    mixedMoment B raw7123step0 raw7123step0Labels = mixedMoment B raw7123step1 raw7123step1Labels := by
      have ha : raw7123step1 = raw7123step0 := by apply Matrix.ext; unfold raw7123step1 raw7123step0; decide +kernel
      have hl : raw7123step0Labels = labelEmbedding6 ∘ raw7123step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7123step0 raw7123step0Labels raw7123step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4578 node4578Labels := by rfl

def raw7124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7124 raw7124Labels = mixedMoment B node5067 node5067Labels := by
  calc
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw7125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7125 raw7125Labels = mixedMoment B node5182 node5182Labels := by
  calc
    mixedMoment B raw7125 raw7125Labels = mixedMoment B raw7125step0 raw7125step0Labels := by
      have ha : raw7125step0 = (fun i j => raw7125 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7125step0 raw7125; decide +kernel
      have hl : raw7125step0Labels = raw7125Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7125 raw7125Labels permutation176 permutation2
    _ = mixedMoment B node5182 node5182Labels := by rfl

def raw7126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7126 raw7126Labels = mixedMoment B node5182 node5182Labels := by
  calc
    mixedMoment B raw7126 raw7126Labels = mixedMoment B raw7126step0 raw7126step0Labels := by
      have ha : raw7126step0 = (fun i j => raw7126 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7126step0 raw7126; decide +kernel
      have hl : raw7126step0Labels = raw7126Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7126 raw7126Labels permutation200 permutation2
    _ = mixedMoment B node5182 node5182Labels := by rfl

def raw7127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7127 raw7127Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw7127 raw7127Labels = mixedMoment B raw7127step0 raw7127step0Labels := by
      have ha : raw7127step0 = (fun i j => raw7127 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7127step0 raw7127; decide +kernel
      have hl : raw7127step0Labels = raw7127Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7127 raw7127Labels permutation153 permutation2
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw7128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw7128step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw7128step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7128 raw7128Labels = mixedMoment B node4577 node4577Labels := by
  calc
    mixedMoment B raw7128 raw7128Labels = mixedMoment B raw7128step0 raw7128step0Labels := by
      have ha : raw7128step0 = (fun i j => raw7128 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7128step0 raw7128; decide +kernel
      have hl : raw7128step0Labels = raw7128Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7128 raw7128Labels permutation182 permutation3
    mixedMoment B raw7128step0 raw7128step0Labels = mixedMoment B raw7128step1 raw7128step1Labels := by
      have ha : raw7128step1 = raw7128step0 := by apply Matrix.ext; unfold raw7128step1 raw7128step0; decide +kernel
      have hl : raw7128step0Labels = labelEmbedding6 ∘ raw7128step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7128step0 raw7128step0Labels raw7128step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4577 node4577Labels := by rfl

def raw7129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7129 raw7129Labels = mixedMoment B node5065 node5065Labels := by
  calc
    _ = mixedMoment B node5065 node5065Labels := by rfl

def raw7130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7130step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7130step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7130step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7130step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7130 raw7130Labels = mixedMoment B node5048 node5048Labels := by
  calc
    mixedMoment B raw7130 raw7130Labels = mixedMoment B raw7130step0 raw7130step0Labels := by
      have ha : raw7130step0 = (fun i j => raw7130 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7130step0 raw7130; decide +kernel
      have hl : raw7130step0Labels = raw7130Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7130 raw7130Labels permutation676 permutation3
    mixedMoment B raw7130step0 raw7130step0Labels = mixedMoment B raw7130step1 raw7130step1Labels := by
      have ha : raw7130step1 = -raw7130step0 := by apply Matrix.ext; change ∀ i j, raw7130step1 i j = -(raw7130step0 i j); unfold raw7130step1 raw7130step0; decide +kernel
      have hl : raw7130step1Labels = raw7130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7130step1 raw7130step1Labels = mixedMoment B raw7130step2 raw7130step2Labels := by
      have ha : raw7130step2 = raw7130step1 := by apply Matrix.ext; unfold raw7130step2 raw7130step1; decide +kernel
      have hl : raw7130step1Labels = labelEmbedding6 ∘ raw7130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7130step1 raw7130step1Labels raw7130step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5048 node5048Labels := by rfl

def raw7131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7131step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7131step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7131step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7131 raw7131Labels = mixedMoment B node5048 node5048Labels := by
  calc
    mixedMoment B raw7131 raw7131Labels = mixedMoment B raw7131step0 raw7131step0Labels := by
      have ha : raw7131step0 = (fun i j => raw7131 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7131step0 raw7131; decide +kernel
      have hl : raw7131step0Labels = raw7131Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7131 raw7131Labels permutation674 permutation3
    mixedMoment B raw7131step0 raw7131step0Labels = mixedMoment B raw7131step1 raw7131step1Labels := by
      have ha : raw7131step1 = -raw7131step0 := by apply Matrix.ext; change ∀ i j, raw7131step1 i j = -(raw7131step0 i j); unfold raw7131step1 raw7131step0; decide +kernel
      have hl : raw7131step1Labels = raw7131step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7131step1 raw7131step1Labels = mixedMoment B raw7131step2 raw7131step2Labels := by
      have ha : raw7131step2 = raw7131step1 := by apply Matrix.ext; unfold raw7131step2 raw7131step1; decide +kernel
      have hl : raw7131step1Labels = labelEmbedding6 ∘ raw7131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7131step1 raw7131step1Labels raw7131step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5048 node5048Labels := by rfl

def raw7132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw7132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw7132step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7132 raw7132Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw7132 raw7132Labels = mixedMoment B raw7132step0 raw7132step0Labels := by
      have hz : ∀ j, raw7132 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7132step0 = (fun i j => raw7132 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7132step0 raw7132; decide +kernel
      have hl : raw7132step0Labels = raw7132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7132 raw7132Labels permutation520 hz
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw7133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7133Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw7133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7133 raw7133Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw7133 raw7133Labels = mixedMoment B raw7133step0 raw7133step0Labels := by
      have ha : raw7133step0 = (fun i j => raw7133 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7133step0 raw7133; decide +kernel
      have hl : raw7133step0Labels = raw7133Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7133 raw7133Labels permutation682 permutation3
    mixedMoment B raw7133step0 raw7133step0Labels = mixedMoment B raw7133step1 raw7133step1Labels := by
      have ha : raw7133step1 = -raw7133step0 := by apply Matrix.ext; change ∀ i j, raw7133step1 i j = -(raw7133step0 i j); unfold raw7133step1 raw7133step0; decide +kernel
      have hl : raw7133step1Labels = raw7133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw7134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7134Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw7134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7134step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7134 raw7134Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw7134 raw7134Labels = mixedMoment B raw7134step0 raw7134step0Labels := by
      have ha : raw7134step0 = (fun i j => raw7134 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7134step0 raw7134; decide +kernel
      have hl : raw7134step0Labels = raw7134Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7134 raw7134Labels permutation676 permutation3
    mixedMoment B raw7134step0 raw7134step0Labels = mixedMoment B raw7134step1 raw7134step1Labels := by
      have ha : raw7134step1 = -raw7134step0 := by apply Matrix.ext; change ∀ i j, raw7134step1 i j = -(raw7134step0 i j); unfold raw7134step1 raw7134step0; decide +kernel
      have hl : raw7134step1Labels = raw7134step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw7135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7135Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw7135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7135step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7135step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7135 raw7135Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw7135 raw7135Labels = mixedMoment B raw7135step0 raw7135step0Labels := by
      have ha : raw7135step0 = (fun i j => raw7135 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7135step0 raw7135; decide +kernel
      have hl : raw7135step0Labels = raw7135Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7135 raw7135Labels permutation674 permutation3
    mixedMoment B raw7135step0 raw7135step0Labels = mixedMoment B raw7135step1 raw7135step1Labels := by
      have ha : raw7135step1 = -raw7135step0 := by apply Matrix.ext; change ∀ i j, raw7135step1 i j = -(raw7135step0 i j); unfold raw7135step1 raw7135step0; decide +kernel
      have hl : raw7135step1Labels = raw7135step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw7136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7136Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7136step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw7136step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7136 raw7136Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw7136 raw7136Labels = mixedMoment B raw7136step0 raw7136step0Labels := by
      have hz : ∀ j, raw7136 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7136step0 = (fun i j => raw7136 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7136step0 raw7136; decide +kernel
      have hl : raw7136step0Labels = raw7136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7136 raw7136Labels permutation520 hz
    mixedMoment B raw7136step0 raw7136step0Labels = mixedMoment B raw7136step1 raw7136step1Labels := by
      have ha : raw7136step1 = (fun i j => raw7136step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7136step1 raw7136step0; decide +kernel
      have hl : raw7136step1Labels = raw7136step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7136step0 raw7136step0Labels permutation137 permutation3
    mixedMoment B raw7136step1 raw7136step1Labels = mixedMoment B raw7136step2 raw7136step2Labels := by
      have ha : raw7136step2 = -raw7136step1 := by apply Matrix.ext; change ∀ i j, raw7136step2 i j = -(raw7136step1 i j); unfold raw7136step2 raw7136step1; decide +kernel
      have hl : raw7136step2Labels = raw7136step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw7137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7137Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7137step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7137 raw7137Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw7137 raw7137Labels = mixedMoment B raw7137step0 raw7137step0Labels := by
      have ha : raw7137step0 = (fun i j => raw7137 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7137step0 raw7137; decide +kernel
      have hl : raw7137step0Labels = raw7137Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7137 raw7137Labels permutation168 permutation6
    mixedMoment B raw7137step0 raw7137step0Labels = mixedMoment B raw7137step1 raw7137step1Labels := by
      have ha : raw7137step1 = -raw7137step0 := by apply Matrix.ext; change ∀ i j, raw7137step1 i j = -(raw7137step0 i j); unfold raw7137step1 raw7137step0; decide +kernel
      have hl : raw7137step1Labels = raw7137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw7138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7138 raw7138Labels = mixedMoment B node1201 node1201Labels := by
  calc
    mixedMoment B raw7138 raw7138Labels = mixedMoment B raw7138step0 raw7138step0Labels := by
      have ha : raw7138step0 = (fun i j => raw7138 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7138step0 raw7138; decide +kernel
      have hl : raw7138step0Labels = raw7138Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7138 raw7138Labels permutation184 permutation3
    _ = mixedMoment B node1201 node1201Labels := by rfl

def raw7139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7139Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7139 raw7139Labels = mixedMoment B node2854 node2854Labels := by
  calc
    mixedMoment B raw7139 raw7139Labels = mixedMoment B raw7139step0 raw7139step0Labels := by
      have ha : raw7139step0 = (fun i j => raw7139 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7139step0 raw7139; decide +kernel
      have hl : raw7139step0Labels = raw7139Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7139 raw7139Labels permutation184 permutation3
    _ = mixedMoment B node2854 node2854Labels := by rfl

def raw7140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw7140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7140 raw7140Labels = mixedMoment B node2854 node2854Labels := by
  calc
    mixedMoment B raw7140 raw7140Labels = mixedMoment B raw7140step0 raw7140step0Labels := by
      have ha : raw7140step0 = (fun i j => raw7140 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7140step0 raw7140; decide +kernel
      have hl : raw7140step0Labels = raw7140Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7140 raw7140Labels permutation208 permutation3
    _ = mixedMoment B node2854 node2854Labels := by rfl

def raw7141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7141step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw7141step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7141 raw7141Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw7141 raw7141Labels = mixedMoment B raw7141step0 raw7141step0Labels := by
      have hz : ∀ j, raw7141 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7141step0 = (fun i j => raw7141 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7141step0 raw7141; decide +kernel
      have hl : raw7141step0Labels = raw7141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7141 raw7141Labels permutation520 hz
    mixedMoment B raw7141step0 raw7141step0Labels = mixedMoment B raw7141step1 raw7141step1Labels := by
      have ha : raw7141step1 = (fun i j => raw7141step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7141step1 raw7141step0; decide +kernel
      have hl : raw7141step1Labels = raw7141step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7141step0 raw7141step0Labels permutation40 permutation3
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw7142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7142step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7142 raw7142Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw7142 raw7142Labels = mixedMoment B raw7142step0 raw7142step0Labels := by
      have ha : raw7142step0 = (fun i j => raw7142 (permutation187 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7142step0 raw7142; decide +kernel
      have hl : raw7142step0Labels = raw7142Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7142 raw7142Labels permutation187 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw7143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7143step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7143 raw7143Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw7143 raw7143Labels = mixedMoment B raw7143step0 raw7143step0Labels := by
      have ha : raw7143step0 = (fun i j => raw7143 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7143step0 raw7143; decide +kernel
      have hl : raw7143step0Labels = raw7143Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7143 raw7143Labels permutation200 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw7144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7144step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7144 raw7144Labels = mixedMoment B node2987 node2987Labels := by
  calc
    mixedMoment B raw7144 raw7144Labels = mixedMoment B raw7144step0 raw7144step0Labels := by
      have ha : raw7144step0 = (fun i j => raw7144 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7144step0 raw7144; decide +kernel
      have hl : raw7144step0Labels = raw7144Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7144 raw7144Labels permutation158 permutation3
    _ = mixedMoment B node2987 node2987Labels := by rfl

def raw7145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7145step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7145 raw7145Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw7145 raw7145Labels = mixedMoment B raw7145step0 raw7145step0Labels := by
      have ha : raw7145step0 = (fun i j => raw7145 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7145step0 raw7145; decide +kernel
      have hl : raw7145step0Labels = raw7145Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7145 raw7145Labels permutation200 permutation3
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw7146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7146step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7146step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7146 raw7146Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw7146 raw7146Labels = mixedMoment B raw7146step0 raw7146step0Labels := by
      have hz : ∀ j, raw7146 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7146step0 = (fun i j => raw7146 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7146step0 raw7146; decide +kernel
      have hl : raw7146step0Labels = raw7146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7146 raw7146Labels permutation520 hz
    mixedMoment B raw7146step0 raw7146step0Labels = mixedMoment B raw7146step1 raw7146step1Labels := by
      have ha : raw7146step1 = (fun i j => raw7146step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7146step1 raw7146step0; decide +kernel
      have hl : raw7146step1Labels = raw7146step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7146step0 raw7146step0Labels permutation44 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw7147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7147step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7147 raw7147Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw7147 raw7147Labels = mixedMoment B raw7147step0 raw7147step0Labels := by
      have ha : raw7147step0 = (fun i j => raw7147 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7147step0 raw7147; decide +kernel
      have hl : raw7147step0Labels = raw7147Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7147 raw7147Labels permutation201 permutation3
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw7148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7148step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7148 raw7148Labels = mixedMoment B node1213 node1213Labels := by
  calc
    mixedMoment B raw7148 raw7148Labels = mixedMoment B raw7148step0 raw7148step0Labels := by
      have ha : raw7148step0 = (fun i j => raw7148 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7148step0 raw7148; decide +kernel
      have hl : raw7148step0Labels = raw7148Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7148 raw7148Labels permutation176 permutation3
    _ = mixedMoment B node1213 node1213Labels := by rfl

def raw7149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7149 raw7149Labels = mixedMoment B node2987 node2987Labels := by
  calc
    mixedMoment B raw7149 raw7149Labels = mixedMoment B raw7149step0 raw7149step0Labels := by
      have ha : raw7149step0 = (fun i j => raw7149 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7149step0 raw7149; decide +kernel
      have hl : raw7149step0Labels = raw7149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7149 raw7149Labels permutation152 permutation3
    _ = mixedMoment B node2987 node2987Labels := by rfl

def raw7150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw7150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7150 raw7150Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw7150 raw7150Labels = mixedMoment B raw7150step0 raw7150step0Labels := by
      have ha : raw7150step0 = (fun i j => raw7150 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7150step0 raw7150; decide +kernel
      have hl : raw7150step0Labels = raw7150Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7150 raw7150Labels permutation176 permutation3
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw7151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7151step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7151step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7151 raw7151Labels = mixedMoment B node3088 node3088Labels := by
  calc
    mixedMoment B raw7151 raw7151Labels = mixedMoment B raw7151step0 raw7151step0Labels := by
      have hz : ∀ j, raw7151 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7151step0 = (fun i j => raw7151 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7151step0 raw7151; decide +kernel
      have hl : raw7151step0Labels = raw7151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7151 raw7151Labels permutation520 hz
    mixedMoment B raw7151step0 raw7151step0Labels = mixedMoment B raw7151step1 raw7151step1Labels := by
      have ha : raw7151step1 = (fun i j => raw7151step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7151step1 raw7151step0; decide +kernel
      have hl : raw7151step1Labels = raw7151step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7151step0 raw7151step0Labels permutation38 permutation3
    _ = mixedMoment B node3088 node3088Labels := by rfl

def raw7152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7152 raw7152Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw7152 raw7152Labels = mixedMoment B raw7152step0 raw7152step0Labels := by
      have ha : raw7152step0 = (fun i j => raw7152 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7152step0 raw7152; decide +kernel
      have hl : raw7152step0Labels = raw7152Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7152 raw7152Labels permutation177 permutation3
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw7153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7153 raw7153Labels = mixedMoment B node1196 node1196Labels := by
  calc
    mixedMoment B raw7153 raw7153Labels = mixedMoment B raw7153step0 raw7153step0Labels := by
      have ha : raw7153step0 = (fun i j => raw7153 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7153step0 raw7153; decide +kernel
      have hl : raw7153step0Labels = raw7153Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7153 raw7153Labels permutation183 permutation3
    _ = mixedMoment B node1196 node1196Labels := by rfl

def raw7154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7154 raw7154Labels = mixedMoment B node2981 node2981Labels := by
  calc
    mixedMoment B raw7154 raw7154Labels = mixedMoment B raw7154step0 raw7154step0Labels := by
      have ha : raw7154step0 = (fun i j => raw7154 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7154step0 raw7154; decide +kernel
      have hl : raw7154step0Labels = raw7154Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7154 raw7154Labels permutation153 permutation3
    _ = mixedMoment B node2981 node2981Labels := by rfl

def raw7155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7155 raw7155Labels = mixedMoment B node2850 node2850Labels := by
  calc
    mixedMoment B raw7155 raw7155Labels = mixedMoment B raw7155step0 raw7155step0Labels := by
      have ha : raw7155step0 = (fun i j => raw7155 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7155step0 raw7155; decide +kernel
      have hl : raw7155step0Labels = raw7155Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7155 raw7155Labels permutation183 permutation3
    _ = mixedMoment B node2850 node2850Labels := by rfl

def raw7156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7156step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7156 raw7156Labels = mixedMoment B node2850 node2850Labels := by
  calc
    mixedMoment B raw7156 raw7156Labels = mixedMoment B raw7156step0 raw7156step0Labels := by
      have ha : raw7156step0 = (fun i j => raw7156 (permutation207 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7156step0 raw7156; decide +kernel
      have hl : raw7156step0Labels = raw7156Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7156 raw7156Labels permutation207 permutation3
    _ = mixedMoment B node2850 node2850Labels := by rfl

def raw7157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw7157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7157 raw7157Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw7157 raw7157Labels = mixedMoment B raw7157step0 raw7157step0Labels := by
      have ha : raw7157step0 = (fun i j => raw7157 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7157step0 raw7157; decide +kernel
      have hl : raw7157step0Labels = raw7157Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7157 raw7157Labels permutation183 permutation3
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw7158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw7158step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7158 raw7158Labels = mixedMoment B node1195 node1195Labels := by
  calc
    mixedMoment B raw7158 raw7158Labels = mixedMoment B raw7158step0 raw7158step0Labels := by
      have ha : raw7158step0 = (fun i j => raw7158 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7158step0 raw7158; decide +kernel
      have hl : raw7158step0Labels = raw7158Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7158 raw7158Labels permutation182 permutation3
    _ = mixedMoment B node1195 node1195Labels := by rfl

def raw7159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw7159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7159 raw7159Labels = mixedMoment B node2470 node2470Labels := by
  calc
    mixedMoment B raw7159 raw7159Labels = mixedMoment B raw7159step0 raw7159step0Labels := by
      have ha : raw7159step0 = (fun i j => raw7159 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7159step0 raw7159; decide +kernel
      have hl : raw7159step0Labels = raw7159Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7159 raw7159Labels permutation682 permutation3
    mixedMoment B raw7159step0 raw7159step0Labels = mixedMoment B raw7159step1 raw7159step1Labels := by
      have ha : raw7159step1 = -raw7159step0 := by apply Matrix.ext; change ∀ i j, raw7159step1 i j = -(raw7159step0 i j); unfold raw7159step1 raw7159step0; decide +kernel
      have hl : raw7159step1Labels = raw7159step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2470 node2470Labels := by rfl

def raw7160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7160step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7160 raw7160Labels = mixedMoment B node2450 node2450Labels := by
  calc
    mixedMoment B raw7160 raw7160Labels = mixedMoment B raw7160step0 raw7160step0Labels := by
      have ha : raw7160step0 = (fun i j => raw7160 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7160step0 raw7160; decide +kernel
      have hl : raw7160step0Labels = raw7160Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7160 raw7160Labels permutation676 permutation3
    mixedMoment B raw7160step0 raw7160step0Labels = mixedMoment B raw7160step1 raw7160step1Labels := by
      have ha : raw7160step1 = -raw7160step0 := by apply Matrix.ext; change ∀ i j, raw7160step1 i j = -(raw7160step0 i j); unfold raw7160step1 raw7160step0; decide +kernel
      have hl : raw7160step1Labels = raw7160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2450 node2450Labels := by rfl

def raw7161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7161 raw7161Labels = mixedMoment B node2450 node2450Labels := by
  calc
    mixedMoment B raw7161 raw7161Labels = mixedMoment B raw7161step0 raw7161step0Labels := by
      have ha : raw7161step0 = (fun i j => raw7161 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7161step0 raw7161; decide +kernel
      have hl : raw7161step0Labels = raw7161Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7161 raw7161Labels permutation674 permutation3
    mixedMoment B raw7161step0 raw7161step0Labels = mixedMoment B raw7161step1 raw7161step1Labels := by
      have ha : raw7161step1 = -raw7161step0 := by apply Matrix.ext; change ∀ i j, raw7161step1 i j = -(raw7161step0 i j); unfold raw7161step1 raw7161step0; decide +kernel
      have hl : raw7161step1Labels = raw7161step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2450 node2450Labels := by rfl

def raw7162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw7162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw7162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw7162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw7162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7162 raw7162Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw7162 raw7162Labels = mixedMoment B raw7162step0 raw7162step0Labels := by
      have hz : ∀ j, raw7162 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7162step0 = (fun i j => raw7162 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7162step0 raw7162; decide +kernel
      have hl : raw7162step0Labels = raw7162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7162 raw7162Labels permutation520 hz
    mixedMoment B raw7162step0 raw7162step0Labels = mixedMoment B raw7162step1 raw7162step1Labels := by
      have ha : raw7162step1 = (fun i j => raw7162step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7162step1 raw7162step0; decide +kernel
      have hl : raw7162step1Labels = raw7162step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7162step0 raw7162step0Labels permutation137 permutation3
    mixedMoment B raw7162step1 raw7162step1Labels = mixedMoment B raw7162step2 raw7162step2Labels := by
      have ha : raw7162step2 = -raw7162step1 := by apply Matrix.ext; change ∀ i j, raw7162step2 i j = -(raw7162step1 i j); unfold raw7162step2 raw7162step1; decide +kernel
      have hl : raw7162step2Labels = raw7162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw7163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7163step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7163step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7163 raw7163Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw7163 raw7163Labels = mixedMoment B raw7163step0 raw7163step0Labels := by
      have ha : raw7163step0 = (fun i j => raw7163 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7163step0 raw7163; decide +kernel
      have hl : raw7163step0Labels = raw7163Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7163 raw7163Labels permutation164 permutation7
    mixedMoment B raw7163step0 raw7163step0Labels = mixedMoment B raw7163step1 raw7163step1Labels := by
      have ha : raw7163step1 = -raw7163step0 := by apply Matrix.ext; change ∀ i j, raw7163step1 i j = -(raw7163step0 i j); unfold raw7163step1 raw7163step0; decide +kernel
      have hl : raw7163step1Labels = raw7163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7163step1 raw7163step1Labels = mixedMoment B raw7163step2 raw7163step2Labels := by
      have ha : raw7163step2 = raw7163step1 := by apply Matrix.ext; unfold raw7163step2 raw7163step1; decide +kernel
      have hl : raw7163step1Labels = labelEmbedding1 ∘ raw7163step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7163step1 raw7163step1Labels raw7163step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw7164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7164step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7164 raw7164Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw7164 raw7164Labels = mixedMoment B raw7164step0 raw7164step0Labels := by
      have ha : raw7164step0 = (fun i j => raw7164 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7164step0 raw7164; decide +kernel
      have hl : raw7164step0Labels = raw7164Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7164 raw7164Labels permutation164 permutation7
    mixedMoment B raw7164step0 raw7164step0Labels = mixedMoment B raw7164step1 raw7164step1Labels := by
      have ha : raw7164step1 = -raw7164step0 := by apply Matrix.ext; change ∀ i j, raw7164step1 i j = -(raw7164step0 i j); unfold raw7164step1 raw7164step0; decide +kernel
      have hl : raw7164step1Labels = raw7164step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7164step1 raw7164step1Labels = mixedMoment B raw7164step2 raw7164step2Labels := by
      have ha : raw7164step2 = raw7164step1 := by apply Matrix.ext; unfold raw7164step2 raw7164step1; decide +kernel
      have hl : raw7164step1Labels = labelEmbedding1 ∘ raw7164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7164step1 raw7164step1Labels raw7164step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw7165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7165step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7165step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7165 raw7165Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw7165 raw7165Labels = mixedMoment B raw7165step0 raw7165step0Labels := by
      have ha : raw7165step0 = (fun i j => raw7165 (permutation166 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7165step0 raw7165; decide +kernel
      have hl : raw7165step0Labels = raw7165Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7165 raw7165Labels permutation166 permutation7
    mixedMoment B raw7165step0 raw7165step0Labels = mixedMoment B raw7165step1 raw7165step1Labels := by
      have ha : raw7165step1 = -raw7165step0 := by apply Matrix.ext; change ∀ i j, raw7165step1 i j = -(raw7165step0 i j); unfold raw7165step1 raw7165step0; decide +kernel
      have hl : raw7165step1Labels = raw7165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7165step1 raw7165step1Labels = mixedMoment B raw7165step2 raw7165step2Labels := by
      have ha : raw7165step2 = raw7165step1 := by apply Matrix.ext; unfold raw7165step2 raw7165step1; decide +kernel
      have hl : raw7165step1Labels = labelEmbedding1 ∘ raw7165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7165step1 raw7165step1Labels raw7165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw7166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw7166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw7166step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7166step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7166step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7166step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7166step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7166 raw7166Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw7166 raw7166Labels = mixedMoment B raw7166step0 raw7166step0Labels := by
      have hz : ∀ j, raw7166 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7166step0 = (fun i j => raw7166 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7166step0 raw7166; decide +kernel
      have hl : raw7166step0Labels = raw7166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7166 raw7166Labels permutation520 hz
    mixedMoment B raw7166step0 raw7166step0Labels = mixedMoment B raw7166step1 raw7166step1Labels := by
      have ha : raw7166step1 = (fun i j => raw7166step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7166step1 raw7166step0; decide +kernel
      have hl : raw7166step1Labels = raw7166step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7166step0 raw7166step0Labels permutation32 permutation7
    mixedMoment B raw7166step1 raw7166step1Labels = mixedMoment B raw7166step2 raw7166step2Labels := by
      have ha : raw7166step2 = -raw7166step1 := by apply Matrix.ext; change ∀ i j, raw7166step2 i j = -(raw7166step1 i j); unfold raw7166step2 raw7166step1; decide +kernel
      have hl : raw7166step2Labels = raw7166step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7166step2 raw7166step2Labels = mixedMoment B raw7166step3 raw7166step3Labels := by
      have ha : raw7166step3 = raw7166step2 := by apply Matrix.ext; unfold raw7166step3 raw7166step2; decide +kernel
      have hl : raw7166step2Labels = labelEmbedding1 ∘ raw7166step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7166step2 raw7166step2Labels raw7166step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw7167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7167step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7167 raw7167Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw7167 raw7167Labels = mixedMoment B raw7167step0 raw7167step0Labels := by
      have ha : raw7167step0 = (fun i j => raw7167 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7167step0 raw7167; decide +kernel
      have hl : raw7167step0Labels = raw7167Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7167 raw7167Labels permutation164 permutation7
    mixedMoment B raw7167step0 raw7167step0Labels = mixedMoment B raw7167step1 raw7167step1Labels := by
      have ha : raw7167step1 = -raw7167step0 := by apply Matrix.ext; change ∀ i j, raw7167step1 i j = -(raw7167step0 i j); unfold raw7167step1 raw7167step0; decide +kernel
      have hl : raw7167step1Labels = raw7167step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7167step1 raw7167step1Labels = mixedMoment B raw7167step2 raw7167step2Labels := by
      have ha : raw7167step2 = raw7167step1 := by apply Matrix.ext; unfold raw7167step2 raw7167step1; decide +kernel
      have hl : raw7167step1Labels = labelEmbedding1 ∘ raw7167step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7167step1 raw7167step1Labels raw7167step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
