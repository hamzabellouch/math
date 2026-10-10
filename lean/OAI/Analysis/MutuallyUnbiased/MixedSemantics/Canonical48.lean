import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6144step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6144step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6144 raw6144Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw6144 raw6144Labels = mixedMoment B raw6144step0 raw6144step0Labels := by
      have hz : ∀ j, raw6144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6144step0 = (fun i j => raw6144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6144step0 raw6144; decide +kernel
      have hl : raw6144step0Labels = raw6144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6144 raw6144Labels permutation346 hz
    mixedMoment B raw6144step0 raw6144step0Labels = mixedMoment B raw6144step1 raw6144step1Labels := by
      have ha : raw6144step1 = (fun i j => raw6144step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6144step1 raw6144step0; decide +kernel
      have hl : raw6144step1Labels = raw6144step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6144step0 raw6144step0Labels permutation34 permutation2
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw6145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6145 raw6145Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw6145 raw6145Labels = mixedMoment B raw6145step0 raw6145step0Labels := by
      have hz : ∀ j, raw6145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6145step0 = (fun i j => raw6145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6145step0 raw6145; decide +kernel
      have hl : raw6145step0Labels = raw6145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6145 raw6145Labels permutation346 hz
    mixedMoment B raw6145step0 raw6145step0Labels = mixedMoment B raw6145step1 raw6145step1Labels := by
      have ha : raw6145step1 = (fun i j => raw6145step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6145step1 raw6145step0; decide +kernel
      have hl : raw6145step1Labels = raw6145step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6145step0 raw6145step0Labels permutation36 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw6146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6146 raw6146Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw6146 raw6146Labels = mixedMoment B raw6146step0 raw6146step0Labels := by
      have hz : ∀ j, raw6146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6146step0 = (fun i j => raw6146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6146step0 raw6146; decide +kernel
      have hl : raw6146step0Labels = raw6146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6146 raw6146Labels permutation346 hz
    mixedMoment B raw6146step0 raw6146step0Labels = mixedMoment B raw6146step1 raw6146step1Labels := by
      have ha : raw6146step1 = (fun i j => raw6146step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6146step1 raw6146step0; decide +kernel
      have hl : raw6146step1Labels = raw6146step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6146step0 raw6146step0Labels permutation33 permutation2
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw6147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6147 raw6147Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw6147 raw6147Labels = mixedMoment B raw6147step0 raw6147step0Labels := by
      have hz : ∀ j, raw6147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6147step0 = (fun i j => raw6147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6147step0 raw6147; decide +kernel
      have hl : raw6147step0Labels = raw6147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6147 raw6147Labels permutation346 hz
    mixedMoment B raw6147step0 raw6147step0Labels = mixedMoment B raw6147step1 raw6147step1Labels := by
      have ha : raw6147step1 = (fun i j => raw6147step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6147step1 raw6147step0; decide +kernel
      have hl : raw6147step1Labels = raw6147step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6147step0 raw6147step0Labels permutation33 permutation2
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw6148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6148step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6148 raw6148Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw6148 raw6148Labels = mixedMoment B raw6148step0 raw6148step0Labels := by
      have ha : raw6148step0 = (fun i j => raw6148 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6148step0 raw6148; decide +kernel
      have hl : raw6148step0Labels = raw6148Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6148 raw6148Labels permutation177 permutation2
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw6149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6149 raw6149Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw6149 raw6149Labels = mixedMoment B raw6149step0 raw6149step0Labels := by
      have hz : ∀ j, raw6149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6149step0 = (fun i j => raw6149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6149step0 raw6149; decide +kernel
      have hl : raw6149step0Labels = raw6149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6149 raw6149Labels permutation346 hz
    mixedMoment B raw6149step0 raw6149step0Labels = mixedMoment B raw6149step1 raw6149step1Labels := by
      have ha : raw6149step1 = (fun i j => raw6149step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6149step1 raw6149step0; decide +kernel
      have hl : raw6149step1Labels = raw6149step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6149step0 raw6149step0Labels permutation39 permutation2
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw6150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6150 raw6150Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw6150 raw6150Labels = mixedMoment B raw6150step0 raw6150step0Labels := by
      have hz : ∀ j, raw6150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6150step0 = (fun i j => raw6150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6150step0 raw6150; decide +kernel
      have hl : raw6150step0Labels = raw6150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6150 raw6150Labels permutation346 hz
    mixedMoment B raw6150step0 raw6150step0Labels = mixedMoment B raw6150step1 raw6150step1Labels := by
      have ha : raw6150step1 = (fun i j => raw6150step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6150step1 raw6150step0; decide +kernel
      have hl : raw6150step1Labels = raw6150step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6150step0 raw6150step0Labels permutation33 permutation2
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw6151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw6151step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw6151step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6151 raw6151Labels = mixedMoment B node4588 node4588Labels := by
  calc
    mixedMoment B raw6151 raw6151Labels = mixedMoment B raw6151step0 raw6151step0Labels := by
      have hz : ∀ j, raw6151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6151step0 = (fun i j => raw6151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6151step0 raw6151; decide +kernel
      have hl : raw6151step0Labels = raw6151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6151 raw6151Labels permutation346 hz
    mixedMoment B raw6151step0 raw6151step0Labels = mixedMoment B raw6151step1 raw6151step1Labels := by
      have ha : raw6151step1 = (fun i j => raw6151step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6151step1 raw6151step0; decide +kernel
      have hl : raw6151step1Labels = raw6151step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6151step0 raw6151step0Labels permutation38 permutation3
    mixedMoment B raw6151step1 raw6151step1Labels = mixedMoment B raw6151step2 raw6151step2Labels := by
      have ha : raw6151step2 = raw6151step1 := by apply Matrix.ext; unfold raw6151step2 raw6151step1; decide +kernel
      have hl : raw6151step1Labels = labelEmbedding6 ∘ raw6151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6151step1 raw6151step1Labels raw6151step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4588 node4588Labels := by rfl

def raw6152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw6152step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw6152step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6152step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw6152step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6152 raw6152Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw6152 raw6152Labels = mixedMoment B raw6152step0 raw6152step0Labels := by
      have hz : ∀ j, raw6152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6152step0 = (fun i j => raw6152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6152step0 raw6152; decide +kernel
      have hl : raw6152step0Labels = raw6152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6152 raw6152Labels permutation346 hz
    mixedMoment B raw6152step0 raw6152step0Labels = mixedMoment B raw6152step1 raw6152step1Labels := by
      have ha : raw6152step1 = (fun i j => raw6152step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6152step1 raw6152step0; decide +kernel
      have hl : raw6152step1Labels = raw6152step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6152step0 raw6152step0Labels permutation151 permutation3
    mixedMoment B raw6152step1 raw6152step1Labels = mixedMoment B raw6152step2 raw6152step2Labels := by
      have ha : raw6152step2 = -raw6152step1 := by apply Matrix.ext; change ∀ i j, raw6152step2 i j = -(raw6152step1 i j); unfold raw6152step2 raw6152step1; decide +kernel
      have hl : raw6152step2Labels = raw6152step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6152step2 raw6152step2Labels = mixedMoment B raw6152step3 raw6152step3Labels := by
      have ha : raw6152step3 = raw6152step2 := by apply Matrix.ext; unfold raw6152step3 raw6152step2; decide +kernel
      have hl : raw6152step2Labels = labelEmbedding6 ∘ raw6152step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6152step2 raw6152step2Labels raw6152step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw6153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw6153step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw6153step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6153 raw6153Labels = mixedMoment B node4824 node4824Labels := by
  calc
    mixedMoment B raw6153 raw6153Labels = mixedMoment B raw6153step0 raw6153step0Labels := by
      have ha : raw6153step0 = (fun i j => raw6153 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6153step0 raw6153; decide +kernel
      have hl : raw6153step0Labels = raw6153Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6153 raw6153Labels permutation622 permutation5
    mixedMoment B raw6153step0 raw6153step0Labels = mixedMoment B raw6153step1 raw6153step1Labels := by
      have ha : raw6153step1 = raw6153step0 := by apply Matrix.ext; unfold raw6153step1 raw6153step0; decide +kernel
      have hl : raw6153step0Labels = labelEmbedding8 ∘ raw6153step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6153step0 raw6153step0Labels raw6153step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4824 node4824Labels := by rfl

def raw6154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6154step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6154 raw6154Labels = mixedMoment B node4829 node4829Labels := by
  calc
    mixedMoment B raw6154 raw6154Labels = mixedMoment B raw6154step0 raw6154step0Labels := by
      have hz : ∀ j, raw6154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6154step0 = (fun i j => raw6154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6154step0 raw6154; decide +kernel
      have hl : raw6154step0Labels = raw6154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6154 raw6154Labels permutation346 hz
    mixedMoment B raw6154step0 raw6154step0Labels = mixedMoment B raw6154step1 raw6154step1Labels := by
      have ha : raw6154step1 = (fun i j => raw6154step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6154step1 raw6154step0; decide +kernel
      have hl : raw6154step1Labels = raw6154step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6154step0 raw6154step0Labels permutation138 permutation5
    mixedMoment B raw6154step1 raw6154step1Labels = mixedMoment B raw6154step2 raw6154step2Labels := by
      have ha : raw6154step2 = raw6154step1 := by apply Matrix.ext; unfold raw6154step2 raw6154step1; decide +kernel
      have hl : raw6154step1Labels = labelEmbedding8 ∘ raw6154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6154step1 raw6154step1Labels raw6154step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4829 node4829Labels := by rfl

def raw6155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6155step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6155 raw6155Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw6155 raw6155Labels = mixedMoment B raw6155step0 raw6155step0Labels := by
      have hz : ∀ j, raw6155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6155step0 = (fun i j => raw6155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6155step0 raw6155; decide +kernel
      have hl : raw6155step0Labels = raw6155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6155 raw6155Labels permutation346 hz
    mixedMoment B raw6155step0 raw6155step0Labels = mixedMoment B raw6155step1 raw6155step1Labels := by
      have ha : raw6155step1 = (fun i j => raw6155step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6155step1 raw6155step0; decide +kernel
      have hl : raw6155step1Labels = raw6155step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6155step0 raw6155step0Labels permutation136 permutation5
    mixedMoment B raw6155step1 raw6155step1Labels = mixedMoment B raw6155step2 raw6155step2Labels := by
      have ha : raw6155step2 = raw6155step1 := by apply Matrix.ext; unfold raw6155step2 raw6155step1; decide +kernel
      have hl : raw6155step1Labels = labelEmbedding8 ∘ raw6155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6155step1 raw6155step1Labels raw6155step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw6156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6156step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw6156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw6156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6156 raw6156Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw6156 raw6156Labels = mixedMoment B raw6156step0 raw6156step0Labels := by
      have hz : ∀ j, raw6156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6156step0 = (fun i j => raw6156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6156step0 raw6156; decide +kernel
      have hl : raw6156step0Labels = raw6156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6156 raw6156Labels permutation346 hz
    mixedMoment B raw6156step0 raw6156step0Labels = mixedMoment B raw6156step1 raw6156step1Labels := by
      have ha : raw6156step1 = (fun i j => raw6156step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6156step1 raw6156step0; decide +kernel
      have hl : raw6156step1Labels = raw6156step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6156step0 raw6156step0Labels permutation151 permutation3
    mixedMoment B raw6156step1 raw6156step1Labels = mixedMoment B raw6156step2 raw6156step2Labels := by
      have ha : raw6156step2 = -raw6156step1 := by apply Matrix.ext; change ∀ i j, raw6156step2 i j = -(raw6156step1 i j); unfold raw6156step2 raw6156step1; decide +kernel
      have hl : raw6156step2Labels = raw6156step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw6157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6157step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6157 raw6157Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw6157 raw6157Labels = mixedMoment B raw6157step0 raw6157step0Labels := by
      have ha : raw6157step0 = (fun i j => raw6157 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6157step0 raw6157; decide +kernel
      have hl : raw6157step0Labels = raw6157Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6157 raw6157Labels permutation676 permutation3
    mixedMoment B raw6157step0 raw6157step0Labels = mixedMoment B raw6157step1 raw6157step1Labels := by
      have ha : raw6157step1 = -raw6157step0 := by apply Matrix.ext; change ∀ i j, raw6157step1 i j = -(raw6157step0 i j); unfold raw6157step1 raw6157step0; decide +kernel
      have hl : raw6157step1Labels = raw6157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw6158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6158 raw6158Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw6158 raw6158Labels = mixedMoment B raw6158step0 raw6158step0Labels := by
      have hz : ∀ j, raw6158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6158step0 = (fun i j => raw6158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6158step0 raw6158; decide +kernel
      have hl : raw6158step0Labels = raw6158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6158 raw6158Labels permutation346 hz
    mixedMoment B raw6158step0 raw6158step0Labels = mixedMoment B raw6158step1 raw6158step1Labels := by
      have ha : raw6158step1 = (fun i j => raw6158step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6158step1 raw6158step0; decide +kernel
      have hl : raw6158step1Labels = raw6158step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6158step0 raw6158step0Labels permutation149 permutation3
    mixedMoment B raw6158step1 raw6158step1Labels = mixedMoment B raw6158step2 raw6158step2Labels := by
      have ha : raw6158step2 = -raw6158step1 := by apply Matrix.ext; change ∀ i j, raw6158step2 i j = -(raw6158step1 i j); unfold raw6158step2 raw6158step1; decide +kernel
      have hl : raw6158step2Labels = raw6158step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw6159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6159Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6159step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6159step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6159 raw6159Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw6159 raw6159Labels = mixedMoment B raw6159step0 raw6159step0Labels := by
      have hz : ∀ j, raw6159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6159step0 = (fun i j => raw6159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6159step0 raw6159; decide +kernel
      have hl : raw6159step0Labels = raw6159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6159 raw6159Labels permutation346 hz
    mixedMoment B raw6159step0 raw6159step0Labels = mixedMoment B raw6159step1 raw6159step1Labels := by
      have ha : raw6159step1 = (fun i j => raw6159step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6159step1 raw6159step0; decide +kernel
      have hl : raw6159step1Labels = raw6159step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6159step0 raw6159step0Labels permutation121 permutation6
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw6160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6160Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6160step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6160 raw6160Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw6160 raw6160Labels = mixedMoment B raw6160step0 raw6160step0Labels := by
      have hz : ∀ j, raw6160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6160step0 = (fun i j => raw6160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6160step0 raw6160; decide +kernel
      have hl : raw6160step0Labels = raw6160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6160 raw6160Labels permutation346 hz
    mixedMoment B raw6160step0 raw6160step0Labels = mixedMoment B raw6160step1 raw6160step1Labels := by
      have ha : raw6160step1 = (fun i j => raw6160step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6160step1 raw6160step0; decide +kernel
      have hl : raw6160step1Labels = raw6160step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6160step0 raw6160step0Labels permutation121 permutation6
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw6161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6161Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6161step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6161step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6161 raw6161Labels = mixedMoment B node1230 node1230Labels := by
  calc
    mixedMoment B raw6161 raw6161Labels = mixedMoment B raw6161step0 raw6161step0Labels := by
      have hz : ∀ j, raw6161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6161step0 = (fun i j => raw6161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6161step0 raw6161; decide +kernel
      have hl : raw6161step0Labels = raw6161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6161 raw6161Labels permutation346 hz
    mixedMoment B raw6161step0 raw6161step0Labels = mixedMoment B raw6161step1 raw6161step1Labels := by
      have ha : raw6161step1 = (fun i j => raw6161step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6161step1 raw6161step0; decide +kernel
      have hl : raw6161step1Labels = raw6161step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6161step0 raw6161step0Labels permutation40 permutation3
    _ = mixedMoment B node1230 node1230Labels := by rfl

def raw6162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6162step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6162 raw6162Labels = mixedMoment B node2922 node2922Labels := by
  calc
    mixedMoment B raw6162 raw6162Labels = mixedMoment B raw6162step0 raw6162step0Labels := by
      have ha : raw6162step0 = (fun i j => raw6162 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6162step0 raw6162; decide +kernel
      have hl : raw6162step0Labels = raw6162Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6162 raw6162Labels permutation184 permutation3
    _ = mixedMoment B node2922 node2922Labels := by rfl

def raw6163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6163step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6163 raw6163Labels = mixedMoment B node2876 node2876Labels := by
  calc
    mixedMoment B raw6163 raw6163Labels = mixedMoment B raw6163step0 raw6163step0Labels := by
      have hz : ∀ j, raw6163 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6163step0 = (fun i j => raw6163 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6163step0 raw6163; decide +kernel
      have hl : raw6163step0Labels = raw6163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6163 raw6163Labels permutation346 hz
    mixedMoment B raw6163step0 raw6163step0Labels = mixedMoment B raw6163step1 raw6163step1Labels := by
      have ha : raw6163step1 = (fun i j => raw6163step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6163step1 raw6163step0; decide +kernel
      have hl : raw6163step1Labels = raw6163step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6163step0 raw6163step0Labels permutation40 permutation3
    _ = mixedMoment B node2876 node2876Labels := by rfl

def raw6164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6164step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6164 raw6164Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw6164 raw6164Labels = mixedMoment B raw6164step0 raw6164step0Labels := by
      have hz : ∀ j, raw6164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6164step0 = (fun i j => raw6164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6164step0 raw6164; decide +kernel
      have hl : raw6164step0Labels = raw6164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6164 raw6164Labels permutation346 hz
    mixedMoment B raw6164step0 raw6164step0Labels = mixedMoment B raw6164step1 raw6164step1Labels := by
      have ha : raw6164step1 = (fun i j => raw6164step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6164step1 raw6164step0; decide +kernel
      have hl : raw6164step1Labels = raw6164step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6164step0 raw6164step0Labels permutation46 permutation3
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw6165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6165 raw6165Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw6165 raw6165Labels = mixedMoment B raw6165step0 raw6165step0Labels := by
      have hz : ∀ j, raw6165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6165step0 = (fun i j => raw6165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6165step0 raw6165; decide +kernel
      have hl : raw6165step0Labels = raw6165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6165 raw6165Labels permutation346 hz
    mixedMoment B raw6165step0 raw6165step0Labels = mixedMoment B raw6165step1 raw6165step1Labels := by
      have ha : raw6165step1 = (fun i j => raw6165step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6165step1 raw6165step0; decide +kernel
      have hl : raw6165step1Labels = raw6165step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6165step0 raw6165step0Labels permutation41 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw6166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6166step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6166 raw6166Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw6166 raw6166Labels = mixedMoment B raw6166step0 raw6166step0Labels := by
      have ha : raw6166step0 = (fun i j => raw6166 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6166step0 raw6166; decide +kernel
      have hl : raw6166step0Labels = raw6166Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6166 raw6166Labels permutation202 permutation3
    _ = mixedMoment B node1210 node1210Labels := by rfl

def raw6167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6167 raw6167Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw6167 raw6167Labels = mixedMoment B raw6167step0 raw6167step0Labels := by
      have ha : raw6167step0 = (fun i j => raw6167 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6167step0 raw6167; decide +kernel
      have hl : raw6167step0Labels = raw6167Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6167 raw6167Labels permutation160 permutation3
    _ = mixedMoment B node2984 node2984Labels := by rfl

def raw6168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6168step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6168 raw6168Labels = mixedMoment B node2860 node2860Labels := by
  calc
    mixedMoment B raw6168 raw6168Labels = mixedMoment B raw6168step0 raw6168step0Labels := by
      have ha : raw6168step0 = (fun i j => raw6168 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6168step0 raw6168; decide +kernel
      have hl : raw6168step0Labels = raw6168Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6168 raw6168Labels permutation202 permutation3
    _ = mixedMoment B node2860 node2860Labels := by rfl

def raw6169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6169 raw6169Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw6169 raw6169Labels = mixedMoment B raw6169step0 raw6169step0Labels := by
      have ha : raw6169step0 = (fun i j => raw6169 (permutation234 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6169step0 raw6169; decide +kernel
      have hl : raw6169step0Labels = raw6169Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6169 raw6169Labels permutation234 permutation3
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw6170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6170 raw6170Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw6170 raw6170Labels = mixedMoment B raw6170step0 raw6170step0Labels := by
      have ha : raw6170step0 = (fun i j => raw6170 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6170step0 raw6170; decide +kernel
      have hl : raw6170step0Labels = raw6170Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6170 raw6170Labels permutation202 permutation3
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw6171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6171 raw6171Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw6171 raw6171Labels = mixedMoment B raw6171step0 raw6171step0Labels := by
      have hz : ∀ j, raw6171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6171step0 = (fun i j => raw6171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6171step0 raw6171; decide +kernel
      have hl : raw6171step0Labels = raw6171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6171 raw6171Labels permutation346 hz
    mixedMoment B raw6171step0 raw6171step0Labels = mixedMoment B raw6171step1 raw6171step1Labels := by
      have ha : raw6171step1 = (fun i j => raw6171step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6171step1 raw6171step0; decide +kernel
      have hl : raw6171step1Labels = raw6171step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6171step0 raw6171step0Labels permutation34 permutation3
    _ = mixedMoment B node1261 node1261Labels := by rfl

def raw6172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6172step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6172 raw6172Labels = mixedMoment B node2997 node2997Labels := by
  calc
    mixedMoment B raw6172 raw6172Labels = mixedMoment B raw6172step0 raw6172step0Labels := by
      have hz : ∀ j, raw6172 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6172step0 = (fun i j => raw6172 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6172step0 raw6172; decide +kernel
      have hl : raw6172step0Labels = raw6172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6172 raw6172Labels permutation346 hz
    mixedMoment B raw6172step0 raw6172step0Labels = mixedMoment B raw6172step1 raw6172step1Labels := by
      have ha : raw6172step1 = (fun i j => raw6172step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6172step1 raw6172step0; decide +kernel
      have hl : raw6172step1Labels = raw6172step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6172step0 raw6172step0Labels permutation34 permutation3
    _ = mixedMoment B node2997 node2997Labels := by rfl

def raw6173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6173step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6173 raw6173Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw6173 raw6173Labels = mixedMoment B raw6173step0 raw6173step0Labels := by
      have ha : raw6173step0 = (fun i j => raw6173 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6173step0 raw6173; decide +kernel
      have hl : raw6173step0Labels = raw6173Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6173 raw6173Labels permutation178 permutation3
    _ = mixedMoment B node2933 node2933Labels := by rfl

def raw6174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6174 raw6174Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw6174 raw6174Labels = mixedMoment B raw6174step0 raw6174step0Labels := by
      have hz : ∀ j, raw6174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6174step0 = (fun i j => raw6174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6174step0 raw6174; decide +kernel
      have hl : raw6174step0Labels = raw6174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6174 raw6174Labels permutation346 hz
    mixedMoment B raw6174step0 raw6174step0Labels = mixedMoment B raw6174step1 raw6174step1Labels := by
      have ha : raw6174step1 = (fun i j => raw6174step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6174step1 raw6174step0; decide +kernel
      have hl : raw6174step1Labels = raw6174step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6174step0 raw6174step0Labels permutation44 permutation3
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw6175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6175 raw6175Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw6175 raw6175Labels = mixedMoment B raw6175step0 raw6175step0Labels := by
      have hz : ∀ j, raw6175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6175step0 = (fun i j => raw6175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6175step0 raw6175; decide +kernel
      have hl : raw6175step0Labels = raw6175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6175 raw6175Labels permutation346 hz
    mixedMoment B raw6175step0 raw6175step0Labels = mixedMoment B raw6175step1 raw6175step1Labels := by
      have ha : raw6175step1 = (fun i j => raw6175step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6175step1 raw6175step0; decide +kernel
      have hl : raw6175step1Labels = raw6175step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6175step0 raw6175step0Labels permutation34 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw6176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6176step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6176 raw6176Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw6176 raw6176Labels = mixedMoment B raw6176step0 raw6176step0Labels := by
      have hz : ∀ j, raw6176 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6176step0 = (fun i j => raw6176 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6176step0 raw6176; decide +kernel
      have hl : raw6176step0Labels = raw6176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6176 raw6176Labels permutation346 hz
    mixedMoment B raw6176step0 raw6176step0Labels = mixedMoment B raw6176step1 raw6176step1Labels := by
      have ha : raw6176step1 = (fun i j => raw6176step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6176step1 raw6176step0; decide +kernel
      have hl : raw6176step1Labels = raw6176step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6176step0 raw6176step0Labels permutation38 permutation3
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw6177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6177 raw6177Labels = mixedMoment B node2990 node2990Labels := by
  calc
    mixedMoment B raw6177 raw6177Labels = mixedMoment B raw6177step0 raw6177step0Labels := by
      have hz : ∀ j, raw6177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6177step0 = (fun i j => raw6177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6177step0 raw6177; decide +kernel
      have hl : raw6177step0Labels = raw6177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6177 raw6177Labels permutation346 hz
    mixedMoment B raw6177step0 raw6177step0Labels = mixedMoment B raw6177step1 raw6177step1Labels := by
      have ha : raw6177step1 = (fun i j => raw6177step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6177step1 raw6177step0; decide +kernel
      have hl : raw6177step1Labels = raw6177step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6177step0 raw6177step0Labels permutation32 permutation3
    _ = mixedMoment B node2990 node2990Labels := by rfl

def raw6178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6178step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6178 raw6178Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw6178 raw6178Labels = mixedMoment B raw6178step0 raw6178step0Labels := by
      have ha : raw6178step0 = (fun i j => raw6178 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6178step0 raw6178; decide +kernel
      have hl : raw6178step0Labels = raw6178Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6178 raw6178Labels permutation182 permutation3
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw6179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6179step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6179step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6179step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6179 raw6179Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw6179 raw6179Labels = mixedMoment B raw6179step0 raw6179step0Labels := by
      have hz : ∀ j, raw6179 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6179step0 = (fun i j => raw6179 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6179step0 raw6179; decide +kernel
      have hl : raw6179step0Labels = raw6179Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6179 raw6179Labels permutation346 hz
    mixedMoment B raw6179step0 raw6179step0Labels = mixedMoment B raw6179step1 raw6179step1Labels := by
      have ha : raw6179step1 = (fun i j => raw6179step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6179step1 raw6179step0; decide +kernel
      have hl : raw6179step1Labels = raw6179step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6179step0 raw6179step0Labels permutation38 permutation3
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw6180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6180 raw6180Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw6180 raw6180Labels = mixedMoment B raw6180step0 raw6180step0Labels := by
      have hz : ∀ j, raw6180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6180step0 = (fun i j => raw6180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6180step0 raw6180; decide +kernel
      have hl : raw6180step0Labels = raw6180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6180 raw6180Labels permutation346 hz
    mixedMoment B raw6180step0 raw6180step0Labels = mixedMoment B raw6180step1 raw6180step1Labels := by
      have ha : raw6180step1 = (fun i j => raw6180step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6180step1 raw6180step0; decide +kernel
      have hl : raw6180step1Labels = raw6180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6180step0 raw6180step0Labels permutation39 permutation3
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw6181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6181Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6181step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw6181step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6181 raw6181Labels = mixedMoment B node1211 node1211Labels := by
  calc
    mixedMoment B raw6181 raw6181Labels = mixedMoment B raw6181step0 raw6181step0Labels := by
      have hz : ∀ j, raw6181 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6181step0 = (fun i j => raw6181 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6181step0 raw6181; decide +kernel
      have hl : raw6181step0Labels = raw6181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6181 raw6181Labels permutation346 hz
    mixedMoment B raw6181step0 raw6181step0Labels = mixedMoment B raw6181step1 raw6181step1Labels := by
      have ha : raw6181step1 = (fun i j => raw6181step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6181step1 raw6181step0; decide +kernel
      have hl : raw6181step1Labels = raw6181step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6181step0 raw6181step0Labels permutation38 permutation3
    _ = mixedMoment B node1211 node1211Labels := by rfl

def raw6182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6182Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6182step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw6182step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6182step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw6182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6182 raw6182Labels = mixedMoment B node2090 node2090Labels := by
  calc
    mixedMoment B raw6182 raw6182Labels = mixedMoment B raw6182step0 raw6182step0Labels := by
      have hz : ∀ j, raw6182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6182step0 = (fun i j => raw6182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6182step0 raw6182; decide +kernel
      have hl : raw6182step0Labels = raw6182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6182 raw6182Labels permutation346 hz
    mixedMoment B raw6182step0 raw6182step0Labels = mixedMoment B raw6182step1 raw6182step1Labels := by
      have ha : raw6182step1 = (fun i j => raw6182step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6182step1 raw6182step0; decide +kernel
      have hl : raw6182step1Labels = raw6182step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6182step0 raw6182step0Labels permutation151 permutation3
    mixedMoment B raw6182step1 raw6182step1Labels = mixedMoment B raw6182step2 raw6182step2Labels := by
      have ha : raw6182step2 = -raw6182step1 := by apply Matrix.ext; change ∀ i j, raw6182step2 i j = -(raw6182step1 i j); unfold raw6182step2 raw6182step1; decide +kernel
      have hl : raw6182step2Labels = raw6182step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2090 node2090Labels := by rfl

def raw6183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6183Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw6183step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw6183step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6183 raw6183Labels = mixedMoment B node2071 node2071Labels := by
  calc
    mixedMoment B raw6183 raw6183Labels = mixedMoment B raw6183step0 raw6183step0Labels := by
      have ha : raw6183step0 = (fun i j => raw6183 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6183step0 raw6183; decide +kernel
      have hl : raw6183step0Labels = raw6183Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6183 raw6183Labels permutation676 permutation3
    mixedMoment B raw6183step0 raw6183step0Labels = mixedMoment B raw6183step1 raw6183step1Labels := by
      have ha : raw6183step1 = -raw6183step0 := by apply Matrix.ext; change ∀ i j, raw6183step1 i j = -(raw6183step0 i j); unfold raw6183step1 raw6183step0; decide +kernel
      have hl : raw6183step1Labels = raw6183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2071 node2071Labels := by rfl

def raw6184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6184Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6184step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw6184step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw6184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6184 raw6184Labels = mixedMoment B node2080 node2080Labels := by
  calc
    mixedMoment B raw6184 raw6184Labels = mixedMoment B raw6184step0 raw6184step0Labels := by
      have hz : ∀ j, raw6184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6184step0 = (fun i j => raw6184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6184step0 raw6184; decide +kernel
      have hl : raw6184step0Labels = raw6184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6184 raw6184Labels permutation346 hz
    mixedMoment B raw6184step0 raw6184step0Labels = mixedMoment B raw6184step1 raw6184step1Labels := by
      have ha : raw6184step1 = (fun i j => raw6184step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6184step1 raw6184step0; decide +kernel
      have hl : raw6184step1Labels = raw6184step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6184step0 raw6184step0Labels permutation149 permutation3
    mixedMoment B raw6184step1 raw6184step1Labels = mixedMoment B raw6184step2 raw6184step2Labels := by
      have ha : raw6184step2 = -raw6184step1 := by apply Matrix.ext; change ∀ i j, raw6184step2 i j = -(raw6184step1 i j); unfold raw6184step2 raw6184step1; decide +kernel
      have hl : raw6184step2Labels = raw6184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2080 node2080Labels := by rfl

def raw6185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6185Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6185step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw6185step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw6185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6185 raw6185Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw6185 raw6185Labels = mixedMoment B raw6185step0 raw6185step0Labels := by
      have hz : ∀ j, raw6185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6185step0 = (fun i j => raw6185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6185step0 raw6185; decide +kernel
      have hl : raw6185step0Labels = raw6185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6185 raw6185Labels permutation346 hz
    mixedMoment B raw6185step0 raw6185step0Labels = mixedMoment B raw6185step1 raw6185step1Labels := by
      have ha : raw6185step1 = (fun i j => raw6185step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6185step1 raw6185step0; decide +kernel
      have hl : raw6185step1Labels = raw6185step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6185step0 raw6185step0Labels permutation137 permutation3
    mixedMoment B raw6185step1 raw6185step1Labels = mixedMoment B raw6185step2 raw6185step2Labels := by
      have ha : raw6185step2 = -raw6185step1 := by apply Matrix.ext; change ∀ i j, raw6185step2 i j = -(raw6185step1 i j); unfold raw6185step2 raw6185step1; decide +kernel
      have hl : raw6185step2Labels = raw6185step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw6186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6186Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6186step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6186step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6186step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6186step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6186 raw6186Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw6186 raw6186Labels = mixedMoment B raw6186step0 raw6186step0Labels := by
      have hz : ∀ j, raw6186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6186step0 = (fun i j => raw6186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6186step0 raw6186; decide +kernel
      have hl : raw6186step0Labels = raw6186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6186 raw6186Labels permutation346 hz
    mixedMoment B raw6186step0 raw6186step0Labels = mixedMoment B raw6186step1 raw6186step1Labels := by
      have ha : raw6186step1 = (fun i j => raw6186step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6186step1 raw6186step0; decide +kernel
      have hl : raw6186step1Labels = raw6186step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6186step0 raw6186step0Labels permutation36 permutation7
    mixedMoment B raw6186step1 raw6186step1Labels = mixedMoment B raw6186step2 raw6186step2Labels := by
      have ha : raw6186step2 = -raw6186step1 := by apply Matrix.ext; change ∀ i j, raw6186step2 i j = -(raw6186step1 i j); unfold raw6186step2 raw6186step1; decide +kernel
      have hl : raw6186step2Labels = raw6186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6186step2 raw6186step2Labels = mixedMoment B raw6186step3 raw6186step3Labels := by
      have ha : raw6186step3 = raw6186step2 := by apply Matrix.ext; unfold raw6186step3 raw6186step2; decide +kernel
      have hl : raw6186step2Labels = labelEmbedding1 ∘ raw6186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6186step2 raw6186step2Labels raw6186step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw6187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6187Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6187step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6187step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6187step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6187step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6187 raw6187Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw6187 raw6187Labels = mixedMoment B raw6187step0 raw6187step0Labels := by
      have ha : raw6187step0 = (fun i j => raw6187 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6187step0 raw6187; decide +kernel
      have hl : raw6187step0Labels = raw6187Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6187 raw6187Labels permutation156 permutation7
    mixedMoment B raw6187step0 raw6187step0Labels = mixedMoment B raw6187step1 raw6187step1Labels := by
      have ha : raw6187step1 = -raw6187step0 := by apply Matrix.ext; change ∀ i j, raw6187step1 i j = -(raw6187step0 i j); unfold raw6187step1 raw6187step0; decide +kernel
      have hl : raw6187step1Labels = raw6187step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6187step1 raw6187step1Labels = mixedMoment B raw6187step2 raw6187step2Labels := by
      have ha : raw6187step2 = raw6187step1 := by apply Matrix.ext; unfold raw6187step2 raw6187step1; decide +kernel
      have hl : raw6187step1Labels = labelEmbedding1 ∘ raw6187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6187step1 raw6187step1Labels raw6187step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw6188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6188Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6188step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6188step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6188 raw6188Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw6188 raw6188Labels = mixedMoment B raw6188step0 raw6188step0Labels := by
      have hz : ∀ j, raw6188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6188step0 = (fun i j => raw6188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6188step0 raw6188; decide +kernel
      have hl : raw6188step0Labels = raw6188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6188 raw6188Labels permutation346 hz
    mixedMoment B raw6188step0 raw6188step0Labels = mixedMoment B raw6188step1 raw6188step1Labels := by
      have ha : raw6188step1 = (fun i j => raw6188step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6188step1 raw6188step0; decide +kernel
      have hl : raw6188step1Labels = raw6188step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6188step0 raw6188step0Labels permutation135 permutation5
    mixedMoment B raw6188step1 raw6188step1Labels = mixedMoment B raw6188step2 raw6188step2Labels := by
      have ha : raw6188step2 = raw6188step1 := by apply Matrix.ext; unfold raw6188step2 raw6188step1; decide +kernel
      have hl : raw6188step1Labels = labelEmbedding1 ∘ raw6188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6188step1 raw6188step1Labels raw6188step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw6189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6189Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6189step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6189step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6189step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6189 raw6189Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw6189 raw6189Labels = mixedMoment B raw6189step0 raw6189step0Labels := by
      have hz : ∀ j, raw6189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6189step0 = (fun i j => raw6189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6189step0 raw6189; decide +kernel
      have hl : raw6189step0Labels = raw6189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6189 raw6189Labels permutation346 hz
    mixedMoment B raw6189step0 raw6189step0Labels = mixedMoment B raw6189step1 raw6189step1Labels := by
      have ha : raw6189step1 = (fun i j => raw6189step0 (permutation134 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6189step1 raw6189step0; decide +kernel
      have hl : raw6189step1Labels = raw6189step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6189step0 raw6189step0Labels permutation134 permutation5
    mixedMoment B raw6189step1 raw6189step1Labels = mixedMoment B raw6189step2 raw6189step2Labels := by
      have ha : raw6189step2 = raw6189step1 := by apply Matrix.ext; unfold raw6189step2 raw6189step1; decide +kernel
      have hl : raw6189step1Labels = labelEmbedding1 ∘ raw6189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6189step1 raw6189step1Labels raw6189step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw6190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6190Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6190step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw6190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6190step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6190 raw6190Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw6190 raw6190Labels = mixedMoment B raw6190step0 raw6190step0Labels := by
      have hz : ∀ j, raw6190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6190step0 = (fun i j => raw6190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6190step0 raw6190; decide +kernel
      have hl : raw6190step0Labels = raw6190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6190 raw6190Labels permutation346 hz
    mixedMoment B raw6190step0 raw6190step0Labels = mixedMoment B raw6190step1 raw6190step1Labels := by
      have ha : raw6190step1 = (fun i j => raw6190step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6190step1 raw6190step0; decide +kernel
      have hl : raw6190step1Labels = raw6190step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6190step0 raw6190step0Labels permutation36 permutation7
    mixedMoment B raw6190step1 raw6190step1Labels = mixedMoment B raw6190step2 raw6190step2Labels := by
      have ha : raw6190step2 = -raw6190step1 := by apply Matrix.ext; change ∀ i j, raw6190step2 i j = -(raw6190step1 i j); unfold raw6190step2 raw6190step1; decide +kernel
      have hl : raw6190step2Labels = raw6190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6190step2 raw6190step2Labels = mixedMoment B raw6190step3 raw6190step3Labels := by
      have ha : raw6190step3 = raw6190step2 := by apply Matrix.ext; unfold raw6190step3 raw6190step2; decide +kernel
      have hl : raw6190step2Labels = labelEmbedding1 ∘ raw6190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6190step2 raw6190step2Labels raw6190step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw6191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6191Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6191step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw6191step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6191step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6191step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6191 raw6191Labels = mixedMoment B node3287 node3287Labels := by
  calc
    mixedMoment B raw6191 raw6191Labels = mixedMoment B raw6191step0 raw6191step0Labels := by
      have hz : ∀ j, raw6191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6191step0 = (fun i j => raw6191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6191step0 raw6191; decide +kernel
      have hl : raw6191step0Labels = raw6191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6191 raw6191Labels permutation346 hz
    mixedMoment B raw6191step0 raw6191step0Labels = mixedMoment B raw6191step1 raw6191step1Labels := by
      have ha : raw6191step1 = (fun i j => raw6191step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6191step1 raw6191step0; decide +kernel
      have hl : raw6191step1Labels = raw6191step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6191step0 raw6191step0Labels permutation40 permutation5
    mixedMoment B raw6191step1 raw6191step1Labels = mixedMoment B raw6191step2 raw6191step2Labels := by
      have ha : raw6191step2 = -raw6191step1 := by apply Matrix.ext; change ∀ i j, raw6191step2 i j = -(raw6191step1 i j); unfold raw6191step2 raw6191step1; decide +kernel
      have hl : raw6191step2Labels = raw6191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6191step2 raw6191step2Labels = mixedMoment B raw6191step3 raw6191step3Labels := by
      have ha : raw6191step3 = raw6191step2 := by apply Matrix.ext; unfold raw6191step3 raw6191step2; decide +kernel
      have hl : raw6191step2Labels = labelEmbedding1 ∘ raw6191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6191step2 raw6191step2Labels raw6191step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3287 node3287Labels := by rfl

def raw6192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6192Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6192 raw6192Labels = mixedMoment B node3560 node3560Labels := by
  calc
    mixedMoment B raw6192 raw6192Labels = mixedMoment B raw6192step0 raw6192step0Labels := by
      have ha : raw6192step0 = (fun i j => raw6192 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6192step0 raw6192; decide +kernel
      have hl : raw6192step0Labels = raw6192Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6192 raw6192Labels permutation156 permutation7
    mixedMoment B raw6192step0 raw6192step0Labels = mixedMoment B raw6192step1 raw6192step1Labels := by
      have ha : raw6192step1 = -raw6192step0 := by apply Matrix.ext; change ∀ i j, raw6192step1 i j = -(raw6192step0 i j); unfold raw6192step1 raw6192step0; decide +kernel
      have hl : raw6192step1Labels = raw6192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6192step1 raw6192step1Labels = mixedMoment B raw6192step2 raw6192step2Labels := by
      have ha : raw6192step2 = raw6192step1 := by apply Matrix.ext; unfold raw6192step2 raw6192step1; decide +kernel
      have hl : raw6192step1Labels = labelEmbedding1 ∘ raw6192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6192step1 raw6192step1Labels raw6192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3560 node3560Labels := by rfl

def raw6193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6193Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6193step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw6193step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6193step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6193step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6193step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6193 raw6193Labels = mixedMoment B node3575 node3575Labels := by
  calc
    mixedMoment B raw6193 raw6193Labels = mixedMoment B raw6193step0 raw6193step0Labels := by
      have hz : ∀ j, raw6193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6193step0 = (fun i j => raw6193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6193step0 raw6193; decide +kernel
      have hl : raw6193step0Labels = raw6193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6193 raw6193Labels permutation346 hz
    mixedMoment B raw6193step0 raw6193step0Labels = mixedMoment B raw6193step1 raw6193step1Labels := by
      have ha : raw6193step1 = (fun i j => raw6193step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6193step1 raw6193step0; decide +kernel
      have hl : raw6193step1Labels = raw6193step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6193step0 raw6193step0Labels permutation36 permutation7
    mixedMoment B raw6193step1 raw6193step1Labels = mixedMoment B raw6193step2 raw6193step2Labels := by
      have ha : raw6193step2 = -raw6193step1 := by apply Matrix.ext; change ∀ i j, raw6193step2 i j = -(raw6193step1 i j); unfold raw6193step2 raw6193step1; decide +kernel
      have hl : raw6193step2Labels = raw6193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6193step2 raw6193step2Labels = mixedMoment B raw6193step3 raw6193step3Labels := by
      have ha : raw6193step3 = raw6193step2 := by apply Matrix.ext; unfold raw6193step3 raw6193step2; decide +kernel
      have hl : raw6193step2Labels = labelEmbedding1 ∘ raw6193step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6193step2 raw6193step2Labels raw6193step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3575 node3575Labels := by rfl

def raw6194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6194Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6194step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6194step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6194step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6194step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6194 raw6194Labels = mixedMoment B node3577 node3577Labels := by
  calc
    mixedMoment B raw6194 raw6194Labels = mixedMoment B raw6194step0 raw6194step0Labels := by
      have hz : ∀ j, raw6194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6194step0 = (fun i j => raw6194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6194step0 raw6194; decide +kernel
      have hl : raw6194step0Labels = raw6194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6194 raw6194Labels permutation346 hz
    mixedMoment B raw6194step0 raw6194step0Labels = mixedMoment B raw6194step1 raw6194step1Labels := by
      have ha : raw6194step1 = (fun i j => raw6194step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6194step1 raw6194step0; decide +kernel
      have hl : raw6194step1Labels = raw6194step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6194step0 raw6194step0Labels permutation36 permutation7
    mixedMoment B raw6194step1 raw6194step1Labels = mixedMoment B raw6194step2 raw6194step2Labels := by
      have ha : raw6194step2 = -raw6194step1 := by apply Matrix.ext; change ∀ i j, raw6194step2 i j = -(raw6194step1 i j); unfold raw6194step2 raw6194step1; decide +kernel
      have hl : raw6194step2Labels = raw6194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6194step2 raw6194step2Labels = mixedMoment B raw6194step3 raw6194step3Labels := by
      have ha : raw6194step3 = raw6194step2 := by apply Matrix.ext; unfold raw6194step3 raw6194step2; decide +kernel
      have hl : raw6194step2Labels = labelEmbedding1 ∘ raw6194step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6194step2 raw6194step2Labels raw6194step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3577 node3577Labels := by rfl

def raw6195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6195Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6195step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw6195step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6195step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6195step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6195 raw6195Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw6195 raw6195Labels = mixedMoment B raw6195step0 raw6195step0Labels := by
      have hz : ∀ j, raw6195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6195step0 = (fun i j => raw6195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6195step0 raw6195; decide +kernel
      have hl : raw6195step0Labels = raw6195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6195 raw6195Labels permutation346 hz
    mixedMoment B raw6195step0 raw6195step0Labels = mixedMoment B raw6195step1 raw6195step1Labels := by
      have ha : raw6195step1 = (fun i j => raw6195step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6195step1 raw6195step0; decide +kernel
      have hl : raw6195step1Labels = raw6195step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6195step0 raw6195step0Labels permutation36 permutation7
    mixedMoment B raw6195step1 raw6195step1Labels = mixedMoment B raw6195step2 raw6195step2Labels := by
      have ha : raw6195step2 = -raw6195step1 := by apply Matrix.ext; change ∀ i j, raw6195step2 i j = -(raw6195step1 i j); unfold raw6195step2 raw6195step1; decide +kernel
      have hl : raw6195step2Labels = raw6195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6195step2 raw6195step2Labels = mixedMoment B raw6195step3 raw6195step3Labels := by
      have ha : raw6195step3 = raw6195step2 := by apply Matrix.ext; unfold raw6195step3 raw6195step2; decide +kernel
      have hl : raw6195step2Labels = labelEmbedding1 ∘ raw6195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6195step2 raw6195step2Labels raw6195step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw6196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6196Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6196step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6196step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6196 raw6196Labels = mixedMoment B node3285 node3285Labels := by
  calc
    mixedMoment B raw6196 raw6196Labels = mixedMoment B raw6196step0 raw6196step0Labels := by
      have ha : raw6196step0 = (fun i j => raw6196 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6196step0 raw6196; decide +kernel
      have hl : raw6196step0Labels = raw6196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6196 raw6196Labels permutation212 permutation5
    mixedMoment B raw6196step0 raw6196step0Labels = mixedMoment B raw6196step1 raw6196step1Labels := by
      have ha : raw6196step1 = -raw6196step0 := by apply Matrix.ext; change ∀ i j, raw6196step1 i j = -(raw6196step0 i j); unfold raw6196step1 raw6196step0; decide +kernel
      have hl : raw6196step1Labels = raw6196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6196step1 raw6196step1Labels = mixedMoment B raw6196step2 raw6196step2Labels := by
      have ha : raw6196step2 = raw6196step1 := by apply Matrix.ext; unfold raw6196step2 raw6196step1; decide +kernel
      have hl : raw6196step1Labels = labelEmbedding1 ∘ raw6196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6196step1 raw6196step1Labels raw6196step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3285 node3285Labels := by rfl

def raw6197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6197Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6197step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6197step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6197step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6197step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6197 raw6197Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw6197 raw6197Labels = mixedMoment B raw6197step0 raw6197step0Labels := by
      have ha : raw6197step0 = (fun i j => raw6197 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6197step0 raw6197; decide +kernel
      have hl : raw6197step0Labels = raw6197Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6197 raw6197Labels permutation156 permutation7
    mixedMoment B raw6197step0 raw6197step0Labels = mixedMoment B raw6197step1 raw6197step1Labels := by
      have ha : raw6197step1 = -raw6197step0 := by apply Matrix.ext; change ∀ i j, raw6197step1 i j = -(raw6197step0 i j); unfold raw6197step1 raw6197step0; decide +kernel
      have hl : raw6197step1Labels = raw6197step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6197step1 raw6197step1Labels = mixedMoment B raw6197step2 raw6197step2Labels := by
      have ha : raw6197step2 = raw6197step1 := by apply Matrix.ext; unfold raw6197step2 raw6197step1; decide +kernel
      have hl : raw6197step1Labels = labelEmbedding1 ∘ raw6197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6197step1 raw6197step1Labels raw6197step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw6198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6198Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw6198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6198step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6198step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6198 raw6198Labels = mixedMoment B node3527 node3527Labels := by
  calc
    mixedMoment B raw6198 raw6198Labels = mixedMoment B raw6198step0 raw6198step0Labels := by
      have ha : raw6198step0 = (fun i j => raw6198 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6198step0 raw6198; decide +kernel
      have hl : raw6198step0Labels = raw6198Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6198 raw6198Labels permutation156 permutation7
    mixedMoment B raw6198step0 raw6198step0Labels = mixedMoment B raw6198step1 raw6198step1Labels := by
      have ha : raw6198step1 = -raw6198step0 := by apply Matrix.ext; change ∀ i j, raw6198step1 i j = -(raw6198step0 i j); unfold raw6198step1 raw6198step0; decide +kernel
      have hl : raw6198step1Labels = raw6198step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6198step1 raw6198step1Labels = mixedMoment B raw6198step2 raw6198step2Labels := by
      have ha : raw6198step2 = raw6198step1 := by apply Matrix.ext; unfold raw6198step2 raw6198step1; decide +kernel
      have hl : raw6198step1Labels = labelEmbedding1 ∘ raw6198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6198step1 raw6198step1Labels raw6198step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3527 node3527Labels := by rfl

def raw6199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6199Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6199step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6199step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6199step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6199step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6199 raw6199Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw6199 raw6199Labels = mixedMoment B raw6199step0 raw6199step0Labels := by
      have ha : raw6199step0 = (fun i j => raw6199 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6199step0 raw6199; decide +kernel
      have hl : raw6199step0Labels = raw6199Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6199 raw6199Labels permutation156 permutation7
    mixedMoment B raw6199step0 raw6199step0Labels = mixedMoment B raw6199step1 raw6199step1Labels := by
      have ha : raw6199step1 = -raw6199step0 := by apply Matrix.ext; change ∀ i j, raw6199step1 i j = -(raw6199step0 i j); unfold raw6199step1 raw6199step0; decide +kernel
      have hl : raw6199step1Labels = raw6199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6199step1 raw6199step1Labels = mixedMoment B raw6199step2 raw6199step2Labels := by
      have ha : raw6199step2 = raw6199step1 := by apply Matrix.ext; unfold raw6199step2 raw6199step1; decide +kernel
      have hl : raw6199step1Labels = labelEmbedding1 ∘ raw6199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6199step1 raw6199step1Labels raw6199step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3528 node3528Labels := by rfl

def raw6200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6200Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw6200step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6200step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6200step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6200step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6200 raw6200Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw6200 raw6200Labels = mixedMoment B raw6200step0 raw6200step0Labels := by
      have ha : raw6200step0 = (fun i j => raw6200 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6200step0 raw6200; decide +kernel
      have hl : raw6200step0Labels = raw6200Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6200 raw6200Labels permutation156 permutation7
    mixedMoment B raw6200step0 raw6200step0Labels = mixedMoment B raw6200step1 raw6200step1Labels := by
      have ha : raw6200step1 = -raw6200step0 := by apply Matrix.ext; change ∀ i j, raw6200step1 i j = -(raw6200step0 i j); unfold raw6200step1 raw6200step0; decide +kernel
      have hl : raw6200step1Labels = raw6200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6200step1 raw6200step1Labels = mixedMoment B raw6200step2 raw6200step2Labels := by
      have ha : raw6200step2 = raw6200step1 := by apply Matrix.ext; unfold raw6200step2 raw6200step1; decide +kernel
      have hl : raw6200step1Labels = labelEmbedding1 ∘ raw6200step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6200step1 raw6200step1Labels raw6200step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw6201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6201Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6201step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6201step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6201step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6201step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6201step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6201 raw6201Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw6201 raw6201Labels = mixedMoment B raw6201step0 raw6201step0Labels := by
      have hz : ∀ j, raw6201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6201step0 = (fun i j => raw6201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6201step0 raw6201; decide +kernel
      have hl : raw6201step0Labels = raw6201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6201 raw6201Labels permutation346 hz
    mixedMoment B raw6201step0 raw6201step0Labels = mixedMoment B raw6201step1 raw6201step1Labels := by
      have ha : raw6201step1 = (fun i j => raw6201step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6201step1 raw6201step0; decide +kernel
      have hl : raw6201step1Labels = raw6201step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6201step0 raw6201step0Labels permutation36 permutation7
    mixedMoment B raw6201step1 raw6201step1Labels = mixedMoment B raw6201step2 raw6201step2Labels := by
      have ha : raw6201step2 = -raw6201step1 := by apply Matrix.ext; change ∀ i j, raw6201step2 i j = -(raw6201step1 i j); unfold raw6201step2 raw6201step1; decide +kernel
      have hl : raw6201step2Labels = raw6201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6201step2 raw6201step2Labels = mixedMoment B raw6201step3 raw6201step3Labels := by
      have ha : raw6201step3 = raw6201step2 := by apply Matrix.ext; unfold raw6201step3 raw6201step2; decide +kernel
      have hl : raw6201step2Labels = labelEmbedding1 ∘ raw6201step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6201step2 raw6201step2Labels raw6201step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw6202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6202Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6202step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6202step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6202 raw6202Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw6202 raw6202Labels = mixedMoment B raw6202step0 raw6202step0Labels := by
      have hz : ∀ j, raw6202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6202step0 = (fun i j => raw6202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6202step0 raw6202; decide +kernel
      have hl : raw6202step0Labels = raw6202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6202 raw6202Labels permutation346 hz
    mixedMoment B raw6202step0 raw6202step0Labels = mixedMoment B raw6202step1 raw6202step1Labels := by
      have ha : raw6202step1 = (fun i j => raw6202step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6202step1 raw6202step0; decide +kernel
      have hl : raw6202step1Labels = raw6202step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6202step0 raw6202step0Labels permutation36 permutation7
    mixedMoment B raw6202step1 raw6202step1Labels = mixedMoment B raw6202step2 raw6202step2Labels := by
      have ha : raw6202step2 = -raw6202step1 := by apply Matrix.ext; change ∀ i j, raw6202step2 i j = -(raw6202step1 i j); unfold raw6202step2 raw6202step1; decide +kernel
      have hl : raw6202step2Labels = raw6202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6202step2 raw6202step2Labels = mixedMoment B raw6202step3 raw6202step3Labels := by
      have ha : raw6202step3 = raw6202step2 := by apply Matrix.ext; unfold raw6202step3 raw6202step2; decide +kernel
      have hl : raw6202step2Labels = labelEmbedding1 ∘ raw6202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6202step2 raw6202step2Labels raw6202step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

def raw6203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6203step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6203step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6203step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6203step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6203 raw6203Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw6203 raw6203Labels = mixedMoment B raw6203step0 raw6203step0Labels := by
      have ha : raw6203step0 = (fun i j => raw6203 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6203step0 raw6203; decide +kernel
      have hl : raw6203step0Labels = raw6203Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6203 raw6203Labels permutation156 permutation7
    mixedMoment B raw6203step0 raw6203step0Labels = mixedMoment B raw6203step1 raw6203step1Labels := by
      have ha : raw6203step1 = -raw6203step0 := by apply Matrix.ext; change ∀ i j, raw6203step1 i j = -(raw6203step0 i j); unfold raw6203step1 raw6203step0; decide +kernel
      have hl : raw6203step1Labels = raw6203step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6203step1 raw6203step1Labels = mixedMoment B raw6203step2 raw6203step2Labels := by
      have ha : raw6203step2 = raw6203step1 := by apply Matrix.ext; unfold raw6203step2 raw6203step1; decide +kernel
      have hl : raw6203step1Labels = labelEmbedding1 ∘ raw6203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6203step1 raw6203step1Labels raw6203step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw6204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6204step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6204step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6204step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6204 raw6204Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw6204 raw6204Labels = mixedMoment B raw6204step0 raw6204step0Labels := by
      have hz : ∀ j, raw6204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6204step0 = (fun i j => raw6204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6204step0 raw6204; decide +kernel
      have hl : raw6204step0Labels = raw6204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6204 raw6204Labels permutation346 hz
    mixedMoment B raw6204step0 raw6204step0Labels = mixedMoment B raw6204step1 raw6204step1Labels := by
      have ha : raw6204step1 = (fun i j => raw6204step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6204step1 raw6204step0; decide +kernel
      have hl : raw6204step1Labels = raw6204step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6204step0 raw6204step0Labels permutation36 permutation7
    mixedMoment B raw6204step1 raw6204step1Labels = mixedMoment B raw6204step2 raw6204step2Labels := by
      have ha : raw6204step2 = -raw6204step1 := by apply Matrix.ext; change ∀ i j, raw6204step2 i j = -(raw6204step1 i j); unfold raw6204step2 raw6204step1; decide +kernel
      have hl : raw6204step2Labels = raw6204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6204step2 raw6204step2Labels = mixedMoment B raw6204step3 raw6204step3Labels := by
      have ha : raw6204step3 = raw6204step2 := by apply Matrix.ext; unfold raw6204step3 raw6204step2; decide +kernel
      have hl : raw6204step2Labels = labelEmbedding1 ∘ raw6204step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6204step2 raw6204step2Labels raw6204step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw6205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6205step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6205step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6205step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6205 raw6205Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw6205 raw6205Labels = mixedMoment B raw6205step0 raw6205step0Labels := by
      have hz : ∀ j, raw6205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6205step0 = (fun i j => raw6205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6205step0 raw6205; decide +kernel
      have hl : raw6205step0Labels = raw6205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6205 raw6205Labels permutation346 hz
    mixedMoment B raw6205step0 raw6205step0Labels = mixedMoment B raw6205step1 raw6205step1Labels := by
      have ha : raw6205step1 = (fun i j => raw6205step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6205step1 raw6205step0; decide +kernel
      have hl : raw6205step1Labels = raw6205step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6205step0 raw6205step0Labels permutation36 permutation7
    mixedMoment B raw6205step1 raw6205step1Labels = mixedMoment B raw6205step2 raw6205step2Labels := by
      have ha : raw6205step2 = -raw6205step1 := by apply Matrix.ext; change ∀ i j, raw6205step2 i j = -(raw6205step1 i j); unfold raw6205step2 raw6205step1; decide +kernel
      have hl : raw6205step2Labels = raw6205step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6205step2 raw6205step2Labels = mixedMoment B raw6205step3 raw6205step3Labels := by
      have ha : raw6205step3 = raw6205step2 := by apply Matrix.ext; unfold raw6205step3 raw6205step2; decide +kernel
      have hl : raw6205step2Labels = labelEmbedding1 ∘ raw6205step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6205step2 raw6205step2Labels raw6205step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw6206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw6206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6206 raw6206Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw6206 raw6206Labels = mixedMoment B raw6206step0 raw6206step0Labels := by
      have hz : ∀ j, raw6206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6206step0 = (fun i j => raw6206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6206step0 raw6206; decide +kernel
      have hl : raw6206step0Labels = raw6206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6206 raw6206Labels permutation346 hz
    mixedMoment B raw6206step0 raw6206step0Labels = mixedMoment B raw6206step1 raw6206step1Labels := by
      have ha : raw6206step1 = (fun i j => raw6206step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6206step1 raw6206step0; decide +kernel
      have hl : raw6206step1Labels = raw6206step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6206step0 raw6206step0Labels permutation40 permutation5
    mixedMoment B raw6206step1 raw6206step1Labels = mixedMoment B raw6206step2 raw6206step2Labels := by
      have ha : raw6206step2 = -raw6206step1 := by apply Matrix.ext; change ∀ i j, raw6206step2 i j = -(raw6206step1 i j); unfold raw6206step2 raw6206step1; decide +kernel
      have hl : raw6206step2Labels = raw6206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6206step2 raw6206step2Labels = mixedMoment B raw6206step3 raw6206step3Labels := by
      have ha : raw6206step3 = raw6206step2 := by apply Matrix.ext; unfold raw6206step3 raw6206step2; decide +kernel
      have hl : raw6206step2Labels = labelEmbedding1 ∘ raw6206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6206step2 raw6206step2Labels raw6206step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

def raw6207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6207step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw6207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6207step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6207step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6207step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6207 raw6207Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw6207 raw6207Labels = mixedMoment B raw6207step0 raw6207step0Labels := by
      have hz : ∀ j, raw6207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6207step0 = (fun i j => raw6207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6207step0 raw6207; decide +kernel
      have hl : raw6207step0Labels = raw6207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6207 raw6207Labels permutation346 hz
    mixedMoment B raw6207step0 raw6207step0Labels = mixedMoment B raw6207step1 raw6207step1Labels := by
      have ha : raw6207step1 = (fun i j => raw6207step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6207step1 raw6207step0; decide +kernel
      have hl : raw6207step1Labels = raw6207step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6207step0 raw6207step0Labels permutation36 permutation7
    mixedMoment B raw6207step1 raw6207step1Labels = mixedMoment B raw6207step2 raw6207step2Labels := by
      have ha : raw6207step2 = -raw6207step1 := by apply Matrix.ext; change ∀ i j, raw6207step2 i j = -(raw6207step1 i j); unfold raw6207step2 raw6207step1; decide +kernel
      have hl : raw6207step2Labels = raw6207step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6207step2 raw6207step2Labels = mixedMoment B raw6207step3 raw6207step3Labels := by
      have ha : raw6207step3 = raw6207step2 := by apply Matrix.ext; unfold raw6207step3 raw6207step2; decide +kernel
      have hl : raw6207step2Labels = labelEmbedding1 ∘ raw6207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6207step2 raw6207step2Labels raw6207step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw6208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw6208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6208step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw6208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6208 raw6208Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw6208 raw6208Labels = mixedMoment B raw6208step0 raw6208step0Labels := by
      have ha : raw6208step0 = (fun i j => raw6208 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6208step0 raw6208; decide +kernel
      have hl : raw6208step0Labels = raw6208Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6208 raw6208Labels permutation156 permutation7
    mixedMoment B raw6208step0 raw6208step0Labels = mixedMoment B raw6208step1 raw6208step1Labels := by
      have ha : raw6208step1 = -raw6208step0 := by apply Matrix.ext; change ∀ i j, raw6208step1 i j = -(raw6208step0 i j); unfold raw6208step1 raw6208step0; decide +kernel
      have hl : raw6208step1Labels = raw6208step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6208step1 raw6208step1Labels = mixedMoment B raw6208step2 raw6208step2Labels := by
      have ha : raw6208step2 = raw6208step1 := by apply Matrix.ext; unfold raw6208step2 raw6208step1; decide +kernel
      have hl : raw6208step1Labels = labelEmbedding1 ∘ raw6208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6208step1 raw6208step1Labels raw6208step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw6209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6209step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw6209step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6209step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6209step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6209step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6209 raw6209Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw6209 raw6209Labels = mixedMoment B raw6209step0 raw6209step0Labels := by
      have hz : ∀ j, raw6209 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6209step0 = (fun i j => raw6209 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6209step0 raw6209; decide +kernel
      have hl : raw6209step0Labels = raw6209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6209 raw6209Labels permutation346 hz
    mixedMoment B raw6209step0 raw6209step0Labels = mixedMoment B raw6209step1 raw6209step1Labels := by
      have ha : raw6209step1 = (fun i j => raw6209step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6209step1 raw6209step0; decide +kernel
      have hl : raw6209step1Labels = raw6209step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6209step0 raw6209step0Labels permutation36 permutation7
    mixedMoment B raw6209step1 raw6209step1Labels = mixedMoment B raw6209step2 raw6209step2Labels := by
      have ha : raw6209step2 = -raw6209step1 := by apply Matrix.ext; change ∀ i j, raw6209step2 i j = -(raw6209step1 i j); unfold raw6209step2 raw6209step1; decide +kernel
      have hl : raw6209step2Labels = raw6209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6209step2 raw6209step2Labels = mixedMoment B raw6209step3 raw6209step3Labels := by
      have ha : raw6209step3 = raw6209step2 := by apply Matrix.ext; unfold raw6209step3 raw6209step2; decide +kernel
      have hl : raw6209step2Labels = labelEmbedding1 ∘ raw6209step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6209step2 raw6209step2Labels raw6209step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw6210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6210step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6210step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6210step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6210step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6210 raw6210Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw6210 raw6210Labels = mixedMoment B raw6210step0 raw6210step0Labels := by
      have hz : ∀ j, raw6210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6210step0 = (fun i j => raw6210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6210step0 raw6210; decide +kernel
      have hl : raw6210step0Labels = raw6210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6210 raw6210Labels permutation346 hz
    mixedMoment B raw6210step0 raw6210step0Labels = mixedMoment B raw6210step1 raw6210step1Labels := by
      have ha : raw6210step1 = (fun i j => raw6210step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6210step1 raw6210step0; decide +kernel
      have hl : raw6210step1Labels = raw6210step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6210step0 raw6210step0Labels permutation36 permutation7
    mixedMoment B raw6210step1 raw6210step1Labels = mixedMoment B raw6210step2 raw6210step2Labels := by
      have ha : raw6210step2 = -raw6210step1 := by apply Matrix.ext; change ∀ i j, raw6210step2 i j = -(raw6210step1 i j); unfold raw6210step2 raw6210step1; decide +kernel
      have hl : raw6210step2Labels = raw6210step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6210step2 raw6210step2Labels = mixedMoment B raw6210step3 raw6210step3Labels := by
      have ha : raw6210step3 = raw6210step2 := by apply Matrix.ext; unfold raw6210step3 raw6210step2; decide +kernel
      have hl : raw6210step2Labels = labelEmbedding1 ∘ raw6210step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6210step2 raw6210step2Labels raw6210step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw6211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6211step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw6211step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw6211step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6211 raw6211Labels = mixedMoment B node2045 node2045Labels := by
  calc
    mixedMoment B raw6211 raw6211Labels = mixedMoment B raw6211step0 raw6211step0Labels := by
      have hz : ∀ j, raw6211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6211step0 = (fun i j => raw6211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6211step0 raw6211; decide +kernel
      have hl : raw6211step0Labels = raw6211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6211 raw6211Labels permutation346 hz
    mixedMoment B raw6211step0 raw6211step0Labels = mixedMoment B raw6211step1 raw6211step1Labels := by
      have ha : raw6211step1 = (fun i j => raw6211step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6211step1 raw6211step0; decide +kernel
      have hl : raw6211step1Labels = raw6211step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6211step0 raw6211step0Labels permutation139 permutation5
    mixedMoment B raw6211step1 raw6211step1Labels = mixedMoment B raw6211step2 raw6211step2Labels := by
      have ha : raw6211step2 = raw6211step1 := by apply Matrix.ext; unfold raw6211step2 raw6211step1; decide +kernel
      have hl : raw6211step1Labels = labelEmbedding1 ∘ raw6211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6211step1 raw6211step1Labels raw6211step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2045 node2045Labels := by rfl

def raw6212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6212step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw6212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw6212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6212 raw6212Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw6212 raw6212Labels = mixedMoment B raw6212step0 raw6212step0Labels := by
      have hz : ∀ j, raw6212 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6212step0 = (fun i j => raw6212 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6212step0 raw6212; decide +kernel
      have hl : raw6212step0Labels = raw6212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6212 raw6212Labels permutation346 hz
    mixedMoment B raw6212step0 raw6212step0Labels = mixedMoment B raw6212step1 raw6212step1Labels := by
      have ha : raw6212step1 = (fun i j => raw6212step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6212step1 raw6212step0; decide +kernel
      have hl : raw6212step1Labels = raw6212step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6212step0 raw6212step0Labels permutation139 permutation5
    mixedMoment B raw6212step1 raw6212step1Labels = mixedMoment B raw6212step2 raw6212step2Labels := by
      have ha : raw6212step2 = raw6212step1 := by apply Matrix.ext; unfold raw6212step2 raw6212step1; decide +kernel
      have hl : raw6212step1Labels = labelEmbedding1 ∘ raw6212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6212step1 raw6212step1Labels raw6212step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw6213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw6213step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw6213step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6213 raw6213Labels = mixedMoment B node2043 node2043Labels := by
  calc
    mixedMoment B raw6213 raw6213Labels = mixedMoment B raw6213step0 raw6213step0Labels := by
      have ha : raw6213step0 = (fun i j => raw6213 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6213step0 raw6213; decide +kernel
      have hl : raw6213step0Labels = raw6213Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6213 raw6213Labels permutation622 permutation5
    mixedMoment B raw6213step0 raw6213step0Labels = mixedMoment B raw6213step1 raw6213step1Labels := by
      have ha : raw6213step1 = raw6213step0 := by apply Matrix.ext; unfold raw6213step1 raw6213step0; decide +kernel
      have hl : raw6213step0Labels = labelEmbedding1 ∘ raw6213step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6213step0 raw6213step0Labels raw6213step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2043 node2043Labels := by rfl

def raw6214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6214step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6214 raw6214Labels = mixedMoment B node2049 node2049Labels := by
  calc
    mixedMoment B raw6214 raw6214Labels = mixedMoment B raw6214step0 raw6214step0Labels := by
      have hz : ∀ j, raw6214 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6214step0 = (fun i j => raw6214 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6214step0 raw6214; decide +kernel
      have hl : raw6214step0Labels = raw6214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6214 raw6214Labels permutation346 hz
    mixedMoment B raw6214step0 raw6214step0Labels = mixedMoment B raw6214step1 raw6214step1Labels := by
      have ha : raw6214step1 = (fun i j => raw6214step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6214step1 raw6214step0; decide +kernel
      have hl : raw6214step1Labels = raw6214step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6214step0 raw6214step0Labels permutation138 permutation5
    mixedMoment B raw6214step1 raw6214step1Labels = mixedMoment B raw6214step2 raw6214step2Labels := by
      have ha : raw6214step2 = raw6214step1 := by apply Matrix.ext; unfold raw6214step2 raw6214step1; decide +kernel
      have hl : raw6214step1Labels = labelEmbedding1 ∘ raw6214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6214step1 raw6214step1Labels raw6214step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2049 node2049Labels := by rfl

def raw6215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6215 raw6215Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw6215 raw6215Labels = mixedMoment B raw6215step0 raw6215step0Labels := by
      have hz : ∀ j, raw6215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6215step0 = (fun i j => raw6215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6215step0 raw6215; decide +kernel
      have hl : raw6215step0Labels = raw6215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6215 raw6215Labels permutation346 hz
    mixedMoment B raw6215step0 raw6215step0Labels = mixedMoment B raw6215step1 raw6215step1Labels := by
      have ha : raw6215step1 = (fun i j => raw6215step0 (permutation136 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6215step1 raw6215step0; decide +kernel
      have hl : raw6215step1Labels = raw6215step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6215step0 raw6215step0Labels permutation136 permutation5
    mixedMoment B raw6215step1 raw6215step1Labels = mixedMoment B raw6215step2 raw6215step2Labels := by
      have ha : raw6215step2 = raw6215step1 := by apply Matrix.ext; unfold raw6215step2 raw6215step1; decide +kernel
      have hl : raw6215step1Labels = labelEmbedding1 ∘ raw6215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6215step1 raw6215step1Labels raw6215step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2055 node2055Labels := by rfl

def raw6216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6216Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6216step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6216 raw6216Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw6216 raw6216Labels = mixedMoment B raw6216step0 raw6216step0Labels := by
      have hz : ∀ j, raw6216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6216step0 = (fun i j => raw6216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6216step0 raw6216; decide +kernel
      have hl : raw6216step0Labels = raw6216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6216 raw6216Labels permutation346 hz
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw6217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6217Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6217step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6217 raw6217Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw6217 raw6217Labels = mixedMoment B raw6217step0 raw6217step0Labels := by
      have hz : ∀ j, raw6217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6217step0 = (fun i j => raw6217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6217step0 raw6217; decide +kernel
      have hl : raw6217step0Labels = raw6217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6217 raw6217Labels permutation346 hz
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw6218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6218Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6218step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6218 raw6218Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw6218 raw6218Labels = mixedMoment B raw6218step0 raw6218step0Labels := by
      have ha : raw6218step0 = (fun i j => raw6218 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6218step0 raw6218; decide +kernel
      have hl : raw6218step0Labels = raw6218Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6218 raw6218Labels permutation176 permutation2
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw6219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6219Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6219step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6219step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6219 raw6219Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw6219 raw6219Labels = mixedMoment B raw6219step0 raw6219step0Labels := by
      have hz : ∀ j, raw6219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6219step0 = (fun i j => raw6219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6219step0 raw6219; decide +kernel
      have hl : raw6219step0Labels = raw6219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6219 raw6219Labels permutation346 hz
    mixedMoment B raw6219step0 raw6219step0Labels = mixedMoment B raw6219step1 raw6219step1Labels := by
      have ha : raw6219step1 = (fun i j => raw6219step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6219step1 raw6219step0; decide +kernel
      have hl : raw6219step1Labels = raw6219step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6219step0 raw6219step0Labels permutation38 permutation2
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw6220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6220Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6220step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6220step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6220 raw6220Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw6220 raw6220Labels = mixedMoment B raw6220step0 raw6220step0Labels := by
      have hz : ∀ j, raw6220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6220step0 = (fun i j => raw6220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6220step0 raw6220; decide +kernel
      have hl : raw6220step0Labels = raw6220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6220 raw6220Labels permutation346 hz
    mixedMoment B raw6220step0 raw6220step0Labels = mixedMoment B raw6220step1 raw6220step1Labels := by
      have ha : raw6220step1 = (fun i j => raw6220step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6220step1 raw6220step0; decide +kernel
      have hl : raw6220step1Labels = raw6220step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6220step0 raw6220step0Labels permutation116 permutation4
    mixedMoment B raw6220step1 raw6220step1Labels = mixedMoment B raw6220step2 raw6220step2Labels := by
      have ha : raw6220step2 = -raw6220step1 := by apply Matrix.ext; change ∀ i j, raw6220step2 i j = -(raw6220step1 i j); unfold raw6220step2 raw6220step1; decide +kernel
      have hl : raw6220step2Labels = raw6220step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw6221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6221Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6221step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw6221step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6221 raw6221Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw6221 raw6221Labels = mixedMoment B raw6221step0 raw6221step0Labels := by
      have hz : ∀ j, raw6221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6221step0 = (fun i j => raw6221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6221step0 raw6221; decide +kernel
      have hl : raw6221step0Labels = raw6221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6221 raw6221Labels permutation346 hz
    mixedMoment B raw6221step0 raw6221step0Labels = mixedMoment B raw6221step1 raw6221step1Labels := by
      have ha : raw6221step1 = (fun i j => raw6221step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6221step1 raw6221step0; decide +kernel
      have hl : raw6221step1Labels = raw6221step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6221step0 raw6221step0Labels permutation33 permutation2
    _ = mixedMoment B node3903 node3903Labels := by rfl

def raw6222 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]
def raw6222Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6222step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]
def raw6222step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6222step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw6222step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical6222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6222 raw6222Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw6222 raw6222Labels = mixedMoment B raw6222step0 raw6222step0Labels := by
      have hz : ∀ j, raw6222 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw6222step0 = (fun i j => raw6222 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw6222step0 raw6222; decide +kernel
      have hl : raw6222step0Labels = raw6222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6222 raw6222Labels permutation590 hz
    mixedMoment B raw6222step0 raw6222step0Labels = mixedMoment B raw6222step1 raw6222step1Labels := by
      have hz : ∀ j, raw6222step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6222step1 = (fun i j => raw6222step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6222step1 raw6222step0; decide +kernel
      have hl : raw6222step1Labels = raw6222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6222step0 raw6222step0Labels permutation80 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw6223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6223Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6223step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6223step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6223 raw6223Labels = mixedMoment B node1263 node1263Labels := by
  calc
    mixedMoment B raw6223 raw6223Labels = mixedMoment B raw6223step0 raw6223step0Labels := by
      have hz : ∀ j, raw6223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6223step0 = (fun i j => raw6223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6223step0 raw6223; decide +kernel
      have hl : raw6223step0Labels = raw6223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6223 raw6223Labels permutation346 hz
    mixedMoment B raw6223step0 raw6223step0Labels = mixedMoment B raw6223step1 raw6223step1Labels := by
      have ha : raw6223step1 = (fun i j => raw6223step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6223step1 raw6223step0; decide +kernel
      have hl : raw6223step1Labels = raw6223step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6223step0 raw6223step0Labels permutation38 permutation2
    _ = mixedMoment B node1263 node1263Labels := by rfl

def raw6224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6224 raw6224Labels = mixedMoment B node1214 node1214Labels := by
  calc
    mixedMoment B raw6224 raw6224Labels = mixedMoment B raw6224step0 raw6224step0Labels := by
      have ha : raw6224step0 = (fun i j => raw6224 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6224step0 raw6224; decide +kernel
      have hl : raw6224step0Labels = raw6224Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6224 raw6224Labels permutation158 permutation2
    _ = mixedMoment B node1214 node1214Labels := by rfl

def raw6225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6225 raw6225Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw6225 raw6225Labels = mixedMoment B raw6225step0 raw6225step0Labels := by
      have hz : ∀ j, raw6225 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6225step0 = (fun i j => raw6225 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6225step0 raw6225; decide +kernel
      have hl : raw6225step0Labels = raw6225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6225 raw6225Labels permutation346 hz
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw6226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6226step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6226 raw6226Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw6226 raw6226Labels = mixedMoment B raw6226step0 raw6226step0Labels := by
      have hz : ∀ j, raw6226 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6226step0 = (fun i j => raw6226 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6226step0 raw6226; decide +kernel
      have hl : raw6226step0Labels = raw6226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6226 raw6226Labels permutation346 hz
    mixedMoment B raw6226step0 raw6226step0Labels = mixedMoment B raw6226step1 raw6226step1Labels := by
      have ha : raw6226step1 = (fun i j => raw6226step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6226step1 raw6226step0; decide +kernel
      have hl : raw6226step1Labels = raw6226step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6226step0 raw6226step0Labels permutation33 permutation2
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw6227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6227 raw6227Labels = mixedMoment B node1218 node1218Labels := by
  calc
    mixedMoment B raw6227 raw6227Labels = mixedMoment B raw6227step0 raw6227step0Labels := by
      have hz : ∀ j, raw6227 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6227step0 = (fun i j => raw6227 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6227step0 raw6227; decide +kernel
      have hl : raw6227step0Labels = raw6227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6227 raw6227Labels permutation346 hz
    _ = mixedMoment B node1218 node1218Labels := by rfl

def raw6228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6228 raw6228Labels = mixedMoment B node2568 node2568Labels := by
  calc
    mixedMoment B raw6228 raw6228Labels = mixedMoment B raw6228step0 raw6228step0Labels := by
      have ha : raw6228step0 = (fun i j => raw6228 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6228step0 raw6228; decide +kernel
      have hl : raw6228step0Labels = raw6228Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6228 raw6228Labels permutation182 permutation2
    _ = mixedMoment B node2568 node2568Labels := by rfl

def raw6229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6229step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6229 raw6229Labels = mixedMoment B node2634 node2634Labels := by
  calc
    mixedMoment B raw6229 raw6229Labels = mixedMoment B raw6229step0 raw6229step0Labels := by
      have hz : ∀ j, raw6229 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6229step0 = (fun i j => raw6229 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6229step0 raw6229; decide +kernel
      have hl : raw6229step0Labels = raw6229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6229 raw6229Labels permutation346 hz
    mixedMoment B raw6229step0 raw6229step0Labels = mixedMoment B raw6229step1 raw6229step1Labels := by
      have ha : raw6229step1 = (fun i j => raw6229step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6229step1 raw6229step0; decide +kernel
      have hl : raw6229step1Labels = raw6229step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6229step0 raw6229step0Labels permutation38 permutation2
    _ = mixedMoment B node2634 node2634Labels := by rfl

def raw6230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw6230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6230 raw6230Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw6230 raw6230Labels = mixedMoment B raw6230step0 raw6230step0Labels := by
      have hz : ∀ j, raw6230 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6230step0 = (fun i j => raw6230 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6230step0 raw6230; decide +kernel
      have hl : raw6230step0Labels = raw6230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6230 raw6230Labels permutation346 hz
    mixedMoment B raw6230step0 raw6230step0Labels = mixedMoment B raw6230step1 raw6230step1Labels := by
      have ha : raw6230step1 = (fun i j => raw6230step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6230step1 raw6230step0; decide +kernel
      have hl : raw6230step1Labels = raw6230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6230step0 raw6230step0Labels permutation40 permutation2
    _ = mixedMoment B node2758 node2758Labels := by rfl

def raw6231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6231step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6231 raw6231Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw6231 raw6231Labels = mixedMoment B raw6231step0 raw6231step0Labels := by
      have hz : ∀ j, raw6231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6231step0 = (fun i j => raw6231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6231step0 raw6231; decide +kernel
      have hl : raw6231step0Labels = raw6231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6231 raw6231Labels permutation346 hz
    mixedMoment B raw6231step0 raw6231step0Labels = mixedMoment B raw6231step1 raw6231step1Labels := by
      have ha : raw6231step1 = (fun i j => raw6231step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6231step1 raw6231step0; decide +kernel
      have hl : raw6231step1Labels = raw6231step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6231step0 raw6231step0Labels permutation39 permutation2
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw6232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6232step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6232 raw6232Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw6232 raw6232Labels = mixedMoment B raw6232step0 raw6232step0Labels := by
      have ha : raw6232step0 = (fun i j => raw6232 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6232step0 raw6232; decide +kernel
      have hl : raw6232step0Labels = raw6232Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6232 raw6232Labels permutation158 permutation2
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw6233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6233 raw6233Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw6233 raw6233Labels = mixedMoment B raw6233step0 raw6233step0Labels := by
      have hz : ∀ j, raw6233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6233step0 = (fun i j => raw6233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6233step0 raw6233; decide +kernel
      have hl : raw6233step0Labels = raw6233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6233 raw6233Labels permutation346 hz
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw6234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6234 raw6234Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw6234 raw6234Labels = mixedMoment B raw6234step0 raw6234step0Labels := by
      have hz : ∀ j, raw6234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6234step0 = (fun i j => raw6234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6234step0 raw6234; decide +kernel
      have hl : raw6234step0Labels = raw6234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6234 raw6234Labels permutation346 hz
    mixedMoment B raw6234step0 raw6234step0Labels = mixedMoment B raw6234step1 raw6234step1Labels := by
      have ha : raw6234step1 = (fun i j => raw6234step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6234step1 raw6234step0; decide +kernel
      have hl : raw6234step1Labels = raw6234step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6234step0 raw6234step0Labels permutation33 permutation2
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw6235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6235 raw6235Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw6235 raw6235Labels = mixedMoment B raw6235step0 raw6235step0Labels := by
      have hz : ∀ j, raw6235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6235step0 = (fun i j => raw6235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6235step0 raw6235; decide +kernel
      have hl : raw6235step0Labels = raw6235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6235 raw6235Labels permutation346 hz
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw6236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6236Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6236step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6236 raw6236Labels = mixedMoment B node2616 node2616Labels := by
  calc
    mixedMoment B raw6236 raw6236Labels = mixedMoment B raw6236step0 raw6236step0Labels := by
      have ha : raw6236step0 = (fun i j => raw6236 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6236step0 raw6236; decide +kernel
      have hl : raw6236step0Labels = raw6236Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6236 raw6236Labels permutation200 permutation2
    _ = mixedMoment B node2616 node2616Labels := by rfl

def raw6237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6237step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6237 raw6237Labels = mixedMoment B node2714 node2714Labels := by
  calc
    mixedMoment B raw6237 raw6237Labels = mixedMoment B raw6237step0 raw6237step0Labels := by
      have ha : raw6237step0 = (fun i j => raw6237 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6237step0 raw6237; decide +kernel
      have hl : raw6237step0Labels = raw6237Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6237 raw6237Labels permutation160 permutation2
    _ = mixedMoment B node2714 node2714Labels := by rfl

def raw6238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6238step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6238 raw6238Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw6238 raw6238Labels = mixedMoment B raw6238step0 raw6238step0Labels := by
      have ha : raw6238step0 = (fun i j => raw6238 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6238step0 raw6238; decide +kernel
      have hl : raw6238step0Labels = raw6238Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6238 raw6238Labels permutation159 permutation2
    _ = mixedMoment B node2720 node2720Labels := by rfl

def raw6239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6239 raw6239Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw6239 raw6239Labels = mixedMoment B raw6239step0 raw6239step0Labels := by
      have ha : raw6239step0 = (fun i j => raw6239 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6239step0 raw6239; decide +kernel
      have hl : raw6239step0Labels = raw6239Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6239 raw6239Labels permutation176 permutation2
    _ = mixedMoment B node2557 node2557Labels := by rfl

def raw6240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6240 raw6240Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw6240 raw6240Labels = mixedMoment B raw6240step0 raw6240step0Labels := by
      have ha : raw6240step0 = (fun i j => raw6240 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6240step0 raw6240; decide +kernel
      have hl : raw6240step0Labels = raw6240Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6240 raw6240Labels permutation177 permutation2
    _ = mixedMoment B node2545 node2545Labels := by rfl

def raw6241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6241Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6241 raw6241Labels = mixedMoment B node2544 node2544Labels := by
  calc
    mixedMoment B raw6241 raw6241Labels = mixedMoment B raw6241step0 raw6241step0Labels := by
      have ha : raw6241step0 = (fun i j => raw6241 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6241step0 raw6241; decide +kernel
      have hl : raw6241step0Labels = raw6241Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6241 raw6241Labels permutation176 permutation2
    _ = mixedMoment B node2544 node2544Labels := by rfl

def raw6242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6242step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6242 raw6242Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw6242 raw6242Labels = mixedMoment B raw6242step0 raw6242step0Labels := by
      have hz : ∀ j, raw6242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6242step0 = (fun i j => raw6242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6242step0 raw6242; decide +kernel
      have hl : raw6242step0Labels = raw6242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6242 raw6242Labels permutation346 hz
    mixedMoment B raw6242step0 raw6242step0Labels = mixedMoment B raw6242step1 raw6242step1Labels := by
      have ha : raw6242step1 = (fun i j => raw6242step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6242step1 raw6242step0; decide +kernel
      have hl : raw6242step1Labels = raw6242step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6242step0 raw6242step0Labels permutation34 permutation2
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw6243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6243Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, -1, 0]]
def raw6243step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6243step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6243 raw6243Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw6243 raw6243Labels = mixedMoment B raw6243step0 raw6243step0Labels := by
      have hz : ∀ j, raw6243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6243step0 = (fun i j => raw6243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6243step0 raw6243; decide +kernel
      have hl : raw6243step0Labels = raw6243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6243 raw6243Labels permutation346 hz
    mixedMoment B raw6243step0 raw6243step0Labels = mixedMoment B raw6243step1 raw6243step1Labels := by
      have ha : raw6243step1 = (fun i j => raw6243step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6243step1 raw6243step0; decide +kernel
      have hl : raw6243step1Labels = raw6243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6243step0 raw6243step0Labels permutation36 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw6244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6244Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw6244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw6244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6244 raw6244Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw6244 raw6244Labels = mixedMoment B raw6244step0 raw6244step0Labels := by
      have hz : ∀ j, raw6244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6244step0 = (fun i j => raw6244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6244step0 raw6244; decide +kernel
      have hl : raw6244step0Labels = raw6244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6244 raw6244Labels permutation346 hz
    mixedMoment B raw6244step0 raw6244step0Labels = mixedMoment B raw6244step1 raw6244step1Labels := by
      have ha : raw6244step1 = (fun i j => raw6244step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6244step1 raw6244step0; decide +kernel
      have hl : raw6244step1Labels = raw6244step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6244step0 raw6244step0Labels permutation39 permutation2
    _ = mixedMoment B node2620 node2620Labels := by rfl

def raw6245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6245Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw6245step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6245 raw6245Labels = mixedMoment B node2619 node2619Labels := by
  calc
    mixedMoment B raw6245 raw6245Labels = mixedMoment B raw6245step0 raw6245step0Labels := by
      have hz : ∀ j, raw6245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6245step0 = (fun i j => raw6245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6245step0 raw6245; decide +kernel
      have hl : raw6245step0Labels = raw6245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6245 raw6245Labels permutation346 hz
    mixedMoment B raw6245step0 raw6245step0Labels = mixedMoment B raw6245step1 raw6245step1Labels := by
      have ha : raw6245step1 = (fun i j => raw6245step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6245step1 raw6245step0; decide +kernel
      have hl : raw6245step1Labels = raw6245step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6245step0 raw6245step0Labels permutation38 permutation2
    _ = mixedMoment B node2619 node2619Labels := by rfl

def raw6246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6246Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw6246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6246 raw6246Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw6246 raw6246Labels = mixedMoment B raw6246step0 raw6246step0Labels := by
      have hz : ∀ j, raw6246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6246step0 = (fun i j => raw6246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6246step0 raw6246; decide +kernel
      have hl : raw6246step0Labels = raw6246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6246 raw6246Labels permutation346 hz
    mixedMoment B raw6246step0 raw6246step0Labels = mixedMoment B raw6246step1 raw6246step1Labels := by
      have ha : raw6246step1 = (fun i j => raw6246step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6246step1 raw6246step0; decide +kernel
      have hl : raw6246step1Labels = raw6246step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6246step0 raw6246step0Labels permutation33 permutation2
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw6247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6247Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw6247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6247 raw6247Labels = mixedMoment B node2716 node2716Labels := by
  calc
    mixedMoment B raw6247 raw6247Labels = mixedMoment B raw6247step0 raw6247step0Labels := by
      have hz : ∀ j, raw6247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6247step0 = (fun i j => raw6247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6247step0 raw6247; decide +kernel
      have hl : raw6247step0Labels = raw6247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6247 raw6247Labels permutation346 hz
    _ = mixedMoment B node2716 node2716Labels := by rfl

def raw6248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw6248step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6248 raw6248Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw6248 raw6248Labels = mixedMoment B raw6248step0 raw6248step0Labels := by
      have hz : ∀ j, raw6248 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6248step0 = (fun i j => raw6248 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6248step0 raw6248; decide +kernel
      have hl : raw6248step0Labels = raw6248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6248 raw6248Labels permutation346 hz
    mixedMoment B raw6248step0 raw6248step0Labels = mixedMoment B raw6248step1 raw6248step1Labels := by
      have ha : raw6248step1 = (fun i j => raw6248step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6248step1 raw6248step0; decide +kernel
      have hl : raw6248step1Labels = raw6248step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6248step0 raw6248step0Labels permutation151 permutation2
    mixedMoment B raw6248step1 raw6248step1Labels = mixedMoment B raw6248step2 raw6248step2Labels := by
      have ha : raw6248step2 = -raw6248step1 := by apply Matrix.ext; change ∀ i j, raw6248step2 i j = -(raw6248step1 i j); unfold raw6248step2 raw6248step1; decide +kernel
      have hl : raw6248step2Labels = raw6248step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw6249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6249step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6249 raw6249Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw6249 raw6249Labels = mixedMoment B raw6249step0 raw6249step0Labels := by
      have ha : raw6249step0 = (fun i j => raw6249 (permutation611 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6249step0 raw6249; decide +kernel
      have hl : raw6249step0Labels = raw6249Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6249 raw6249Labels permutation611 permutation7
    mixedMoment B raw6249step0 raw6249step0Labels = mixedMoment B raw6249step1 raw6249step1Labels := by
      have ha : raw6249step1 = raw6249step0 := by apply Matrix.ext; unfold raw6249step1 raw6249step0; decide +kernel
      have hl : raw6249step0Labels = labelEmbedding10 ∘ raw6249step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6249step0 raw6249step0Labels raw6249step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw6250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6250step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6250step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6250 raw6250Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw6250 raw6250Labels = mixedMoment B raw6250step0 raw6250step0Labels := by
      have hz : ∀ j, raw6250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6250step0 = (fun i j => raw6250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6250step0 raw6250; decide +kernel
      have hl : raw6250step0Labels = raw6250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6250 raw6250Labels permutation346 hz
    mixedMoment B raw6250step0 raw6250step0Labels = mixedMoment B raw6250step1 raw6250step1Labels := by
      have ha : raw6250step1 = (fun i j => raw6250step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6250step1 raw6250step0; decide +kernel
      have hl : raw6250step1Labels = raw6250step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6250step0 raw6250step0Labels permutation139 permutation7
    mixedMoment B raw6250step1 raw6250step1Labels = mixedMoment B raw6250step2 raw6250step2Labels := by
      have ha : raw6250step2 = raw6250step1 := by apply Matrix.ext; unfold raw6250step2 raw6250step1; decide +kernel
      have hl : raw6250step1Labels = labelEmbedding10 ∘ raw6250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6250step1 raw6250step1Labels raw6250step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw6251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6251step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6251 raw6251Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw6251 raw6251Labels = mixedMoment B raw6251step0 raw6251step0Labels := by
      have hz : ∀ j, raw6251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6251step0 = (fun i j => raw6251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6251step0 raw6251; decide +kernel
      have hl : raw6251step0Labels = raw6251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6251 raw6251Labels permutation346 hz
    mixedMoment B raw6251step0 raw6251step0Labels = mixedMoment B raw6251step1 raw6251step1Labels := by
      have ha : raw6251step1 = (fun i j => raw6251step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6251step1 raw6251step0; decide +kernel
      have hl : raw6251step1Labels = raw6251step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6251step0 raw6251step0Labels permutation137 permutation7
    mixedMoment B raw6251step1 raw6251step1Labels = mixedMoment B raw6251step2 raw6251step2Labels := by
      have ha : raw6251step2 = raw6251step1 := by apply Matrix.ext; unfold raw6251step2 raw6251step1; decide +kernel
      have hl : raw6251step1Labels = labelEmbedding10 ∘ raw6251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6251step1 raw6251step1Labels raw6251step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw6252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6252step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6252 raw6252Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw6252 raw6252Labels = mixedMoment B raw6252step0 raw6252step0Labels := by
      have hz : ∀ j, raw6252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6252step0 = (fun i j => raw6252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6252step0 raw6252; decide +kernel
      have hl : raw6252step0Labels = raw6252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6252 raw6252Labels permutation346 hz
    mixedMoment B raw6252step0 raw6252step0Labels = mixedMoment B raw6252step1 raw6252step1Labels := by
      have ha : raw6252step1 = (fun i j => raw6252step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6252step1 raw6252step0; decide +kernel
      have hl : raw6252step1Labels = raw6252step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6252step0 raw6252step0Labels permutation116 permutation4
    mixedMoment B raw6252step1 raw6252step1Labels = mixedMoment B raw6252step2 raw6252step2Labels := by
      have ha : raw6252step2 = raw6252step1 := by apply Matrix.ext; unfold raw6252step2 raw6252step1; decide +kernel
      have hl : raw6252step1Labels = labelEmbedding7 ∘ raw6252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6252step1 raw6252step1Labels raw6252step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw6253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6253step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6253 raw6253Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw6253 raw6253Labels = mixedMoment B raw6253step0 raw6253step0Labels := by
      have hz : ∀ j, raw6253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6253step0 = (fun i j => raw6253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6253step0 raw6253; decide +kernel
      have hl : raw6253step0Labels = raw6253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6253 raw6253Labels permutation346 hz
    mixedMoment B raw6253step0 raw6253step0Labels = mixedMoment B raw6253step1 raw6253step1Labels := by
      have ha : raw6253step1 = (fun i j => raw6253step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6253step1 raw6253step0; decide +kernel
      have hl : raw6253step1Labels = raw6253step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6253step0 raw6253step0Labels permutation38 permutation3
    mixedMoment B raw6253step1 raw6253step1Labels = mixedMoment B raw6253step2 raw6253step2Labels := by
      have ha : raw6253step2 = raw6253step1 := by apply Matrix.ext; unfold raw6253step2 raw6253step1; decide +kernel
      have hl : raw6253step1Labels = labelEmbedding6 ∘ raw6253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6253step1 raw6253step1Labels raw6253step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw6254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6254step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6254 raw6254Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw6254 raw6254Labels = mixedMoment B raw6254step0 raw6254step0Labels := by
      have ha : raw6254step0 = (fun i j => raw6254 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6254step0 raw6254; decide +kernel
      have hl : raw6254step0Labels = raw6254Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6254 raw6254Labels permutation182 permutation3
    mixedMoment B raw6254step0 raw6254step0Labels = mixedMoment B raw6254step1 raw6254step1Labels := by
      have ha : raw6254step1 = raw6254step0 := by apply Matrix.ext; unfold raw6254step1 raw6254step0; decide +kernel
      have hl : raw6254step0Labels = labelEmbedding6 ∘ raw6254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6254step0 raw6254step0Labels raw6254step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw6255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6255step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6255step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6255 raw6255Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw6255 raw6255Labels = mixedMoment B raw6255step0 raw6255step0Labels := by
      have hz : ∀ j, raw6255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6255step0 = (fun i j => raw6255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6255step0 raw6255; decide +kernel
      have hl : raw6255step0Labels = raw6255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6255 raw6255Labels permutation346 hz
    mixedMoment B raw6255step0 raw6255step0Labels = mixedMoment B raw6255step1 raw6255step1Labels := by
      have ha : raw6255step1 = (fun i j => raw6255step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6255step1 raw6255step0; decide +kernel
      have hl : raw6255step1Labels = raw6255step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6255step0 raw6255step0Labels permutation38 permutation3
    mixedMoment B raw6255step1 raw6255step1Labels = mixedMoment B raw6255step2 raw6255step2Labels := by
      have ha : raw6255step2 = raw6255step1 := by apply Matrix.ext; unfold raw6255step2 raw6255step1; decide +kernel
      have hl : raw6255step1Labels = labelEmbedding6 ∘ raw6255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6255step1 raw6255step1Labels raw6255step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw6256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw6256step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw6256step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6256 raw6256Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw6256 raw6256Labels = mixedMoment B raw6256step0 raw6256step0Labels := by
      have hz : ∀ j, raw6256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6256step0 = (fun i j => raw6256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6256step0 raw6256; decide +kernel
      have hl : raw6256step0Labels = raw6256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6256 raw6256Labels permutation346 hz
    mixedMoment B raw6256step0 raw6256step0Labels = mixedMoment B raw6256step1 raw6256step1Labels := by
      have ha : raw6256step1 = (fun i j => raw6256step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6256step1 raw6256step0; decide +kernel
      have hl : raw6256step1Labels = raw6256step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6256step0 raw6256step0Labels permutation40 permutation3
    mixedMoment B raw6256step1 raw6256step1Labels = mixedMoment B raw6256step2 raw6256step2Labels := by
      have ha : raw6256step2 = raw6256step1 := by apply Matrix.ext; unfold raw6256step2 raw6256step1; decide +kernel
      have hl : raw6256step1Labels = labelEmbedding6 ∘ raw6256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6256step1 raw6256step1Labels raw6256step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw6257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6257step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6257 raw6257Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw6257 raw6257Labels = mixedMoment B raw6257step0 raw6257step0Labels := by
      have hz : ∀ j, raw6257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6257step0 = (fun i j => raw6257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6257step0 raw6257; decide +kernel
      have hl : raw6257step0Labels = raw6257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6257 raw6257Labels permutation346 hz
    mixedMoment B raw6257step0 raw6257step0Labels = mixedMoment B raw6257step1 raw6257step1Labels := by
      have ha : raw6257step1 = (fun i j => raw6257step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6257step1 raw6257step0; decide +kernel
      have hl : raw6257step1Labels = raw6257step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6257step0 raw6257step0Labels permutation42 permutation3
    mixedMoment B raw6257step1 raw6257step1Labels = mixedMoment B raw6257step2 raw6257step2Labels := by
      have ha : raw6257step2 = raw6257step1 := by apply Matrix.ext; unfold raw6257step2 raw6257step1; decide +kernel
      have hl : raw6257step1Labels = labelEmbedding6 ∘ raw6257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6257step1 raw6257step1Labels raw6257step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw6258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6258step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6258 raw6258Labels = mixedMoment B node4400 node4400Labels := by
  calc
    mixedMoment B raw6258 raw6258Labels = mixedMoment B raw6258step0 raw6258step0Labels := by
      have ha : raw6258step0 = (fun i j => raw6258 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6258step0 raw6258; decide +kernel
      have hl : raw6258step0Labels = raw6258Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6258 raw6258Labels permutation158 permutation3
    mixedMoment B raw6258step0 raw6258step0Labels = mixedMoment B raw6258step1 raw6258step1Labels := by
      have ha : raw6258step1 = raw6258step0 := by apply Matrix.ext; unfold raw6258step1 raw6258step0; decide +kernel
      have hl : raw6258step0Labels = labelEmbedding6 ∘ raw6258step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6258step0 raw6258step0Labels raw6258step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4400 node4400Labels := by rfl

def raw6259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6259step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6259 raw6259Labels = mixedMoment B node4999 node4999Labels := by
  calc
    mixedMoment B raw6259 raw6259Labels = mixedMoment B raw6259step0 raw6259step0Labels := by
      have ha : raw6259step0 = (fun i j => raw6259 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6259step0 raw6259; decide +kernel
      have hl : raw6259step0Labels = raw6259Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6259 raw6259Labels permutation158 permutation3
    mixedMoment B raw6259step0 raw6259step0Labels = mixedMoment B raw6259step1 raw6259step1Labels := by
      have ha : raw6259step1 = raw6259step0 := by apply Matrix.ext; unfold raw6259step1 raw6259step0; decide +kernel
      have hl : raw6259step0Labels = labelEmbedding6 ∘ raw6259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6259step0 raw6259step0Labels raw6259step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4999 node4999Labels := by rfl

def raw6260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6260step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6260 raw6260Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw6260 raw6260Labels = mixedMoment B raw6260step0 raw6260step0Labels := by
      have ha : raw6260step0 = (fun i j => raw6260 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6260step0 raw6260; decide +kernel
      have hl : raw6260step0Labels = raw6260Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6260 raw6260Labels permutation200 permutation3
    mixedMoment B raw6260step0 raw6260step0Labels = mixedMoment B raw6260step1 raw6260step1Labels := by
      have ha : raw6260step1 = raw6260step0 := by apply Matrix.ext; unfold raw6260step1 raw6260step0; decide +kernel
      have hl : raw6260step0Labels = labelEmbedding6 ∘ raw6260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6260step0 raw6260step0Labels raw6260step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw6261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6261step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6261 raw6261Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw6261 raw6261Labels = mixedMoment B raw6261step0 raw6261step0Labels := by
      have ha : raw6261step0 = (fun i j => raw6261 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6261step0 raw6261; decide +kernel
      have hl : raw6261step0Labels = raw6261Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6261 raw6261Labels permutation160 permutation3
    mixedMoment B raw6261step0 raw6261step0Labels = mixedMoment B raw6261step1 raw6261step1Labels := by
      have ha : raw6261step1 = raw6261step0 := by apply Matrix.ext; unfold raw6261step1 raw6261step0; decide +kernel
      have hl : raw6261step0Labels = labelEmbedding6 ∘ raw6261step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6261step0 raw6261step0Labels raw6261step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw6262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6262step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6262 raw6262Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw6262 raw6262Labels = mixedMoment B raw6262step0 raw6262step0Labels := by
      have ha : raw6262step0 = (fun i j => raw6262 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6262step0 raw6262; decide +kernel
      have hl : raw6262step0Labels = raw6262Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6262 raw6262Labels permutation162 permutation3
    mixedMoment B raw6262step0 raw6262step0Labels = mixedMoment B raw6262step1 raw6262step1Labels := by
      have ha : raw6262step1 = raw6262step0 := by apply Matrix.ext; unfold raw6262step1 raw6262step0; decide +kernel
      have hl : raw6262step0Labels = labelEmbedding6 ∘ raw6262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6262step0 raw6262step0Labels raw6262step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw6263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6263step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6263 raw6263Labels = mixedMoment B node4427 node4427Labels := by
  calc
    mixedMoment B raw6263 raw6263Labels = mixedMoment B raw6263step0 raw6263step0Labels := by
      have hz : ∀ j, raw6263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6263step0 = (fun i j => raw6263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6263step0 raw6263; decide +kernel
      have hl : raw6263step0Labels = raw6263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6263 raw6263Labels permutation346 hz
    mixedMoment B raw6263step0 raw6263step0Labels = mixedMoment B raw6263step1 raw6263step1Labels := by
      have ha : raw6263step1 = (fun i j => raw6263step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6263step1 raw6263step0; decide +kernel
      have hl : raw6263step1Labels = raw6263step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6263step0 raw6263step0Labels permutation32 permutation3
    mixedMoment B raw6263step1 raw6263step1Labels = mixedMoment B raw6263step2 raw6263step2Labels := by
      have ha : raw6263step2 = raw6263step1 := by apply Matrix.ext; unfold raw6263step2 raw6263step1; decide +kernel
      have hl : raw6263step1Labels = labelEmbedding6 ∘ raw6263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6263step1 raw6263step1Labels raw6263step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4427 node4427Labels := by rfl

def raw6264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6264step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6264 raw6264Labels = mixedMoment B node5020 node5020Labels := by
  calc
    mixedMoment B raw6264 raw6264Labels = mixedMoment B raw6264step0 raw6264step0Labels := by
      have hz : ∀ j, raw6264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6264step0 = (fun i j => raw6264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6264step0 raw6264; decide +kernel
      have hl : raw6264step0Labels = raw6264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6264 raw6264Labels permutation346 hz
    mixedMoment B raw6264step0 raw6264step0Labels = mixedMoment B raw6264step1 raw6264step1Labels := by
      have ha : raw6264step1 = (fun i j => raw6264step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6264step1 raw6264step0; decide +kernel
      have hl : raw6264step1Labels = raw6264step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6264step0 raw6264step0Labels permutation32 permutation3
    mixedMoment B raw6264step1 raw6264step1Labels = mixedMoment B raw6264step2 raw6264step2Labels := by
      have ha : raw6264step2 = raw6264step1 := by apply Matrix.ext; unfold raw6264step2 raw6264step1; decide +kernel
      have hl : raw6264step1Labels = labelEmbedding6 ∘ raw6264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6264step1 raw6264step1Labels raw6264step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5020 node5020Labels := by rfl

def raw6265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6265step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6265 raw6265Labels = mixedMoment B node5061 node5061Labels := by
  calc
    mixedMoment B raw6265 raw6265Labels = mixedMoment B raw6265step0 raw6265step0Labels := by
      have ha : raw6265step0 = (fun i j => raw6265 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6265step0 raw6265; decide +kernel
      have hl : raw6265step0Labels = raw6265Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6265 raw6265Labels permutation176 permutation3
    mixedMoment B raw6265step0 raw6265step0Labels = mixedMoment B raw6265step1 raw6265step1Labels := by
      have ha : raw6265step1 = raw6265step0 := by apply Matrix.ext; unfold raw6265step1 raw6265step0; decide +kernel
      have hl : raw6265step0Labels = labelEmbedding6 ∘ raw6265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6265step0 raw6265step0Labels raw6265step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5061 node5061Labels := by rfl

def raw6266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6266step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6266 raw6266Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw6266 raw6266Labels = mixedMoment B raw6266step0 raw6266step0Labels := by
      have hz : ∀ j, raw6266 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6266step0 = (fun i j => raw6266 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6266step0 raw6266; decide +kernel
      have hl : raw6266step0Labels = raw6266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6266 raw6266Labels permutation346 hz
    mixedMoment B raw6266step0 raw6266step0Labels = mixedMoment B raw6266step1 raw6266step1Labels := by
      have ha : raw6266step1 = (fun i j => raw6266step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6266step1 raw6266step0; decide +kernel
      have hl : raw6266step1Labels = raw6266step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6266step0 raw6266step0Labels permutation34 permutation3
    mixedMoment B raw6266step1 raw6266step1Labels = mixedMoment B raw6266step2 raw6266step2Labels := by
      have ha : raw6266step2 = raw6266step1 := by apply Matrix.ext; unfold raw6266step2 raw6266step1; decide +kernel
      have hl : raw6266step1Labels = labelEmbedding6 ∘ raw6266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6266step1 raw6266step1Labels raw6266step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw6267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw6267step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw6267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6267 raw6267Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw6267 raw6267Labels = mixedMoment B raw6267step0 raw6267step0Labels := by
      have hz : ∀ j, raw6267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6267step0 = (fun i j => raw6267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6267step0 raw6267; decide +kernel
      have hl : raw6267step0Labels = raw6267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6267 raw6267Labels permutation346 hz
    mixedMoment B raw6267step0 raw6267step0Labels = mixedMoment B raw6267step1 raw6267step1Labels := by
      have ha : raw6267step1 = (fun i j => raw6267step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6267step1 raw6267step0; decide +kernel
      have hl : raw6267step1Labels = raw6267step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6267step0 raw6267step0Labels permutation36 permutation3
    mixedMoment B raw6267step1 raw6267step1Labels = mixedMoment B raw6267step2 raw6267step2Labels := by
      have ha : raw6267step2 = raw6267step1 := by apply Matrix.ext; unfold raw6267step2 raw6267step1; decide +kernel
      have hl : raw6267step1Labels = labelEmbedding6 ∘ raw6267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6267step1 raw6267step1Labels raw6267step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw6268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6268step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6268step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6268 raw6268Labels = mixedMoment B node4403 node4403Labels := by
  calc
    mixedMoment B raw6268 raw6268Labels = mixedMoment B raw6268step0 raw6268step0Labels := by
      have hz : ∀ j, raw6268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6268step0 = (fun i j => raw6268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6268step0 raw6268; decide +kernel
      have hl : raw6268step0Labels = raw6268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6268 raw6268Labels permutation346 hz
    mixedMoment B raw6268step0 raw6268step0Labels = mixedMoment B raw6268step1 raw6268step1Labels := by
      have ha : raw6268step1 = (fun i j => raw6268step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6268step1 raw6268step0; decide +kernel
      have hl : raw6268step1Labels = raw6268step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6268step0 raw6268step0Labels permutation33 permutation3
    mixedMoment B raw6268step1 raw6268step1Labels = mixedMoment B raw6268step2 raw6268step2Labels := by
      have ha : raw6268step2 = raw6268step1 := by apply Matrix.ext; unfold raw6268step2 raw6268step1; decide +kernel
      have hl : raw6268step1Labels = labelEmbedding6 ∘ raw6268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6268step1 raw6268step1Labels raw6268step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4403 node4403Labels := by rfl

def raw6269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6269step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6269 raw6269Labels = mixedMoment B node5002 node5002Labels := by
  calc
    mixedMoment B raw6269 raw6269Labels = mixedMoment B raw6269step0 raw6269step0Labels := by
      have hz : ∀ j, raw6269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6269step0 = (fun i j => raw6269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6269step0 raw6269; decide +kernel
      have hl : raw6269step0Labels = raw6269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6269 raw6269Labels permutation346 hz
    mixedMoment B raw6269step0 raw6269step0Labels = mixedMoment B raw6269step1 raw6269step1Labels := by
      have ha : raw6269step1 = (fun i j => raw6269step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6269step1 raw6269step0; decide +kernel
      have hl : raw6269step1Labels = raw6269step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6269step0 raw6269step0Labels permutation33 permutation3
    mixedMoment B raw6269step1 raw6269step1Labels = mixedMoment B raw6269step2 raw6269step2Labels := by
      have ha : raw6269step2 = raw6269step1 := by apply Matrix.ext; unfold raw6269step2 raw6269step1; decide +kernel
      have hl : raw6269step1Labels = labelEmbedding6 ∘ raw6269step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6269step1 raw6269step1Labels raw6269step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5002 node5002Labels := by rfl

def raw6270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6270step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6270 raw6270Labels = mixedMoment B node5049 node5049Labels := by
  calc
    mixedMoment B raw6270 raw6270Labels = mixedMoment B raw6270step0 raw6270step0Labels := by
      have ha : raw6270step0 = (fun i j => raw6270 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6270step0 raw6270; decide +kernel
      have hl : raw6270step0Labels = raw6270Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6270 raw6270Labels permutation177 permutation3
    mixedMoment B raw6270step0 raw6270step0Labels = mixedMoment B raw6270step1 raw6270step1Labels := by
      have ha : raw6270step1 = raw6270step0 := by apply Matrix.ext; unfold raw6270step1 raw6270step0; decide +kernel
      have hl : raw6270step0Labels = labelEmbedding6 ∘ raw6270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6270step0 raw6270step0Labels raw6270step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5049 node5049Labels := by rfl

def raw6271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw6271step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw6271step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6271 raw6271Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw6271 raw6271Labels = mixedMoment B raw6271step0 raw6271step0Labels := by
      have hz : ∀ j, raw6271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6271step0 = (fun i j => raw6271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6271step0 raw6271; decide +kernel
      have hl : raw6271step0Labels = raw6271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6271 raw6271Labels permutation346 hz
    mixedMoment B raw6271step0 raw6271step0Labels = mixedMoment B raw6271step1 raw6271step1Labels := by
      have ha : raw6271step1 = (fun i j => raw6271step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6271step1 raw6271step0; decide +kernel
      have hl : raw6271step1Labels = raw6271step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6271step0 raw6271step0Labels permutation39 permutation3
    mixedMoment B raw6271step1 raw6271step1Labels = mixedMoment B raw6271step2 raw6271step2Labels := by
      have ha : raw6271step2 = raw6271step1 := by apply Matrix.ext; unfold raw6271step2 raw6271step1; decide +kernel
      have hl : raw6271step1Labels = labelEmbedding6 ∘ raw6271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6271step1 raw6271step1Labels raw6271step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
